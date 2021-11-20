pub mod error_reporting;
pub mod pipelines;
pub mod substitution;

use hir::symbol_table::FrozenSymtab;
use hir::{ItemList, Pattern, TypeList};
use mir::types::Type as MirType;
use mir::ValueName;
pub use pipelines::generate_pipeline;
use spade_common::id_tracker::ExprIdTracker;
use substitution::Substitutions;

use parse_tree_macros::local_impl;
use spade_common::{location_info::Loc, name::NameID};
use spade_hir as hir;
use spade_hir::{
    expression::BinaryOperator, symbol_table::SymbolTable, Entity, ExprKind, Expression, Statement,
};
use spade_mir as mir;
use spade_typeinference::{
    equation::{TypeVar, TypedExpression},
    TypeState,
};
use spade_types::{ConcreteType, PrimitiveType};

pub enum Error {
    UsingGenericType { expr: Loc<Expression>, t: TypeVar },
}
pub type Result<T> = std::result::Result<T, Error>;

pub trait Manglable {
    fn mangled(&self) -> String;
}
impl Manglable for NameID {
    fn mangled(&self) -> String {
        let str_name = self.1.as_strs().join("_");
        format!("_m{}_{}", self.0, str_name)
    }
}

#[local_impl]
impl TypeStateLocal for TypeState {
    /// Returns the type of the expression as a concrete type. If the type is not
    /// fully ungenerified, returns an error
    fn expr_type(
        &self,
        expr: &Loc<Expression>,
        symtab: &SymbolTable,
        types: &TypeList,
    ) -> Result<ConcreteType> {
        let t = self
            .type_of(&TypedExpression::Id(expr.id))
            .expect("Expression had no specified type");

        if let Some(t) = Self::ungenerify_type(&t, symtab, types) {
            Ok(t)
        } else {
            Err(Error::UsingGenericType {
                expr: expr.clone(),
                t: t.clone(),
            })
        }
    }
}

#[local_impl]
impl ConcreteTypeLocal for ConcreteType {
    fn to_mir_type(&self) -> mir::types::Type {
        use mir::types::Type;
        use ConcreteType as CType;

        match self {
            CType::Tuple(inner) => {
                Type::Tuple(inner.iter().map(ConcreteTypeLocal::to_mir_type).collect())
            }
            CType::Single {
                base: PrimitiveType::Bool,
                params: _,
            } => Type::Bool,
            CType::Single {
                base: PrimitiveType::Clock,
                params: _,
            } => Type::Bool,
            CType::Single {
                base: PrimitiveType::Int,
                params,
            } => match params.as_slice() {
                [CType::Integer(val)] => Type::Int(*val as u64),
                t => unreachable!("{:?} is an invalid generic parameter for an integer", t),
            },
            CType::Single {
                base: PrimitiveType::Uint,
                params,
            } => match params.as_slice() {
                [CType::Integer(val)] => Type::Int(*val as u64),
                t => unreachable!("{:?} is an invalid generic parameter for an integer", t),
            },
            CType::Integer(_) => {
                unreachable!("Found an integer at the base level of a type")
            }
            CType::Enum { options } => {
                let inner = options
                    .iter()
                    .map(|o| o.1.iter().map(|t| t.to_mir_type()).collect())
                    .collect();
                Type::Enum(inner)
            }
        }
    }
}

#[local_impl]
impl NameIDLocal for NameID {
    fn value_name(&self) -> mir::ValueName {
        let mangled = format!("{}", self.1.as_strs().join("_"));
        mir::ValueName::Named(self.0, mangled)
    }
}

struct PatternCondition {
    pub statements: Vec<mir::Statement>,
    pub result_name: ValueName,
}

#[local_impl]
impl PatternLocal for Pattern {
    /// Lower a pattern to its individual parts. Requires the `Pattern::id` to be
    /// present in the code before this
    /// self_name is the name of the operand which this pattern matches
    fn lower(
        &self,
        self_name: ValueName,
        symtab: &SymbolTable,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &hir::ItemList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = vec![];
        match &self.kind {
            hir::PatternKind::Integer(_) => todo!(),
            hir::PatternKind::Bool(_) => {},
            hir::PatternKind::Name { .. } => {}
            hir::PatternKind::Tuple(inner) => {
                let inner_types = if let mir::types::Type::Tuple(inner) = &types
                    .type_of_id(self.id, symtab, &item_list.types)
                    .to_mir_type()
                {
                    inner.clone()
                } else {
                    unreachable!("Tuple destructuring of non-tuple");
                };

                for (i, p) in inner.iter().enumerate() {
                    result.push(mir::Statement::Binding(mir::Binding {
                        name: p.value_name(),
                        operator: mir::Operator::IndexTuple(i as u64, inner_types.clone()),
                        operands: vec![self_name.clone()],
                        ty: types
                            .type_of_id(p.id, symtab, &item_list.types)
                            .to_mir_type(),
                    }));

                    result.append(&mut p.lower(p.value_name(), symtab, types, subs, item_list)?)
                }
            }
            hir::PatternKind::Type(path, args) => {
                let enum_variant = symtab.enum_variant_by_id(path);
                let self_type = types
                    .type_of_id(self.id, symtab, &item_list.types)
                    .to_mir_type();

                for (i, p) in args.iter().enumerate() {
                    result.push(mir::Statement::Binding(mir::Binding {
                        name: p.value.value_name(),
                        operator: mir::Operator::EnumMember {
                            variant: enum_variant.option,
                            member_index: i,
                            enum_type: self_type.clone(),
                        },
                        operands: vec![self_name.clone()],
                        ty: types
                            .type_of_id(p.value.id, symtab, &item_list.types)
                            .to_mir_type(),
                    }));

                    result.append(&mut p.value.lower(
                        p.value.value_name(),
                        symtab,
                        types,
                        subs,
                        item_list,
                    )?)
                }
            }
        }

        Ok(result)
    }

    /// Returns MIR code for a condition that must hold for `expr` to satisfy
    /// this pattern.
    fn condition(
        &self,
        expr: &Loc<Expression>,
        symtab: &FrozenSymtab,
        idtracker: &mut ExprIdTracker,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &hir::ItemList,
    ) -> Result<PatternCondition> {
        let output_id = idtracker.next();
        let result_name = ValueName::Expr(output_id);
        match &self.kind {
            hir::PatternKind::Integer(_) => todo!("Codegen for integer patterns"),
            hir::PatternKind::Bool(true) => {
                Ok(PatternCondition{statements: vec![], result_name: expr.variable(subs)})
            },
            hir::PatternKind::Bool(false) => {
                let statements = vec![
                    mir::Statement::Binding(mir::Binding{
                        name: result_name.clone(),
                        ty: MirType::Bool,
                        operator: mir::Operator::LogicalNot,
                        operands: vec![expr.variable(subs)]
                    })
                ];

                Ok(PatternCondition{statements, result_name})
            }
            hir::PatternKind::Name { .. } => Ok(PatternCondition {
                statements: vec![mir::Statement::Constant(
                    output_id,
                    MirType::Bool,
                    mir::ConstantValue::Bool(true),
                )],
                result_name,
            }),
            hir::PatternKind::Tuple(_) => todo!("Codegen for tuple patterns"),
            hir::PatternKind::Type(path, _args) => {
                let enum_variant = symtab.symtab().enum_variant_by_id(&path);

                let self_type = types
                    .type_of_id(self.id, symtab.symtab(), &item_list.types)
                    .to_mir_type();

                let statement = mir::Statement::Binding(mir::Binding {
                    name: result_name.clone(),
                    operator: mir::Operator::IsEnumVariant {
                        variant: enum_variant.option,
                        enum_type: self_type,
                    },
                    operands: vec![expr.variable(subs)],
                    ty: MirType::Bool,
                });

                Ok(PatternCondition {
                    statements: vec![statement],
                    result_name,
                })
            }
        }
    }

    /// Get the name which the whole pattern should be bound. In practice,
    /// this will be the pattern ID unless the pattern is just a name, in
    /// which case it will be a name
    ///
    /// This is done to avoid creating too many unnessecary ExprID variables
    /// in the output code to make it more readable
    fn value_name(&self) -> ValueName {
        match &self.kind {
            hir::PatternKind::Name {
                name,
                pre_declared: _,
            } => return name.value_name(),
            hir::PatternKind::Integer(_) => {}
            hir::PatternKind::Bool(_) => {}
            hir::PatternKind::Tuple(_) => {}
            hir::PatternKind::Type(_, _) => {}
        }
        ValueName::Expr(self.id)
    }

    /// Return true if this pattern is just an alias for another name. If this is not
    /// the case, an alias from its true name to `value_name` must be generated
    fn is_alias(&self) -> bool {
        match self.kind {
            hir::PatternKind::Name { .. } => true,
            hir::PatternKind::Integer(_) => false,
            hir::PatternKind::Bool(_) => false,
            hir::PatternKind::Tuple(_) => false,
            hir::PatternKind::Type(_, _) => false,
        }
    }
}

#[local_impl]
impl StatementLocal for Statement {
    fn lower(
        &self,
        symtab: &FrozenSymtab,
        idtracker: &mut ExprIdTracker,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &hir::ItemList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = vec![];
        match &self {
            Statement::Binding(pattern, _t, value) => {
                result.append(&mut value.lower(symtab, idtracker, types, subs, item_list)?);

                result.push(mir::Statement::Binding(mir::Binding {
                    name: pattern.value_name(),
                    operator: mir::Operator::Alias,
                    operands: vec![value.variable(subs)],
                    ty: types
                        .type_of_id(pattern.id, symtab.symtab(), &item_list.types)
                        .to_mir_type(),
                }));
                result.append(&mut pattern.lower(
                    value.variable(subs),
                    symtab.symtab(),
                    types,
                    subs,
                    item_list,
                )?);
            }
            Statement::Register(register) => {
                result.append(
                    &mut register
                        .clock
                        .lower(symtab, idtracker, types, subs, item_list)?,
                );

                if let Some((trig, value)) = &register.reset {
                    result.append(&mut trig.lower(symtab, idtracker, types, subs, item_list)?);
                    result.append(&mut value.lower(symtab, idtracker, types, subs, item_list)?);
                }

                result.append(
                    &mut register
                        .value
                        .lower(symtab, idtracker, types, subs, item_list)?,
                );

                result.push(mir::Statement::Register(mir::Register {
                    name: register.pattern.value_name(),
                    ty: types
                        .type_of_id(register.pattern.id, symtab.symtab(), &item_list.types)
                        .to_mir_type(),
                    clock: register.clock.variable(subs),
                    reset: register
                        .reset
                        .as_ref()
                        .map(|(value, trig)| (value.variable(subs), trig.variable(subs))),
                    value: register.value.variable(subs),
                }));

                result.append(&mut register.pattern.lower(
                    register.pattern.value_name(),
                    symtab.symtab(),
                    types,
                    subs,
                    item_list,
                )?);
            }
            Statement::Declaration(_) => {}
        }
        Ok(result)
    }
}

#[local_impl]
impl ExprLocal for Loc<Expression> {
    /// If the verilog code for this expression is just an alias for another variable
    /// that is returned here. This allows us to skip generating wires that we don't
    /// really need
    fn alias(&self, subs: &Substitutions) -> Option<mir::ValueName> {
        match &self.kind {
            ExprKind::Identifier(ident) => Some(subs.lookup(&ident).value_name()),
            ExprKind::IntLiteral(_) => None,
            ExprKind::BoolLiteral(_) => None,
            ExprKind::FnCall(_, _) => None,
            ExprKind::TupleLiteral(_) => None,
            ExprKind::TupleIndex(_, _) => None,
            ExprKind::Block(block) => Some(block.result.variable(subs)),
            ExprKind::If(_, _, _) => None,
            ExprKind::Match(_, _) => None,
            ExprKind::BinaryOperator(_, _, _) => None,
            ExprKind::EntityInstance(_, _) => None,
            ExprKind::PipelineInstance { .. } => None,
        }
    }

    // NOTE: this impl and a few others could be moved to a impl block that does not have
    // the Loc requirement if desired
    fn variable(&self, subs: &Substitutions) -> mir::ValueName {
        // If this expressions should not use the standard __expr__{} variable,
        // that is specified here

        self.alias(subs)
            .unwrap_or_else(|| mir::ValueName::Expr(self.id))
    }

    fn lower(
        &self,
        symtab: &FrozenSymtab,
        idtracker: &mut ExprIdTracker,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = vec![];

        let self_type = types
            .expr_type(self, symtab.symtab(), &item_list.types)?
            .to_mir_type();

        match &self.kind {
            ExprKind::Identifier(_) => {
                // Empty. The identifier will be defined elsewhere
            }
            ExprKind::IntLiteral(value) => {
                let ty = self_type;
                result.push(mir::Statement::Constant(
                    self.id,
                    ty,
                    mir::ConstantValue::Int(*value as u64),
                ));
            }
            ExprKind::BoolLiteral(value) => {
                let ty = self_type;
                result.push(mir::Statement::Constant(
                    self.id,
                    ty,
                    mir::ConstantValue::Bool(*value),
                ));
            }
            ExprKind::BinaryOperator(lhs, op, rhs) => {
                let binop_builder = |op| {
                    result.append(&mut lhs.lower(symtab, idtracker, types, subs, &item_list)?);
                    result.append(&mut rhs.lower(symtab, idtracker, types, subs, &item_list)?);

                    result.push(mir::Statement::Binding(mir::Binding {
                        name: self.variable(subs),
                        operator: op,
                        operands: vec![lhs.variable(subs), rhs.variable(subs)],
                        ty: self_type,
                    }));
                    Ok(())
                };
                use mir::Operator::*;
                match op {
                    BinaryOperator::Add => binop_builder(Add)?,
                    BinaryOperator::Sub => binop_builder(Sub)?,
                    BinaryOperator::Mul => binop_builder(Mul)?,
                    BinaryOperator::Eq => binop_builder(Eq)?,
                    BinaryOperator::Gt => binop_builder(Gt)?,
                    BinaryOperator::Lt => binop_builder(Lt)?,
                    BinaryOperator::LeftShift => binop_builder(LeftShift)?,
                    BinaryOperator::RightShift => binop_builder(RightShift)?,
                    BinaryOperator::LogicalAnd => binop_builder(LogicalAnd)?,
                    BinaryOperator::LogicalOr => binop_builder(LogicalOr)?,
                    BinaryOperator::BitwiseAnd => binop_builder(BitwiseAnd)?,
                    BinaryOperator::BitwiseOr => binop_builder(BitwiseOr)?,
                };
            }
            ExprKind::TupleLiteral(elems) => {
                for elem in elems {
                    result.append(&mut elem.lower(symtab, idtracker, types, subs, &item_list)?)
                }

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::ConstructTuple,
                    operands: elems.iter().map(|e| e.variable(subs)).collect(),
                    ty: self_type,
                }))
            }
            ExprKind::TupleIndex(tup, idx) => {
                result.append(&mut tup.lower(symtab, idtracker, types, subs, &item_list)?);

                let types = if let mir::types::Type::Tuple(inner) = &types
                    .expr_type(tup, symtab.symtab(), &item_list.types)?
                    .to_mir_type()
                {
                    inner.clone()
                } else {
                    unreachable!("Tupel indexing of non-tuple: {:?}", self_type);
                };

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::IndexTuple(idx.inner as u64, types),
                    operands: vec![tup.variable(subs)],
                    ty: self_type,
                }))
            }
            ExprKind::Block(block) => {
                for statement in &block.statements {
                    result.append(&mut statement.lower(symtab, idtracker, types, subs, item_list)?);
                }
                result.append(
                    &mut block
                        .result
                        .lower(symtab, idtracker, types, subs, item_list)?,
                );

                // Empty. The block result will always be the last expression
            }
            ExprKind::If(cond, on_true, on_false) => {
                result.append(&mut cond.lower(symtab, idtracker, types, subs, item_list)?);
                result.append(&mut on_true.lower(symtab, idtracker, types, subs, item_list)?);
                result.append(&mut on_false.lower(symtab, idtracker, types, subs, item_list)?);

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::Select,
                    operands: vec![
                        cond.variable(subs),
                        on_true.variable(subs),
                        on_false.variable(subs),
                    ],
                    ty: types
                        .expr_type(self, symtab.symtab(), &item_list.types)?
                        .to_mir_type(),
                }));
            }
            ExprKind::Match(operand, branches) => {
                result.append(&mut operand.lower(symtab, idtracker, types, subs, item_list)?);
                let mut operands = vec![];
                for (pat, result_expr) in branches {
                    let mut cond =
                        pat.condition(operand, symtab, idtracker, types, subs, item_list)?;
                    result.append(&mut cond.statements);
                    result
                        .append(&mut result_expr.lower(symtab, idtracker, types, subs, item_list)?);
                    result.append(&mut pat.lower(
                        operand.variable(subs),
                        symtab.symtab(),
                        types,
                        subs,
                        item_list,
                    )?);

                    operands.push(cond.result_name);
                    operands.push(result_expr.variable(subs));
                }

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::Match,
                    operands,
                    ty: types
                        .expr_type(self, symtab.symtab(), &item_list.types)?
                        .to_mir_type(),
                }))
            }
            ExprKind::FnCall(name, params) => {
                for param in params {
                    result.append(
                        &mut param
                            .value
                            .lower(symtab, idtracker, types, subs, item_list)?,
                    );
                }
                // Look up the name in the executable list to see if this is a type instantiation
                match item_list.executables.get(name) {
                    Some(hir::ExecutableItem::EnumInstance { base_enum, variant }) => {
                        let variant_count = match item_list.types.get(base_enum) {
                            Some(type_decl) => match &type_decl.kind {
                                hir::TypeDeclKind::Enum(e) => e.inner.options.len(),
                                _ => panic!("Instantiating enum of type which is not an enum"),
                            },
                            None => panic!("No type declaration found for {}", base_enum),
                        };

                        result.push(mir::Statement::Binding(mir::Binding {
                            name: self.variable(subs),
                            ty: types
                                .expr_type(self, symtab.symtab(), &item_list.types)?
                                .to_mir_type(),
                            operator: mir::Operator::ConstructEnum {
                                variant: *variant,
                                variant_count,
                            },
                            operands: params
                                .into_iter()
                                .map(|arg| arg.value.variable(subs))
                                .collect(),
                        }))
                    }
                    Some(hir::ExecutableItem::Pipeline(_)) => {
                        panic!("Expected function definition, found pipeline")
                    }
                    Some(hir::ExecutableItem::Entity(_)) => {
                        panic!("Expected function definition, found entity")
                    }
                    None => {
                        panic!(
                            "Expected to find an executable named {} for function call",
                            name
                        )
                    }
                }
            }
            ExprKind::EntityInstance(name, args) => {
                for arg in args {
                    result.append(&mut arg.value.lower(symtab, idtracker, types, subs, item_list)?)
                }
                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::Instance(name.1.to_string()),
                    operands: args
                        .into_iter()
                        .map(|arg| arg.value.variable(subs))
                        .collect(),
                    ty: types
                        .expr_type(self, symtab.symtab(), &item_list.types)?
                        .to_mir_type(),
                }))
            }
            ExprKind::PipelineInstance {
                depth: _,
                name,
                args,
            } => {
                for arg in args {
                    result.append(&mut arg.value.lower(symtab, idtracker, types, subs, item_list)?)
                }
                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::Instance(name.1.to_string()),
                    operands: args
                        .into_iter()
                        .map(|arg| arg.value.variable(subs))
                        .collect(),
                    ty: types
                        .expr_type(self, symtab.symtab(), &item_list.types)?
                        .to_mir_type(),
                }))
            }
        }
        Ok(result)
    }
}

pub fn generate_entity<'a>(
    entity: &Entity,
    symtab: &mut FrozenSymtab,
    idtracker: &mut ExprIdTracker,
    types: &TypeState,
    item_list: &ItemList,
) -> Result<mir::Entity> {
    let inputs = entity
        .inputs
        .iter()
        .map(|(name_id, _)| {
            let name = format!("_i_{}", name_id.1.to_string());
            let val_name = name_id.value_name();
            let ty = types
                .type_of_name(name_id, symtab.symtab(), &item_list.types)
                .to_mir_type();

            (name, val_name, ty)
        })
        .collect();

    let statements =
        entity
            .body
            .lower(symtab, idtracker, types, &Substitutions::new(), item_list)?;

    let output_t = types
        .expr_type(&entity.body, symtab.symtab(), &item_list.types)?
        .to_mir_type();

    let subs = Substitutions::new();

    Ok(mir::Entity {
        name: entity.name.1.to_string(),
        inputs: inputs,
        output: entity.body.variable(&subs),
        output_type: output_t,
        statements: statements,
    })
}
