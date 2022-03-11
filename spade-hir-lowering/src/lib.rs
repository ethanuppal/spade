pub mod error_reporting;
pub mod pipelines;
pub mod substitution;

use hir::symbol_table::{FrozenSymtab, PatternableKind};
use hir::{Argument, ItemList, Pattern, PatternArgument, TypeList};
use mir::types::Type as MirType;
use mir::{ConstantValue, ValueName};
pub use pipelines::generate_pipeline;
use spade_common::id_tracker::ExprIdTracker;
use spade_common::location_info::WithLocation;
use spade_common::name::{Identifier, Path};
use spade_typeinference::equation::FreeTypeVar;
use substitution::Substitutions;

use parse_tree_macros::local_impl;
use spade_common::{location_info::Loc, name::NameID};
use spade_hir as hir;
use spade_hir::{
    expression::BinaryOperator, symbol_table::SymbolTable, Entity, ExprKind, Expression, Statement,
};
use spade_mir as mir;
use spade_typeinference::{equation::TypedExpression, TypeState};
use spade_types::{ConcreteType, PrimitiveType};

pub enum Error {
    UsingGenericType {
        expr: Loc<Expression>,
        t: FreeTypeVar,
    },
    CastToLarger {
        from: Loc<u64>,
        to: Loc<u64>,
    },
    ConcatSizeMismatch {
        lhs: Loc<u64>,
        rhs: Loc<u64>,
        result: Loc<u64>,
        expected: u64,
    },
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
            .expect("Expression had no specified type")
            .as_free();

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
            CType::Array { inner, size } => Type::Array {
                inner: Box::new(inner.to_mir_type()),
                length: *size as u64,
            },
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
            CType::Single {
                base: PrimitiveType::Memory,
                params,
            } => match params.as_slice() {
                [inner, CType::Integer(length)] => Type::Memory {
                    inner: Box::new(inner.to_mir_type()),
                    length: *length as u64,
                },
                t => unreachable!("{:?} is an invalid generic parameter for a memory", t),
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
            CType::Struct { members } => {
                let members = members.iter().map(|(_, t)| t.to_mir_type()).collect();
                Type::Tuple(members)
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
            hir::PatternKind::Integer(_) => {}
            hir::PatternKind::Bool(_) => {}
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
                let patternable = symtab.patternable_type_by_id(path);
                match patternable.kind {
                    PatternableKind::Struct => {
                        let s = symtab.struct_by_id(path);

                        let inner_types = if let mir::types::Type::Tuple(inner) = &types
                            .type_of_id(self.id, symtab, &item_list.types)
                            .to_mir_type()
                        {
                            inner.clone()
                        } else {
                            unreachable!("Struct destructuring of non-tuple");
                        };

                        for PatternArgument {
                            target,
                            value,
                            kind: _,
                        } in args
                        {
                            let i = s.params.arg_index(target).unwrap();

                            result.push(mir::Statement::Binding(mir::Binding {
                                name: value.value_name(),
                                operator: mir::Operator::IndexTuple(i as u64, inner_types.clone()),
                                operands: vec![self_name.clone()],
                                ty: types
                                    .type_of_id(value.id, symtab, &item_list.types)
                                    .to_mir_type(),
                            }));

                            result.append(&mut value.lower(
                                value.value_name(),
                                symtab,
                                types,
                                subs,
                                item_list,
                            )?)
                        }
                    }
                    PatternableKind::Enum => {
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
            }
        }

        Ok(result)
    }

    /// Returns MIR code for a condition that must hold for `expr` to satisfy
    /// this pattern.
    fn condition(
        &self,
        value_name: &ValueName,
        symtab: &FrozenSymtab,
        idtracker: &mut ExprIdTracker,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &hir::ItemList,
    ) -> Result<PatternCondition> {
        let output_id = idtracker.next();
        let mut result_name = ValueName::Expr(output_id);
        match &self.kind {
            hir::PatternKind::Integer(val) => {
                let self_type = types.type_of_id(self.id, symtab.symtab(), &item_list.types);
                let const_id = idtracker.next();
                let statements = vec![
                    mir::Statement::Constant(
                        const_id,
                        self_type.to_mir_type(),
                        ConstantValue::Int(*val as u64),
                    ),
                    mir::Statement::Binding(mir::Binding {
                        name: result_name.clone(),
                        ty: MirType::Bool,
                        operator: mir::Operator::Eq,
                        operands: vec![value_name.clone(), ValueName::Expr(const_id)],
                    }),
                ];

                Ok(PatternCondition {
                    statements,
                    result_name,
                })
            }
            hir::PatternKind::Bool(true) => Ok(PatternCondition {
                statements: vec![],
                result_name: value_name.clone(),
            }),
            hir::PatternKind::Bool(false) => {
                let statements = vec![mir::Statement::Binding(mir::Binding {
                    name: result_name.clone(),
                    ty: MirType::Bool,
                    operator: mir::Operator::LogicalNot,
                    operands: vec![value_name.clone()],
                })];

                Ok(PatternCondition {
                    statements,
                    result_name,
                })
            }
            hir::PatternKind::Name { .. } => Ok(PatternCondition {
                statements: vec![mir::Statement::Constant(
                    output_id,
                    MirType::Bool,
                    mir::ConstantValue::Bool(true),
                )],
                result_name,
            }),
            hir::PatternKind::Tuple(branches) => {
                assert!(
                    !branches.is_empty(),
                    "Tuple patterns without any subpatterns are unsupported"
                );

                let subpatterns = branches
                    .iter()
                    .map(|pat| {
                        pat.condition(&pat.value_name(), symtab, idtracker, types, subs, item_list)
                    })
                    .collect::<Result<Vec<_>>>()?;

                let mut conditions = subpatterns
                    .iter()
                    // Rev is not strictly nessecary but it makes conditions get generated
                    // left to right
                    .rev()
                    .map(|sub| sub.result_name.clone())
                    .collect::<Vec<_>>();

                let mut statements = subpatterns
                    .into_iter()
                    .map(|sub| sub.statements.into_iter())
                    .flatten()
                    .collect::<Vec<_>>();

                // NOTE: Safe unwrap, we're asserting !is_empty above
                result_name = conditions.pop().unwrap();
                for cond in conditions {
                    let new_result_name = ValueName::Expr(idtracker.next());
                    statements.push(mir::Statement::Binding(mir::Binding {
                        name: new_result_name.clone(),
                        ty: MirType::Bool,
                        operator: mir::Operator::LogicalAnd,
                        operands: vec![result_name, cond],
                    }));
                    result_name = new_result_name;
                }

                Ok(PatternCondition {
                    statements,
                    result_name,
                })
            }
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
                    operands: vec![value_name.clone()],
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
            ExprKind::FieldAccess(_, _) => None,
            ExprKind::ArrayLiteral { .. } => None,
            ExprKind::Index(_, _) => None,
            ExprKind::Block(block) => Some(block.result.variable(subs)),
            ExprKind::If(_, _, _) => None,
            ExprKind::Match(_, _) => None,
            ExprKind::BinaryOperator(_, _, _) => None,
            ExprKind::UnaryOperator(_, _) => None,
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
                    BinaryOperator::Ge => binop_builder(Ge)?,
                    BinaryOperator::Le => binop_builder(Le)?,
                    BinaryOperator::Xor => binop_builder(Xor)?,
                    BinaryOperator::LeftShift => binop_builder(LeftShift)?,
                    BinaryOperator::RightShift => binop_builder(RightShift)?,
                    BinaryOperator::LogicalAnd => binop_builder(LogicalAnd)?,
                    BinaryOperator::LogicalOr => binop_builder(LogicalOr)?,
                    BinaryOperator::BitwiseAnd => binop_builder(BitwiseAnd)?,
                    BinaryOperator::BitwiseOr => binop_builder(BitwiseOr)?,
                };
            }
            ExprKind::UnaryOperator(op, operand) => {
                let binop_builder = |op| {
                    result.append(&mut operand.lower(symtab, idtracker, types, subs, &item_list)?);

                    result.push(mir::Statement::Binding(mir::Binding {
                        name: self.variable(subs),
                        operator: op,
                        operands: vec![operand.variable(subs)],
                        ty: self_type,
                    }));
                    Ok(())
                };
                use mir::Operator::*;
                match op {
                    hir::expression::UnaryOperator::Sub => binop_builder(USub)?,
                    hir::expression::UnaryOperator::Not => binop_builder(Not)?,
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
                    unreachable!("Tuple indexing of non-tuple: {:?}", self_type);
                };

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::IndexTuple(idx.inner as u64, types),
                    operands: vec![tup.variable(subs)],
                    ty: self_type,
                }))
            }
            ExprKind::FieldAccess(target, field) => {
                result.append(&mut target.lower(symtab, idtracker, types, subs, &item_list)?);

                let ctype = types.expr_type(target, symtab.symtab(), &item_list.types)?;

                let member_types = if let mir::types::Type::Tuple(members) = &ctype.to_mir_type() {
                    members.clone()
                } else {
                    unreachable!("Field access on non-struct {:?}", self_type)
                };

                let field_index = if let ConcreteType::Struct { members } = ctype {
                    let field_indices = members
                        .iter()
                        .enumerate()
                        .filter_map(
                            |(i, (name, _))| {
                                if name == &field.inner {
                                    Some(i)
                                } else {
                                    None
                                }
                            },
                        )
                        .collect::<Vec<_>>();

                    assert_eq!(
                        field_indices.len(),
                        1,
                        "Expected exactly 1 field with the name {}",
                        field
                    );

                    *field_indices.first().unwrap()
                } else {
                    unreachable!("Field access on non-struct {:?}", self_type)
                };

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::IndexTuple(field_index as u64, member_types),
                    operands: vec![target.variable(subs)],
                    ty: self_type,
                }))
            }
            ExprKind::ArrayLiteral(values) => {
                for elem in values {
                    result.append(&mut elem.lower(symtab, idtracker, types, subs, &item_list)?)
                }
                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::ConstructArray,
                    operands: values.iter().map(|v| v.variable(subs)).collect(),
                    ty: self_type,
                }))
            }
            ExprKind::Index(target, index) => {
                result.append(&mut target.lower(symtab, idtracker, types, subs, &item_list)?);
                result.append(&mut index.lower(symtab, idtracker, types, subs, &item_list)?);

                let inner_size = if let mir::types::Type::Array { inner, .. } = &types
                    .expr_type(target, symtab.symtab(), &item_list.types)?
                    .to_mir_type()
                {
                    inner.size()
                } else {
                    unreachable!("Array indexing of non array: {:?}", self_type);
                };

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::IndexArray(inner_size as usize),
                    operands: vec![target.variable(subs), index.variable(subs)],
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
                    result.append(&mut pat.lower(
                        operand.variable(subs),
                        symtab.symtab(),
                        types,
                        subs,
                        item_list,
                    )?);

                    let mut cond = pat.condition(
                        &operand.variable(subs),
                        symtab,
                        idtracker,
                        types,
                        subs,
                        item_list,
                    )?;
                    result.append(&mut cond.statements);

                    result
                        .append(&mut result_expr.lower(symtab, idtracker, types, subs, item_list)?);

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
            ExprKind::FnCall(name, args) => result.append(
                &mut self.handle_call(name, args, symtab, idtracker, types, subs, item_list)?,
            ),
            ExprKind::EntityInstance(name, args) => result.append(
                &mut self.handle_call(name, args, symtab, idtracker, types, subs, item_list)?,
            ),
            ExprKind::PipelineInstance {
                depth: _,
                name,
                args,
            } => result.append(
                &mut self.handle_call(name, args, symtab, idtracker, types, subs, item_list)?,
            ),
        }
        Ok(result)
    }

    fn handle_call(
        &self,
        name: &NameID,
        args: &[Argument],
        symtab: &FrozenSymtab,
        idtracker: &mut ExprIdTracker,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = vec![];
        for param in args {
            result.append(
                &mut param
                    .value
                    .lower(symtab, idtracker, types, subs, item_list)?,
            );
        }

        // Check if this is a standard library function which we are supposed to
        // handle
        macro_rules! handle_special_functions {
            ($([$($path:expr),*] => $handler:expr),*) => {
                $(
                    let path = Path(vec![$(Identifier($path.to_string()).nowhere()),*]).nowhere();
                    if symtab.symtab()
                        .try_lookup_final_id(&path)
                        .map(|n| &n == name)
                        .unwrap_or(false)
                    {
                        $handler
                    };
                )*
            }
        }

        handle_special_functions! {
            ["std", "mem", "clocked_memory"] => {
                return self.handle_clocked_memory_decl(
                    result,
                    args,
                    symtab,
                    types,
                    subs,
                    item_list,
                )
            },
            ["std", "mem", "read_mem"] => {
                return self.handle_read_memory(
                    result,
                    args,
                    symtab,
                    types,
                    subs,
                    item_list,
                )
            },
            ["std", "conv", "trunc"] => {
                return self.handle_trunc(
                    result,
                    args,
                    symtab,
                    types,
                    subs,
                    item_list,
                )
            },
            ["std", "conv", "sext"] => {
                return self.handle_sext(
                    result,
                    args,
                    symtab,
                    types,
                    subs,
                    item_list,
                )
            },
            ["std", "conv", "concat"] => {
                return self.handle_concat(
                    result,
                    args,
                    symtab,
                    types,
                    subs,
                    item_list,
                )
            }
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
                    operands: args
                        .into_iter()
                        .map(|arg| arg.value.variable(subs))
                        .collect(),
                }))
            }
            Some(hir::ExecutableItem::StructInstance) => {
                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    ty: types
                        .expr_type(self, symtab.symtab(), &item_list.types)?
                        .to_mir_type(),
                    operator: mir::Operator::ConstructTuple,
                    operands: args
                        .into_iter()
                        .map(|arg| arg.value.variable(subs))
                        .collect(),
                }))
            }
            Some(hir::ExecutableItem::Pipeline(_)) | Some(hir::ExecutableItem::Entity(_)) => {
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
                }));
            }
            None => {
                // NOTE: Something causes entities to not be in the executable list at this point.
                // We'll just ignore that problem and assume it exists for now. Bug introduced
                // in commit 20f58921
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
                }));
            }
        }
        Ok(result)
    }

    /// Result is the initial statement list to expand and return
    fn handle_clocked_memory_decl(
        &self,
        result: Vec<mir::Statement>,
        args: &[Argument],
        symtab: &FrozenSymtab,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        // The localimpl macro is a bit stupid
        let mut result = result;

        let elem_count = if let ConcreteType::Single {
            base: PrimitiveType::Memory,
            params,
        } = types.expr_type(&self, symtab.symtab(), &item_list.types)?
        {
            if let ConcreteType::Integer(size) = params[1] {
                size
            } else {
                panic!("Second param of memory declaration type was not integer")
            }
        } else {
            panic!("Decl memory declares a non-memory")
        };

        // Figure out the sizes of the operands
        let port_t = types.expr_type(&args[1].value, symtab.symtab(), &item_list.types)?;
        if let ConcreteType::Array { inner, size } = port_t {
            if let ConcreteType::Tuple(tup_inner) = *inner {
                assert!(
                    tup_inner.len() == 3,
                    "Expected exactly 3 types in write port tuple"
                );
                let write_ports = size as u64;
                let addr_w = tup_inner[1].to_mir_type().size();
                let inner_w = tup_inner[2].to_mir_type().size();

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(subs),
                    operator: mir::Operator::DeclClockedMemory {
                        addr_w,
                        inner_w,
                        write_ports,
                        elems: elem_count as u64,
                    },
                    operands: args
                        .into_iter()
                        .map(|arg| arg.value.variable(subs))
                        .collect(),
                    ty: types
                        .expr_type(self, symtab.symtab(), &item_list.types)?
                        .to_mir_type(),
                }))
            } else {
                panic!("Clocked array write port inner was not tuple")
            }
        } else {
            panic!("Clocked array write ports were not array")
        }

        return Ok(result);
    }

    /// Result is the initial statement list to expand and return
    fn handle_read_memory(
        &self,
        result: Vec<mir::Statement>,
        args: &[Argument],
        symtab: &FrozenSymtab,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        // The localimpl macro is a bit stupid
        let mut result = result;

        let target = &args[0].value;
        let index = &args[1].value;

        let self_type = types
            .expr_type(self, symtab.symtab(), &item_list.types)?
            .to_mir_type();

        result.push(mir::Statement::Binding(mir::Binding {
            name: self.variable(subs),
            operator: mir::Operator::IndexMemory,
            operands: vec![target.variable(subs), index.variable(subs)],
            ty: self_type,
        }));

        Ok(result)
    }

    fn handle_trunc(
        &self,
        result: Vec<mir::Statement>,
        args: &[Argument],
        symtab: &FrozenSymtab,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = result;

        let self_type = types
            .expr_type(self, symtab.symtab(), &item_list.types)?
            .to_mir_type();

        let input_type = types
            .expr_type(&args[0].value, symtab.symtab(), &item_list.types)?
            .to_mir_type();

        if self_type.size() > input_type.size() {
            return Err(Error::CastToLarger {
                to: self_type.size().at_loc(self),
                from: input_type.size().at_loc(&args[0].value),
            });
        }

        result.push(mir::Statement::Binding(mir::Binding {
            name: self.variable(subs),
            operator: mir::Operator::Truncate,
            operands: vec![args[0].value.variable(subs)],
            ty: types
                .expr_type(self, symtab.symtab(), &item_list.types)?
                .to_mir_type(),
        }));

        Ok(result)
    }

    fn handle_sext(
        &self,
        result: Vec<mir::Statement>,
        args: &[Argument],
        symtab: &FrozenSymtab,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = result;

        let self_type = types
            .expr_type(self, symtab.symtab(), &item_list.types)?
            .to_mir_type();

        let input_type = types
            .expr_type(&args[0].value, symtab.symtab(), &item_list.types)?
            .to_mir_type();

        let extra_bits = if self_type.size() > input_type.size() {
            self_type.size() - input_type.size()
        } else {
            0
        };

        result.push(mir::Statement::Binding(mir::Binding {
            name: self.variable(subs),
            operator: mir::Operator::SignExtend {
                extra_bits,
                operand_size: input_type.size(),
            },
            operands: vec![args[0].value.variable(subs)],
            ty: self_type,
        }));

        Ok(result)
    }

    fn handle_concat(
        &self,
        result: Vec<mir::Statement>,
        args: &[Argument],
        symtab: &FrozenSymtab,
        types: &TypeState,
        subs: &Substitutions,
        item_list: &ItemList,
    ) -> Result<Vec<mir::Statement>> {
        let mut result = result;

        let arg0_type = types
            .expr_type(&args[0].value, symtab.symtab(), &item_list.types)?
            .to_mir_type();
        let arg1_type = types
            .expr_type(&args[1].value, symtab.symtab(), &item_list.types)?
            .to_mir_type();

        let self_type = types
            .expr_type(self, symtab.symtab(), &item_list.types)?
            .to_mir_type();

        if self_type.size() != arg0_type.size() + arg1_type.size() {
            Err(Error::ConcatSizeMismatch {
                lhs: arg0_type.size().at_loc(&args[0].value),
                rhs: arg1_type.size().at_loc(&args[1].value),
                expected: arg0_type.size() + arg1_type.size(),
                result: self_type.size().at_loc(self),
            })
        } else {
            result.push(mir::Statement::Binding(mir::Binding {
                name: self.variable(subs),
                operator: mir::Operator::Concat,
                operands: vec![args[0].value.variable(subs), args[1].value.variable(subs)],
                ty: self_type,
            }));

            Ok(result)
        }
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
            let name = name_id.1.to_string();
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
