pub mod error_reporting;

use spade_common::location_info::Loc;
use spade_hir::{expression::BinaryOperator, Entity, ExprKind, Expression, NameID, Statement};
use spade_mir as mir;
use spade_typeinference::{
    equation::{TypeVar, TypedExpression},
    TypeState,
};
use spade_types::{BaseType, ConcreteType, KnownType};

pub enum Error {
    UsingGenericType { expr: Loc<Expression>, t: TypeVar },
}
pub type Result<T> = std::result::Result<T, Error>;

pub trait Manglable {
    fn mangled(&self) -> String;
}
impl Manglable for NameID {
    fn mangled(&self) -> String {
        format!("_m{}_{}", self.0, self.1)
    }
}

trait TypeStateLocal {
    fn expr_type(&self, expr: &Loc<Expression>) -> Result<ConcreteType>;
}

impl TypeStateLocal for TypeState {
    /// Returns the type of the expression as a concrete type. If the type is not
    /// fully ungenerified, returns the corresponding type var
    fn expr_type(&self, expr: &Loc<Expression>) -> Result<ConcreteType> {
        let t = self
            .type_of(&TypedExpression::Id(expr.id))
            .expect("Expression had no specified type");

        if let Some(t) = Self::ungenerify_type(&t) {
            Ok(t)
        } else {
            Err(Error::UsingGenericType {
                expr: expr.clone(),
                t: t.clone(),
            })
        }
    }
}

trait ConcreteTypeLocal {
    fn to_mir_type(&self) -> mir::types::Type;
}
impl ConcreteTypeLocal for ConcreteType {
    fn to_mir_type(&self) -> mir::types::Type {
        use mir::types::Type;
        use BaseType as BType;
        use ConcreteType as CType;
        use KnownType as KType;

        match self {
            CType::Tuple(inner) => {
                Type::Tuple(inner.iter().map(ConcreteTypeLocal::to_mir_type).collect())
            }
            CType::Single {
                base: KType::Type(BType::Bool),
                params: _,
            } => Type::Bool,
            CType::Single {
                base: KType::Type(BType::Clock),
                params: _,
            } => Type::Bool,
            CType::Single {
                base: KType::Type(BType::Int),
                params,
            } => match params.as_slice() {
                [CType::Single {
                    base: KType::Integer(val),
                    ..
                }] => Type::Int(*val as u64),
                t => unreachable!("{:?} is an invalid generic parameter for an integer", t),
            },
            CType::Single {
                base: KType::Type(BType::Unit),
                ..
            } => {
                todo!("add lowering support for unit types")
            }
            CType::Single {
                base: KType::Integer(_),
                ..
            } => {
                unreachable!("Found an integer at the base level of a type")
            }
        }
    }
}

trait NameIDLocal {
    fn value_name(&self) -> mir::ValueName;
}
impl NameIDLocal for NameID {
    fn value_name(&self) -> mir::ValueName {
        let mangled = format!("{}", self.1);
        mir::ValueName::Named(self.0, mangled)
    }
}

// TODO: Consider adding a proc-macro to add these local derives automatically

trait StatementLocal {
    fn lower(&self, types: &TypeState) -> Result<Vec<mir::Statement>>;
}
impl StatementLocal for Statement {
    fn lower(&self, types: &TypeState) -> Result<Vec<mir::Statement>> {
        let mut result = vec![];
        match &self {
            Statement::Binding(name, _t, value) => {
                result.append(&mut value.lower(types)?);

                result.push(mir::Statement::Binding(mir::Binding {
                    name: name.value_name(),
                    operator: mir::Operator::Alias,
                    operands: vec![value.variable()],
                    ty: types.type_of_name(name).to_mir_type(),
                }));
            }
            Statement::Register(register) => {
                result.append(&mut register.clock.lower(types)?);

                if let Some((trig, value)) = &register.reset {
                    result.append(&mut trig.lower(types)?);
                    result.append(&mut value.lower(types)?);
                }

                result.append(&mut register.value.lower(types)?);

                result.push(mir::Statement::Register(mir::Register {
                    name: register.name.value_name(),
                    ty: types.type_of_name(&register.name).to_mir_type(),
                    clock: register.clock.variable(),
                    reset: register
                        .reset
                        .as_ref()
                        .map(|(value, trig)| (value.variable(), trig.variable())),
                    value: register.value.variable(),
                }))
            }
        }
        Ok(result)
    }
}

trait ExprLocal {
    fn alias(&self) -> Option<mir::ValueName>;

    // NOTE: this impl and a few others could be moved to a impl block that does not have
    // the Loc requirement if desired
    fn variable(&self) -> mir::ValueName;

    fn lower(&self, types: &TypeState) -> Result<Vec<mir::Statement>>;
}
impl ExprLocal for Loc<Expression> {
    /// If the verilog code for this expression is just an alias for another variable
    /// that is returned here. This allows us to skip generating wires that we don't
    /// really need
    fn alias(&self) -> Option<mir::ValueName> {
        match &self.kind {
            ExprKind::Identifier(ident) => Some(ident.value_name()),
            ExprKind::IntLiteral(_) => None,
            ExprKind::BoolLiteral(_) => None,
            ExprKind::FnCall(_, _) => None,
            ExprKind::TupleLiteral(_) => None,
            ExprKind::TupleIndex(_, _) => None,
            ExprKind::Block(block) => Some(block.result.variable()),
            ExprKind::If(_, _, _) => None,
            ExprKind::BinaryOperator(_, _, _) => None,
            ExprKind::EntityInstance(_, _) => None,
        }
    }

    // NOTE: this impl and a few others could be moved to a impl block that does not have
    // the Loc requirement if desired
    fn variable(&self) -> mir::ValueName {
        // If this expressions should not use the standard __expr__{} variable,
        // that is specified here

        self.alias()
            .unwrap_or_else(|| mir::ValueName::Expr(self.id))
    }

    fn lower(&self, types: &TypeState) -> Result<Vec<mir::Statement>> {
        let mut result = vec![];

        let self_type = types.expr_type(self)?.to_mir_type();

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
            ExprKind::FnCall(_name, _params) => {
                todo!("Support codegen for function calls")
            }
            ExprKind::BinaryOperator(lhs, op, rhs) => {
                let binop_builder = |op| {
                    result.append(&mut lhs.lower(types)?);
                    result.append(&mut rhs.lower(types)?);

                    result.push(mir::Statement::Binding(mir::Binding {
                        name: self.variable(),
                        operator: op,
                        operands: vec![lhs.variable(), rhs.variable()],
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
                };
            }
            ExprKind::TupleLiteral(elems) => {
                for elem in elems {
                    result.append(&mut elem.lower(types)?)
                }

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(),
                    operator: mir::Operator::ConstructTuple,
                    operands: elems.iter().map(|e| e.variable()).collect(),
                    ty: self_type,
                }))
                // for elem in elems {
                //     code.join(&elem.code(types)?);
                // }
                // let elem_code = elems
                //     .iter()
                //     // NOTE: we reverse here in order to get the first element in the lsb position
                //     .rev()
                //     .map(|elem| elem.variable())
                //     .collect::<Vec<_>>()
                //     .join(", ");
                // code.join(&assign(&self.variable(), &format!("{{{}}}", elem_code)))
            }
            ExprKind::TupleIndex(tup, idx) => {
                result.append(&mut tup.lower(types)?);

                let types =
                    if let mir::types::Type::Tuple(inner) = &types.expr_type(tup)?.to_mir_type() {
                        inner.clone()
                    } else {
                        unreachable!("Tupel indexing of non-tuple: {:?}", self_type);
                    };

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(),
                    operator: mir::Operator::IndexTuple(idx.inner as u64, types),
                    operands: vec![tup.variable()],
                    ty: self_type,
                }))
                // code.join(&tup.code(types)?);

                // let types = match types.expr_type(tup)? {
                //     ConcreteType::Tuple(inner) => inner,
                //     ConcreteType::Single { .. } => {
                //         panic!("Tuple indexing of non-tuple after type check");
                //     }
                // };
                // // Compute the start index of the element we're looking for
                // let mut start_idx = 0;
                // for i in 0..idx.inner {
                //     start_idx += size_of_type(&types[i as usize]);
                // }

                // let end_idx = start_idx + size_of_type(&types[idx.inner as usize]) - 1;

                // let index = if start_idx == end_idx {
                //     format!("{}", start_idx)
                // } else {
                //     format!("{}:{}", end_idx, start_idx)
                // };

                // code.join(&assign(
                //     &self.variable(),
                //     &format!("{}[{}]", tup.variable(), index),
                // ));
            }
            ExprKind::Block(block) => {
                for statement in &block.statements {
                    result.append(&mut statement.lower(types)?);
                }
                result.append(&mut block.result.lower(types)?);

                // Empty. The block result will always be the last expression
            }
            ExprKind::If(cond, on_true, on_false) => {
                result.append(&mut cond.lower(types)?);
                result.append(&mut on_true.lower(types)?);
                result.append(&mut on_false.lower(types)?);

                result.push(mir::Statement::Binding(mir::Binding {
                    name: self.variable(),
                    operator: mir::Operator::Select,
                    operands: vec![cond.variable(), on_true.variable(), on_false.variable()],
                    ty: types.expr_type(self)?.to_mir_type(),
                }));
            }
            ExprKind::EntityInstance(name, _) => {
                todo!("Implement mir lowering for entity instanciation")
            }
        }
        Ok(result)
    }
}

pub fn generate_entity<'a>(entity: &Entity, types: &TypeState) -> Result<mir::Entity> {
    let inputs = entity
        .inputs
        .iter()
        .map(|(name_id, _)| {
            let name = format!("_i_{}", name_id.1.to_string());
            let val_name = name_id.value_name();
            let ty = types.type_of_name(name_id).to_mir_type();

            (name, val_name, ty)
        })
        .collect();

    let statements = entity.body.lower(types)?;

    let output_t = types.expr_type(&entity.body)?.to_mir_type();

    Ok(mir::Entity {
        name: entity.name.1.to_string(),
        inputs: inputs,
        output: entity.body.variable(),
        output_type: output_t,
        statements: statements,
    })
}
