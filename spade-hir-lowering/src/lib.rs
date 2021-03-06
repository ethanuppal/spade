use indoc::formatdoc;

use spade_common::location_info::Loc;
use spade_hir::{
    expression::BinaryOperator, Entity, ExprKind, Expression, NameID, Register, Statement,
};
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
trait RegisterLocal {
    fn mir_statement(&self, types: &TypeState) -> Result<mir::Register>;
}
impl RegisterLocal for Register {
    fn mir_statement(&self, types: &TypeState) -> Result<mir::Register> {
        unimplemented!()
        /*
        // Generate the code for the expression
        code.join(&self.value.code(types)?);
        code.join(&self.clock.code(types)?);

        let this_var = self.name.mangled();
        let this_type = types.type_of_name(&self.name.clone());

        // Declare the register
        code.join(&reg(&this_var, size_of_type(&this_type)));

        // The codegen depends quite a bit on wether or not
        // a reset is present, so we'll do those completely
        // separately for now
        let this_code = if let Some((rst_cond, rst_value)) = &self.reset {
            code.join(&rst_cond.code(types)?);
            code.join(&rst_value.code(types)?);
            formatdoc! {r#"
                always @(posedge {}, posedge {}) begin
                    if ({}) begin
                        {} <= {};
                    end
                    else begin
                        {} <= {};
                    end
                end"#,
                self.clock.variable(),
                rst_cond.variable(),
                rst_cond.variable(),
                this_var,
                rst_value.variable(),
                this_var,
                self.value.variable()
            }
        } else {
            formatdoc! {r#"
                always @(posedge {}) begin
                    {} <= {};
                end"#,
                self.clock.variable(),
                this_var,
                self.value.variable()
            }
        };

        code.join(&this_code);
        Ok(())
        */
    }
}

trait StatementLocal {
    fn code(&self, types: &TypeState) -> Result<Statement>;
}
impl StatementLocal for Statement {
    fn code(&self, types: &TypeState) -> Result<Statement> {
        match &self {
            Statement::Binding(name, _t, value) => {
                unimplemented!();
                // code.join(&value.code(types)?);

                // let this_var = name.mangled();
                // let this_type = types.type_of_name(&name);

                // // Declare the register
                // code.join(&wire(&this_var, size_of_type(&this_type)));

                // // Define the wire containing the value
                // let this_code = formatdoc! {r#"
                //     assign {} = {};"#,
                //     this_var,
                //     value.variable()
                // };

                // code.join(&this_code)
            }
            Statement::Register(register) => {
                unimplemented!()
                // register.code(types, code)?;
            }
        }
        // Ok(())
    }
}

trait ExprLocal {
    fn alias(&self) -> Option<mir::ValueName>;

    // True if a verilog register has to be created for the value instead of a
    // wire. This is required if the processing is in an always block
    fn requires_reg(&self) -> bool;

    // NOTE: this impl and a few others could be moved to a impl block that does not have
    // the Loc requirement if desired
    fn variable(&self) -> mir::ValueName;

    fn code(&self, types: &TypeState) -> Result<mir::Binding>;
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
        }
    }

    // True if a verilog register has to be created for the value instead of a
    // wire. This is required if the processing is in an always block
    fn requires_reg(&self) -> bool {
        match &self.kind {
            ExprKind::Identifier(_) => false,
            ExprKind::IntLiteral(_) => false,
            ExprKind::BoolLiteral(_) => false,
            ExprKind::FnCall(_, _) => false,
            ExprKind::Block(_) => false,
            ExprKind::If(_, _, _) => true,
            ExprKind::TupleIndex(_, _) => false,
            ExprKind::TupleLiteral(_) => false,
            ExprKind::BinaryOperator(_, _, _) => false,
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

    fn code(&self, types: &TypeState) -> Result<mir::Binding> {
        unimplemented!()
        // let mut code = Code::new();

        // // Define the wire if it is needed
        // if self.alias().is_none() {
        //     if self.requires_reg() {
        //         code.join(&reg(
        //             &self.variable(),
        //             size_of_type(&types.expr_type(self)?),
        //         ))
        //     } else {
        //         code.join(&wire(
        //             &self.variable(),
        //             size_of_type(&types.expr_type(self)?),
        //         ))
        //     }
        // }

        // match &self.kind {
        //     ExprKind::Identifier(_) => {
        //         // Empty. The identifier will be defined elsewhere
        //     }
        //     ExprKind::IntLiteral(value) => {
        //         let this_code = assign(&self.variable(), &format!("{}", value));
        //         code.join(&this_code);
        //     }
        //     ExprKind::BoolLiteral(value) => {
        //         let this_code =
        //             assign(&self.variable(), &format!("{}", if *value { 1 } else { 0 }));
        //         code.join(&this_code);
        //     }
        //     ExprKind::FnCall(_name, _params) => {
        //         todo!("Support codegen for function calls")
        //         // let mut binop_builder = |op| {
        //         //     if let [lhs, rhs] = params.as_slice() {
        //         //         code.join(&lhs.inner.code(types));
        //         //         code.join(&rhs.inner.code(types));

        //         //         let this_code = formatdoc! {r#"
        //         //             assign {} = {} {} {};"#,
        //         //             self.variable(),
        //         //             lhs.inner.variable(),
        //         //             op,
        //         //             rhs.inner.variable(),
        //         //         };
        //         //         code.join(&this_code)
        //         //     } else {
        //         //         panic!("Binary operation called with more than 2 arguments")
        //         //     }
        //         // };

        //         // // TODO: Propper error handling
        //         // match name
        //         //     .inner
        //         //     .maybe_slices()
        //         //     .expect("Anonymous functions can not be codegened right now")
        //         //     .as_slice()
        //         // {
        //         //     ["intrinsics", "add"] => binop_builder("+"),
        //         //     ["intrinsics", "sub"] => binop_builder("-"),
        //         //     ["intrinsics", "mul"] => binop_builder("*"),
        //         //     ["intrinsics", "eq"] => binop_builder("=="),
        //         //     ["intrinsics", "lt"] => binop_builder("<"),
        //         //     ["intrinsics", "gt"] => binop_builder(">"),
        //         //     ["intrinsics", "left_shift"] => binop_builder("<<"),
        //         //     ["intrinsics", "right_shift"] => binop_builder(">>"),
        //         //     ["intrinsics", "logical_and"] => binop_builder("&&"),
        //         //     ["intrinsics", "logical_or"] => binop_builder("||"),
        //         //     _ => panic!("Unrecognised function {}", name.inner),
        //         // }
        //     }
        //     ExprKind::BinaryOperator(lhs, op, rhs) => {
        //         let mut binop_builder = |op| {
        //             code.join(&lhs.code(types)?);
        //             code.join(&rhs.code(types)?);

        //             let this_code = formatdoc! {r#"
        //                 assign {} = {} {} {};"#,
        //                 self.variable(),
        //                 lhs.variable(),
        //                 op,
        //                 rhs.variable(),
        //             };
        //             code.join(&this_code);
        //             Ok(())
        //         };

        //         match op {
        //             BinaryOperator::Add => binop_builder("+")?,
        //             BinaryOperator::Sub => binop_builder("-")?,
        //             BinaryOperator::Mul => binop_builder("*")?,
        //             BinaryOperator::Eq => binop_builder("==")?,
        //             BinaryOperator::Gt => binop_builder(">")?,
        //             BinaryOperator::Lt => binop_builder("<")?,
        //             BinaryOperator::LeftShift => binop_builder("<<")?,
        //             BinaryOperator::RightShift => binop_builder(">>")?,
        //             BinaryOperator::LogicalAnd => binop_builder("&&")?,
        //             BinaryOperator::LogicalOr => binop_builder("||")?,
        //         };
        //     }
        //     ExprKind::TupleLiteral(elems) => {
        //         for elem in elems {
        //             code.join(&elem.code(types)?);
        //         }
        //         let elem_code = elems
        //             .iter()
        //             // NOTE: we reverse here in order to get the first element in the lsb position
        //             .rev()
        //             .map(|elem| elem.variable())
        //             .collect::<Vec<_>>()
        //             .join(", ");
        //         code.join(&assign(&self.variable(), &format!("{{{}}}", elem_code)))
        //     }
        //     ExprKind::TupleIndex(tup, idx) => {
        //         code.join(&tup.code(types)?);

        //         let types = match types.expr_type(tup)? {
        //             ConcreteType::Tuple(inner) => inner,
        //             ConcreteType::Single { .. } => {
        //                 panic!("Tuple indexing of non-tuple after type check");
        //             }
        //         };
        //         // Compute the start index of the element we're looking for
        //         let mut start_idx = 0;
        //         for i in 0..idx.inner {
        //             start_idx += size_of_type(&types[i as usize]);
        //         }

        //         let end_idx = start_idx + size_of_type(&types[idx.inner as usize]) - 1;

        //         let index = if start_idx == end_idx {
        //             format!("{}", start_idx)
        //         } else {
        //             format!("{}:{}", end_idx, start_idx)
        //         };

        //         code.join(&assign(
        //             &self.variable(),
        //             &format!("{}[{}]", tup.variable(), index),
        //         ));
        //     }
        //     ExprKind::Block(block) => {
        //         for statement in &block.statements {
        //             statement.code(types, &mut code)?;
        //         }
        //         code.join(&block.result.code(types)?)
        //         // Empty. The block result will always be the last expression
        //     }
        //     ExprKind::If(cond, on_true, on_false) => {
        //         // TODO: Add a code struct that handles all this bullshit
        //         code.join(&cond.code(types)?);
        //         code.join(&on_true.code(types)?);
        //         code.join(&on_false.code(types)?);

        //         let self_var = self.variable();
        //         let this_code = formatdoc! {r#"
        //             always @* begin
        //                 if ({}) begin
        //                     {} = {};
        //                 end
        //                 else begin
        //                     {} = {};
        //                 end
        //             end"#,
        //             cond.variable(),
        //             self_var,
        //             on_true.variable(),
        //             self_var,
        //             on_false.variable()
        //         };
        //         code.join(&this_code)
        //     }
        // }
        // Ok(code)
    }
}

pub fn generate_entity<'a>(entity: &Entity, types: &TypeState) -> Result<mir::Entity> {
    let inputs = entity
        .head
        .inputs
        .iter()
        .map(|(name_id, _)| {
            let name = format!("_i_{}", name_id.1.to_string());
            let val_name = name_id.value_name();
            let ty = types.type_of_name(name_id).to_mir_type();

            (name, val_name, ty)
        })
        .collect();

    let output_t = types.expr_type(&entity.body)?.to_mir_type();

    Ok(mir::Entity {
        name: entity.name.1.to_string(),
        inputs: inputs,
        output: entity.body.variable(),
        output_type: output_t,
        statements: vec![],
    })

    // // Inputs are named _i_{name} and then translated to the name_id name for later use
    // let inputs = entity.head.inputs.iter().map(|(name, _)| {
    //     let input_name = format!("_i_{}", name.1);
    //     let t = types.type_of_name(name);
    //     let size = size_of_type(&t);
    //     (
    //         format!("input{} {},", size_spec(size), input_name),
    //         code! {
    //             [0] &wire(&name.mangled(), size);
    //             [0] &assign(&name.mangled(), &input_name)
    //         },
    //     )
    // });

    // let (inputs, input_assignments): (Vec<_>, Vec<_>) = inputs.unzip();

    // let output_t = types.expr_type(&entity.body)?;

    // let output_definition = format!("output{} __output", size_spec(size_of_type(&output_t)));

    // let output_assignment = assign("__output", &entity.body.variable());

    // Ok(code! {
    //     [0] &format!("module {} (", entity.name.1);
    //             [2] &inputs;
    //             [2] &output_definition;
    //         [1] &");";
    //         [1] &input_assignments;
    //         [1] &entity.body.code(types)?;
    //         [1] &output_assignment;
    //     [0] &"endmodule"
    // })
}
