use indoc::formatdoc;

use crate::{
    hir::{expression::BinaryOperator, Entity, ExprKind, Expression, NameID, Register, Statement},
    typeinference::TypeState,
    types::{BaseType, ConcreteType, KnownType},
};

mod util;
mod verilog;

use self::{
    util::Code,
    verilog::{assign, reg, size_spec, wire},
};

use crate::code;

impl NameID {
    fn mangled(&self) -> String {
        format!("_m{}_{}", self.0, self.1)
    }
}

fn size_of_type(t: &ConcreteType) -> u128 {
    match t {
        ConcreteType::Single {
            base: KnownType::Type(BaseType::Int),
            params,
        } => match params.as_slice() {
            [ConcreteType::Single {
                base: KnownType::Integer(size),
                ..
            }] => *size,
            other => panic!("Expected integer to have size, got {:?}", other),
        },
        ConcreteType::Single {
            base: KnownType::Type(BaseType::Bool),
            params,
        } => {
            assert!(params.is_empty(), "Bool type got generics");

            1
        }
        ConcreteType::Single {
            base: KnownType::Type(BaseType::Clock),
            params,
        } => {
            assert!(params.is_empty(), "Clock type got generics");

            1
        }
        ConcreteType::Single {
            base: KnownType::Integer(_),
            ..
        } => {
            panic!("A type level integer has no size")
        }
        ConcreteType::Tuple(inner) => inner.iter().map(size_of_type).sum(),
        other => panic!("{:?} has no size right now", other),
    }
}

// Consider rewriting this to be functions on the code struct

impl Register {
    pub fn code(&self, types: &TypeState, code: &mut Code) {
        // Generate the code for the expression
        code.join(&self.value.code(types));
        code.join(&self.clock.code(types));

        let this_var = self.name.mangled();
        let this_type = types.type_of_name(&self.name.clone());

        // Declare the register
        code.join(&reg(&this_var, size_of_type(&this_type)));

        // The codegen depends quite a bit on wether or not
        // a reset is present, so we'll do those completely
        // separately for now
        let this_code = if let Some((rst_cond, rst_value)) = &self.reset {
            code.join(&rst_cond.code(types));
            code.join(&rst_value.code(types));
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

        code.join(&this_code)
    }
}

impl Statement {
    pub fn code(&self, types: &TypeState, code: &mut Code) {
        match &self {
            Statement::Binding(name, _t, value) => {
                code.join(&value.code(types));

                let this_var = name.mangled();
                let this_type = types.type_of_name(&name);

                // Declare the register
                code.join(&wire(&this_var, size_of_type(&this_type)));

                // Define the wire containing the value
                let this_code = formatdoc! {r#"
                    assign {} = {};"#,
                    this_var,
                    value.variable()
                };

                code.join(&this_code)
            }
            Statement::Register(register) => {
                register.code(types, code);
            }
        }
    }
}

impl Expression {
    /// If the verilog code for this expression is just an alias for another variable
    /// that is returned here. This allows us to skip generating wires that we don't
    /// really need
    pub fn alias(&self) -> Option<String> {
        match &self.kind {
            ExprKind::Identifier(ident) => Some(ident.mangled()),
            ExprKind::IntLiteral(_) => None,
            ExprKind::BoolLiteral(_) => None,
            ExprKind::FnCall(_, _) => None,
            ExprKind::TupleLiteral(_) => None,
            ExprKind::TupleIndex(_, _) => None,
            ExprKind::Block(block) => Some(block.result.inner.variable()),
            ExprKind::If(_, _, _) => None,
            ExprKind::BinaryOperator(_, _, _) => None,
        }
    }

    // True if a verilog register has to be created for the value instead of a
    // wire. This is required if the processing is in an always block
    pub fn requires_reg(&self) -> bool {
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

    pub fn variable(&self) -> String {
        // If this expressions should not use the standard __expr__{} variable,
        // that is specified here

        self.alias()
            .unwrap_or_else(|| format!("__expr__{}", self.id))
    }

    pub fn code(&self, types: &TypeState) -> Code {
        let mut code = Code::new();

        // Define the wire if it is needed
        if self.alias().is_none() {
            if self.requires_reg() {
                code.join(&reg(&self.variable(), size_of_type(&types.expr_type(self))))
            } else {
                code.join(&wire(
                    &self.variable(),
                    size_of_type(&types.expr_type(self)),
                ))
            }
        }

        match &self.kind {
            ExprKind::Identifier(_) => {
                // Empty. The identifier will be defined elsewhere
            }
            ExprKind::IntLiteral(value) => {
                let this_code = assign(&self.variable(), &format!("{}", value));
                code.join(&this_code);
            }
            ExprKind::BoolLiteral(value) => {
                let this_code =
                    assign(&self.variable(), &format!("{}", if *value { 1 } else { 0 }));
                code.join(&this_code);
            }
            ExprKind::FnCall(_name, _params) => {
                todo!("Support codegen for function calls")
                // let mut binop_builder = |op| {
                //     if let [lhs, rhs] = params.as_slice() {
                //         code.join(&lhs.inner.code(types));
                //         code.join(&rhs.inner.code(types));

                //         let this_code = formatdoc! {r#"
                //             assign {} = {} {} {};"#,
                //             self.variable(),
                //             lhs.inner.variable(),
                //             op,
                //             rhs.inner.variable(),
                //         };
                //         code.join(&this_code)
                //     } else {
                //         panic!("Binary operation called with more than 2 arguments")
                //     }
                // };

                // // TODO: Propper error handling
                // match name
                //     .inner
                //     .maybe_slices()
                //     .expect("Anonymous functions can not be codegened right now")
                //     .as_slice()
                // {
                //     ["intrinsics", "add"] => binop_builder("+"),
                //     ["intrinsics", "sub"] => binop_builder("-"),
                //     ["intrinsics", "mul"] => binop_builder("*"),
                //     ["intrinsics", "eq"] => binop_builder("=="),
                //     ["intrinsics", "lt"] => binop_builder("<"),
                //     ["intrinsics", "gt"] => binop_builder(">"),
                //     ["intrinsics", "left_shift"] => binop_builder("<<"),
                //     ["intrinsics", "right_shift"] => binop_builder(">>"),
                //     ["intrinsics", "logical_and"] => binop_builder("&&"),
                //     ["intrinsics", "logical_or"] => binop_builder("||"),
                //     _ => panic!("Unrecognised function {}", name.inner),
                // }
            }
            ExprKind::BinaryOperator(lhs, op, rhs) => {
                let mut binop_builder = |op| {
                    code.join(&lhs.inner.code(types));
                    code.join(&rhs.inner.code(types));

                    let this_code = formatdoc! {r#"
                        assign {} = {} {} {};"#,
                        self.variable(),
                        lhs.inner.variable(),
                        op,
                        rhs.inner.variable(),
                    };
                    code.join(&this_code)
                };

                match op {
                    BinaryOperator::Add => binop_builder("+"),
                    BinaryOperator::Sub => binop_builder("-"),
                    BinaryOperator::Mul => binop_builder("*"),
                    BinaryOperator::Eq => binop_builder("=="),
                    BinaryOperator::Gt => binop_builder(">"),
                    BinaryOperator::Lt => binop_builder("<"),
                    BinaryOperator::LeftShift => binop_builder("<<"),
                    BinaryOperator::RightShift => binop_builder(">>"),
                    BinaryOperator::LogicalAnd => binop_builder("&&"),
                    BinaryOperator::LogicalOr => binop_builder("||"),
                }
            }
            ExprKind::TupleLiteral(elems) => {
                let elem_code = elems
                    .iter()
                    // NOTE: we reverse here in order to get the first element in the lsb position
                    .rev()
                    .map(|elem| elem.variable())
                    .collect::<Vec<_>>()
                    .join(", ");
                code.join(&assign(&self.variable(), &format!("{{{}}}", elem_code)))
            }
            ExprKind::TupleIndex(tup, idx) => {
                let types = match types.expr_type(tup) {
                    ConcreteType::Tuple(inner) => inner,
                    ConcreteType::Single { .. } => {
                        panic!("Tuple indexing of non-tuple after type check");
                    }
                };
                // Compute the start index of the element we're looking for
                let mut start_idx = 0;
                for i in 0..idx.inner {
                    start_idx += size_of_type(&types[i as usize]);
                }

                let end = start_idx + size_of_type(&types[idx.inner as usize]) - 1;

                code.join(&assign(
                    &self.variable(),
                    &format!("{}[{}:{}]", tup.variable(), end, start_idx),
                ));
            }
            ExprKind::Block(block) => {
                for statement in &block.statements {
                    statement.code(types, &mut code);
                }
                code.join(&block.result.inner.code(types))
                // Empty. The block result will always be the last expression
            }
            ExprKind::If(cond, on_true, on_false) => {
                // TODO: Add a code struct that handles all this bullshit
                code.join(&cond.inner.code(types));
                code.join(&on_true.inner.code(types));
                code.join(&on_false.inner.code(types));

                let self_var = self.variable();
                let this_code = formatdoc! {r#"
                    always @* begin
                        if ({}) begin
                            {} = {};
                        end
                        else begin
                            {} = {};
                        end
                    end"#,
                    cond.inner.variable(),
                    self_var,
                    on_true.inner.variable(),
                    self_var,
                    on_false.inner.variable()
                };
                code.join(&this_code)
            }
        }
        code
    }
}

pub fn generate_entity<'a>(entity: &Entity, types: &TypeState) -> Code {
    // Inputs are named _i_{name} and then translated to the name_id name for later use
    let inputs = entity.head.inputs.iter().map(|(name, _)| {
        let input_name = format!("_i_{}", name.1);
        let t = types.type_of_name(name);
        let size = size_of_type(&t);
        (
            format!("input{} {},", size_spec(size), input_name),
            code! {
                [0] &wire(&name.mangled(), size);
                [0] &assign(&name.mangled(), &input_name)
            },
        )
    });

    let (inputs, input_assignments): (Vec<_>, Vec<_>) = inputs.unzip();

    let output_t = types.expr_type(&entity.body);
    let output_definition = format!("output{} __output", size_spec(size_of_type(&output_t)));

    let output_assignment = assign("__output", &entity.body.inner.variable());

    code! {
        [0] &format!("module {} (", entity.name.1);
                [2] &inputs;
                [2] &output_definition;
            [1] &");";
            [1] &input_assignments;
            [1] &entity.body.inner.code(types);
            [1] &output_assignment;
        [0] &"endmodule"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_same_code, testutil::parse_typecheck_entity};
    use colored::Colorize;
    use indoc::indoc;

    #[test]
    fn entity_defintions_are_correct() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input[15:0] _i_a,
                input[15:0] _i_b,
                output[15:0] __output
            );
            wire[15:0] _m0_a;
            assign _m0_a = _i_a;
            wire[15:0] _m1_b;
            assign _m1_b = _i_b;
            assign __output = _m0_a;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn if_expressions_have_correct_codegen() {
        let code = r#"
        entity name(c: bool, a: int<16>, b: int<16>) -> int<16> {
            if c
                a
            else
                b
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input _i_c,
                input[15:0] _i_a,
                input[15:0] _i_b,
                output[15:0] __output
            );
            wire _m0_c;
            assign _m0_c = _i_c;
            wire[15:0] _m1_a;
            assign _m1_a = _i_a;
            wire[15:0] _m2_b;
            assign _m2_b = _i_b;
            reg[15:0] __expr__3;
            always @* begin
                if (_m0_c) begin
                    __expr__3 = _m1_a;
                end
                else begin
                    __expr__3 = _m2_b;
                end
            end
            assign __output = __expr__3;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn bool_literals_codegen() {
        let code = r#"
        entity always_true() -> bool {
            true
        }
        "#;

        let expected = indoc!(
            r#"
        module always_true (
                output __output
            );
            wire __expr__0;
            assign __expr__0 = 1;
            assign __output = __expr__0;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn an_adder_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a + b
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input[15:0] _i_a,
                input[15:0] _i_b,
                output[15:0] __output
            );
            wire[15:0] _m0_a;
            assign _m0_a = _i_a;
            wire[15:0] _m1_b;
            assign _m1_b = _i_b;
            wire[15:0] __expr__2;
            assign __expr__2 = _m0_a + _m1_b;
            assign __output = __expr__2;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn a_left_shifter_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a << b
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input[15:0] _i_a,
                input[15:0] _i_b,
                output[15:0] __output
            );
            wire[15:0] _m0_a;
            assign _m0_a = _i_a;
            wire[15:0] _m1_b;
            assign _m1_b = _i_b;
            wire[15:0] __expr__2;
            assign __expr__2 = _m0_a << _m1_b;
            assign __output = __expr__2;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn a_right_shifter_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a >> b
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input[15:0] _i_a,
                input[15:0] _i_b,
                output[15:0] __output
            );
            wire[15:0] _m0_a;
            assign _m0_a = _i_a;
            wire[15:0] _m1_b;
            assign _m1_b = _i_b;
            wire[15:0] __expr__2;
            assign __expr__2 = _m0_a >> _m1_b;
            assign __output = __expr__2;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn equals_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a == b
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input[15:0] _i_a,
                input[15:0] _i_b,
                output __output
            );
            wire[15:0] _m0_a;
            assign _m0_a = _i_a;
            wire[15:0] _m1_b;
            assign _m1_b = _i_b;
            wire __expr__2;
            assign __expr__2 = _m0_a == _m1_b;
            assign __output = __expr__2;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn logical_and_operator_codegens_correctly() {
        let code = r#"
        entity name(a: bool, b: bool) -> bool {
            a && b
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input _i_a,
                input _i_b,
                output __output
            );
            wire _m0_a;
            assign _m0_a = _i_a;
            wire _m1_b;
            assign _m1_b = _i_b;
            wire __expr__2;
            assign __expr__2 = _m0_a && _m1_b;
            assign __output = __expr__2;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn logical_or_operator_codegens_correctly() {
        let code = r#"
        entity name(a: bool, b: bool) -> bool {
            a || b
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input _i_a,
                input _i_b,
                output __output
            );
            wire _m0_a;
            assign _m0_a = _i_a;
            wire _m1_b;
            assign _m1_b = _i_b;
            wire __expr__2;
            assign __expr__2 = _m0_a || _m1_b;
            assign __output = __expr__2;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn a_comparator_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a < b
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input[15:0] _i_a,
                input[15:0] _i_b,
                output __output
            );
            wire[15:0] _m0_a;
            assign _m0_a = _i_a;
            wire[15:0] _m1_b;
            assign _m1_b = _i_b;
            wire __expr__2;
            assign __expr__2 = _m0_a < _m1_b;
            assign __output = __expr__2;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn registers_work() {
        let code = r#"
        entity name(clk: clk, a: int<16>) -> int<16> {
            reg(clk) res = a;
            res
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input _i_clk,
                input[15:0] _i_a,
                output[15:0] __output
            );
            wire _m0_clk;
            assign _m0_clk = _i_clk;
            wire[15:0] _m1_a;
            assign _m1_a = _i_a;
            reg[15:0] _m2_res;
            always @(posedge _m0_clk) begin
                _m2_res <= _m1_a;
            end
            assign __output = _m2_res;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn registers_with_reset_work() {
        let code = r#"
        entity name(clk: clk, rst: bool, a: int<16>) -> int<16> {
            reg(clk) res reset (rst: 0) = a;
            res
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input _i_clk,
                input _i_rst,
                input[15:0] _i_a,
                output[15:0] __output
            );
            wire _m0_clk;
            assign _m0_clk = _i_clk;
            wire _m1_rst;
            assign _m1_rst = _i_rst;
            wire[15:0] _m2_a;
            assign _m2_a = _i_a;
            reg[15:0] _m3_res;
            wire[15:0] __expr__2;
            assign __expr__2 = 0;
            always @(posedge _m0_clk, posedge _m1_rst) begin
                if (_m1_rst) begin
                    _m3_res <= __expr__2;
                end
                else begin
                    _m3_res <= _m2_a;
                end
            end
            assign __output = _m3_res;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn untyped_let_bindings_work() {
        let code = r#"
        entity name(clk: clk, a: int<16>) -> int<16> {
            let res = a;
            res
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input _i_clk,
                input[15:0] _i_a,
                output[15:0] __output
            );
            wire _m0_clk;
            assign _m0_clk = _i_clk;
            wire[15:0] _m1_a;
            assign _m1_a = _i_a;
            wire[15:0] _m2_res;
            assign _m2_res = _m1_a;
            assign __output = _m2_res;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn tuple_indexing_and_creation_works() {
        let code = r#"
        entity name(a: int<16>, b: int<8>) -> int<8> {
            let compound = (a, b);
            compound#1
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                input[15:0] _i_a,
                input[7:0] _i_b,
                output[7:0] __output
            );
            wire[15:0] _m0_a;
            assign _m0_a = _i_a;
            wire[7:0] _m1_b;
            assign _m1_b = _i_b;
            wire[23:0] __expr__2;
            assign __expr__2 = {_m1_b, _m0_a};
            wire[23:0] _m2_compound;
            assign _m2_compound = __expr__2;
            wire[7:0] __expr__4;
            assign __expr__4 = _m2_compound[23:16];
            assign __output = __expr__4;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }
}
