use indoc::formatdoc;

use crate::{
    fixed_types::{t_bool, t_clock, t_int},
    hir::{Entity, ExprKind, Expression, Register, Statement},
    types::{ConcreteType, KnownType},
    typeinference::{
        TypeState,
    },
};

mod util;
mod verilog;

use self::{
    util::Code,
    verilog::{assign, reg, size_spec, wire},
};

use crate::code;

fn size_of_type(t: ConcreteType) -> u128 {
    match t.base {
        _t if _t == t_int() => match t.params.as_slice() {
            [ConcreteType {
                base: KnownType::Integer(size),
                ..
            }] => *size,
            other => panic!("Expected integer to have size, got {:?}", other),
        },
        _t if _t == t_bool() => {
            assert!(t.params.is_empty(), "Bool type got generics");

            1
        }
        _t if _t == t_clock() => {
            assert!(t.params.is_empty(), "Clock type got generics");

            1
        }
        KnownType::Integer(_) => {
            panic!("A type level integer has no size")
        }
        KnownType::Unit => 0,
        other => panic!("{:?} has no size right now", other),
    }
}

// Consider rewriting this to be functions on the code struct

impl Register {
    pub fn code(&self, types: &TypeState, code: &mut Code) {
        // Generate the code for the expression
        code.join(&self.value.code(types));
        code.join(&self.clock.code(types));

        let this_var = format!("_m_{}", self.name.inner);
        let this_type = types.type_of_name(&self.name.clone().to_path());

        // Declare the register
        code.join(&reg(&this_var, size_of_type(this_type)));

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

                let this_var = format!("_m_{}", name.inner);
                let this_type = types.type_of_name(&name.clone().to_path());

                // Declare the register
                code.join(&wire(&this_var, size_of_type(this_type)));

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
            ExprKind::Identifier(ident) => Some(ident.inner.mangle()),
            ExprKind::IntLiteral(_) => None,
            ExprKind::BoolLiteral(_) => None,
            ExprKind::FnCall(_, _) => None,
            ExprKind::Block(block) => Some(block.result.inner.variable()),
            ExprKind::If(_, _, _) => None,
        }
    }

    pub fn requires_reg(&self) -> bool {
        match &self.kind {
            ExprKind::Identifier(_) => false,
            ExprKind::IntLiteral(_) => false,
            ExprKind::BoolLiteral(_) => false,
            ExprKind::FnCall(_, _) => false,
            ExprKind::Block(_) => false,
            ExprKind::If(_, _, _) => true,
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
                code.join(&reg(&self.variable(), size_of_type(types.expr_type(self))))
            } else {
                code.join(&wire(&self.variable(), size_of_type(types.expr_type(self))))
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
            ExprKind::FnCall(name, params) => {
                let mut binop_builder = |op| {
                    if let [lhs, rhs] = params.as_slice() {
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
                    } else {
                        panic!("Binary operation called with more than 2 arguments")
                    }
                };

                // TODO: Propper error handling
                match name
                    .inner
                    .maybe_slices()
                    .expect("Anonymous functions can not be codegened right now")
                    .as_slice()
                {
                    ["intrinsics", "add"] => binop_builder("+"),
                    ["intrinsics", "sub"] => binop_builder("-"),
                    ["intrinsics", "mul"] => binop_builder("*"),
                    ["intrinsics", "eq"] => binop_builder("=="),
                    ["intrinsics", "lt"] => binop_builder("<"),
                    ["intrinsics", "gt"] => binop_builder(">"),
                    ["intrinsics", "left_shift"] => binop_builder("<<"),
                    ["intrinsics", "right_shift"] => binop_builder(">>"),
                    ["intrinsics", "logical_and"] => binop_builder("&&"),
                    ["intrinsics", "logical_or"] => binop_builder("||"),
                    _ => panic!("Unrecognised function {}", name.inner),
                }
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
    let inputs = entity.head.inputs.iter().map(|(name, _)| {
        let t = types.type_of_name(&Path(vec![name.inner.clone()]));
        format!("input{} _m_{},", size_spec(size_of_type(t)), name.inner)
    });

    let output_t = types.expr_type(&entity.body);
    let output_definition = format!("output{} __output", size_spec(size_of_type(output_t)));

    let output_assignment = assign("__output", &entity.body.inner.variable());

    code! {
        [0] &format!("module {} (", entity.name.inner);
                [2] &inputs.collect::<Vec<_>>();
                [2] &output_definition;
            [1] &");";
            [1] &entity.body.inner.code(types);
            [1] &output_assignment;
        [0] &"endmodule"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_same_code, testutil::parse_typecheck_entity};
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
                input[15:0] _m_a,
                input[15:0] _m_b,
                output[15:0] __output
            );
            assign __output = _m_a;
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
                input _m_c,
                input[15:0] _m_a,
                input[15:0] _m_b,
                output[15:0] __output
            );
            reg[15:0] __expr__3;
            always @* begin
                if (_m_c) begin
                    __expr__3 = _m_a;
                end
                else begin
                    __expr__3 = _m_b;
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
                input[15:0] _m_a,
                input[15:0] _m_b,
                output[15:0] __output
            );
            wire[15:0] __expr__2;
            assign __expr__2 = _m_a + _m_b;
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
                input[15:0] _m_a,
                input[15:0] _m_b,
                output[15:0] __output
            );
            wire[15:0] __expr__2;
            assign __expr__2 = _m_a << _m_b;
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
                input[15:0] _m_a,
                input[15:0] _m_b,
                output[15:0] __output
            );
            wire[15:0] __expr__2;
            assign __expr__2 = _m_a >> _m_b;
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
                input[15:0] _m_a,
                input[15:0] _m_b,
                output __output
            );
            wire __expr__2;
            assign __expr__2 = _m_a == _m_b;
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
                input _m_a,
                input _m_b,
                output __output
            );
            wire __expr__2;
            assign __expr__2 = _m_a && _m_b;
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
                input _m_a,
                input _m_b,
                output __output
            );
            wire __expr__2;
            assign __expr__2 = _m_a || _m_b;
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
                input[15:0] _m_a,
                input[15:0] _m_b,
                output __output
            );
            wire __expr__2;
            assign __expr__2 = _m_a < _m_b;
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
                input _m_clk,
                input[15:0] _m_a,
                output[15:0] __output
            );
            reg[15:0] _m_res;
            always @(posedge _m_clk) begin
                _m_res <= _m_a;
            end
            assign __output = _m_res;
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
                input _m_clk,
                input _m_rst,
                input[15:0] _m_a,
                output[15:0] __output
            );
            reg[15:0] _m_res;
            wire[15:0] __expr__2;
            assign __expr__2 = 0;
            always @(posedge _m_clk, posedge _m_rst) begin
                if (_m_rst) begin
                    _m_res <= __expr__2;
                end
                else begin
                    _m_res <= _m_a;
                end
            end
            assign __output = _m_res;
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
                input _m_clk,
                input[15:0] _m_a,
                output[15:0] __output
            );
            wire[15:0] _m_res;
            assign _m_res = _m_a;
            assign __output = _m_res;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).to_string();
        assert_same_code!(&result, expected);
    }
}
