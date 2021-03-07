/*
#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use colored::Colorize;
    use indoc::indoc;
    use spade_error_reporting as error_reporting;
    use spade_hir_codegen::*;
    use spade_testutil::{assert_same_code, parse_typecheck_entity};

    pub trait ResultExt<T> {
        fn report_failure(self) -> T;
    }
    impl<T> ResultExt<T> for Result<T> {
        fn report_failure(self) -> T {
            match self {
                Ok(t) => t,
                Err(e) => {
                    error_reporting::report_codegen_error(&PathBuf::from(""), "", e, false);
                    panic!("Compilation error")
                }
            }
        }
    }

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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();

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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
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

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
        assert_same_code!(&result, expected);
    }

    #[test]
    fn tuple_indexing_of_booleans_works() {
        let code = r#"
        entity name() -> bool {
            (true, true)#1
        }
        "#;

        let expected = indoc!(
            r#"
        module name (
                output __output
            );
            wire __expr__3;
            wire[1:0] __expr__2;
            wire __expr__0;
            assign __expr__0 = 1;
            wire __expr__1;
            assign __expr__1 = 1;
            assign __expr__2 = {__expr__1, __expr__0};
            assign __expr__3 = __expr__2[1];
            assign __output = __expr__3;
        endmodule"#
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state)
            .report_failure()
            .to_string();
        assert_same_code!(&result, expected);
    }
}
*/
