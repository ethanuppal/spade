#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use colored::Colorize;
    use spade_hir_lowering::error_reporting::report_hir_lowering_error;
    use spade_hir_lowering::*;
    use spade_mir::{
        self,
        diff::{compare_entity, VarMap},
        diff_printing::translated_strings,
        entity,
        types::Type,
        ConstantValue,
    };
    use spade_testutil::{parse_typecheck_entity, parse_typecheck_module_body};

    pub trait ResultExt<T> {
        fn report_failure(self) -> T;
    }
    impl<T> ResultExt<T> for Result<T> {
        fn report_failure(self) -> T {
            match self {
                Ok(t) => t,
                Err(e) => {
                    report_hir_lowering_error(&PathBuf::from(""), "", e, false);
                    panic!("Compilation error")
                }
            }
        }
    }

    macro_rules! assert_same_mir {
        ($got:expr, $expected:expr) => {
            let mut var_map = VarMap::new();

            if !compare_entity($got, $expected, &mut var_map) {
                let (got, expected) = translated_strings($got, $expected, &var_map);

                println!("{}:\n{}", "got".red(), got);
                println!("{}", "==============================================".red());
                println!("{}:\n{}", "expected".green(), expected);
                println!(
                    "{}",
                    "==============================================".green()
                );
                println!("{}", prettydiff::diff_chars(&got, &expected));
                println!(
                    "{}",
                    "==============================================".yellow()
                );
                panic!("Code missmatch")
            }
        };
    }

    #[test]
    fn entity_defintions_are_correct() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
        ) -> Type::Int(16); {
        } => n(0, "a"));

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();

        assert_same_mir!(&result, &expected);
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

        let expected = entity! {"name"; (
                "_i_c", n(0, "c"), Type::Bool,
                "_i_a", n(1, "a"), Type::Int(16),
                "_i_b", n(2, "b"), Type::Int(16)
            ) -> Type::Int(16); {
                (e(0); Type::Int(16); Select; n(0, "c"), n(1, "a"), n(2, "b"))
            } => e(0)
        };

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();

        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn bool_literals_codegen() {
        let code = r#"
        entity always_true() -> bool {
            true
        }
        "#;

        let expected = entity! {"always_true"; () -> Type::Bool; {
            (const 0; Type::Bool; ConstantValue::Bool(true))
        } => e(0)};

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn an_adder_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a + b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Int(16); {
                (e(0); Type::Int(16); Add; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn an_subtractor_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a - b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Int(16); {
                (e(0); Type::Int(16); Sub; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn a_left_shifter_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a << b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Int(16); {
                (e(0); Type::Int(16); LeftShift; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn a_right_shifter_is_buildable() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a >> b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Int(16); {
                (e(0); Type::Int(16); RightShift; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn equals_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a == b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Eq; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn logical_and_operator_codegens_correctly() {
        let code = r#"
        entity name(a: bool, b: bool) -> bool {
            a && b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Bool,
                "_i_b", n(1, "b"), Type::Bool
            ) -> Type::Bool; {
                (e(0); Type::Bool; LogicalAnd; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn logical_or_operator_codegens_correctly() {
        let code = r#"
        entity name(a: bool, b: bool) -> bool {
            a || b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Bool,
                "_i_b", n(1, "b"), Type::Bool
            ) -> Type::Bool; {
                (e(0); Type::Bool; LogicalOr; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn greater_than_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a > b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Gt; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn less_than_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a < b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Lt; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn registers_work() {
        let code = r#"
        entity name(clk: clk, a: int<16>) -> int<16> {
            reg(clk) res = a;
            res
        }
        "#;

        let expected = entity! {"name"; (
                "_i_clk", n(0, "clk"), Type::Bool,
                "_i_a", n(1, "a"), Type::Int(16),
            ) -> Type::Int(16); {
                (reg n(0, "res"); Type::Int(16); clock(n(0, "clk")); n(1, "a"))
            } => n(0, "res")
        };

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn registers_with_reset_work() {
        let code = r#"
        entity name(clk: clk, rst: bool, a: int<16>) -> int<16> {
            reg(clk) res reset (rst: 0) = a;
            res
        }
        "#;

        let expected = entity! {"name"; (
                "_i_clk", n(0, "clk"), Type::Bool,
                "_i_rst", n(2, "rst"), Type::Bool,
                "_i_a", n(1, "a"), Type::Int(16),
            ) -> Type::Int(16); {
                (const 0; Type::Int(16); ConstantValue::Int(0));
                (reg n(0, "res");
                    Type::Int(16);
                    clock(n(0, "clk"));
                    reset (n(2, "rst"), e(0));
                    n(1, "a"))
            } => n(0, "res")
        };

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn untyped_let_bindings_work() {
        let code = r#"
        entity name(clk: clk, a: int<16>) -> int<16> {
            let res = a;
            res
        }
        "#;

        let expected = entity! {"name"; (
                "_i_clk", n(0, "clk"), Type::Bool,
                "_i_a", n(1, "a"), Type::Int(16),
            ) -> Type::Int(16); {
                (n(2, "res"); Type::Int(16); Alias; n(1, "a"));
            } => n(2, "res")
        };

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn tuple_indexing_and_creation_works() {
        let code = r#"
        entity name(a: int<16>, b: int<8>) -> int<8> {
            let compound = (a, b);
            compound#1
        }
        "#;

        let tup_inner = vec![Type::Int(16), Type::Int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(8),
            ) -> Type::Int(8); {
                (e(1); tup_type.clone(); ConstructTuple; n(0, "a"), n(1, "b"));
                (n(2, "compound"); tup_type; Alias; e(1));
                (e(0); Type::Int(8); IndexTuple((1, tup_inner)); n(2, "compound"));
            } => e(0)
        );

        let processed = parse_typecheck_entity(code);

        let result = generate_entity(&processed.entity, &processed.type_state).report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn entity_instanciation_works() {
        let code = r#"
            entity sub(a: int<16>) -> int<16> {
                a
            }

            entity top() -> int<16> {
                inst sub(0)
            }
        "#;

        let expected = vec![
            entity!("sub"; (
                    "_i_a", n(0, "a"), Type::Int(16)
                ) -> Type::Int(16); {
                } => n(0, "a")
            ),
            entity!("top"; () -> Type::Int(16); {
                (const 1; Type::Int(16); ConstantValue::Int(0));
                (e(0); Type::Int(16); Instance(("sub".to_string())); e(1))
            } => e(0)),
        ];

        let module = parse_typecheck_module_body(code);

        let mut result = vec![];
        for processed in module {
            result.push(generate_entity(&processed.entity, &processed.type_state).report_failure());
        }

        for (exp, res) in expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    }
}
