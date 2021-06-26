#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use colored::Colorize;
    use spade_common::error_reporting::CompilationError;
    use spade_hir_lowering::*;
    use spade_mir::{
        self,
        diff::{compare_entity, VarMap},
        diff_printing::translated_strings,
        entity,
        types::Type,
        ConstantValue,
    };
    use spade_testutil::{
        parse_typecheck_entity, parse_typecheck_module_body, parse_typecheck_pipeline,
        ParseTypececkResult,
    };
    use spade_typeinference::ProcessedItem;

    pub trait ResultExt<T> {
        fn report_failure(self) -> T;
    }
    impl<T> ResultExt<T> for Result<T> {
        fn report_failure(self) -> T {
            match self {
                Ok(t) => t,
                Err(e) => {
                    e.report(&PathBuf::from(""), "", false);
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
                panic!("Code mismatch")
            }
        };
    }

    macro_rules! build_entity {
        ($code:expr) => {{
            let (processed, symtab) = parse_typecheck_entity($code);
            let result = generate_entity(&processed.entity, symtab.symtab(), &processed.type_state)
                .report_failure();
            result
        }};
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

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn if_expressions_have_correct_codegen() {
        let code = r#"
        entity name(c: bool, a: int<16>, b: int<16>) -> int<16> {
            if c then
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        assert_same_mir!(&build_entity!(code), &expected);
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

        let ParseTypececkResult { items, symtab } = parse_typecheck_module_body(code);

        let mut result = vec![];
        for processed in items.executables {
            match processed {
                ProcessedItem::Entity(processed) => {
                    result.push(
                        generate_entity(&processed.entity, symtab.symtab(), &processed.type_state)
                            .report_failure(),
                    );
                }
                _ => panic!("expected an entity"),
            }
        }

        for (exp, res) in expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    }

    #[test]
    fn pipeline_instanciation_works() {
        let code = r#"
            pipeline(2) sub(clk: clk, a: int<16>) -> int<16> {
                stage {}
                stage {}
                a
            }

            entity top(clk: clk) -> int<16> {
                inst(2) sub(clk, 0)
            }
        "#;

        let expected = vec![
            entity!("sub"; (
                    "_i_clk", n(100, "clk"), Type::Bool,
                    "_i_a", n(0, "a"), Type::Int(16)
                ) -> Type::Int(16); {
                    (reg n(1, "a_s0"); Type::Int(16); clock (n(100, "clk")); n(0, "a"));
                    (reg n(2, "a_s1"); Type::Int(16); clock (n(100, "clk")); n(1, "a_s0"));
                } => n(2, "a_s1")
            ),
            entity!("top"; ("_i_clk", n(100, "clk"), Type::Bool) -> Type::Int(16); {
                (const 1; Type::Int(16); ConstantValue::Int(0));
                (e(0); Type::Int(16); Instance(("sub".to_string())); n(100, "clk"), e(1))
            } => e(0)),
        ];

        let module = parse_typecheck_module_body(code);
        let mut symtab = module.symtab;

        let mut result = vec![];
        for processed in module.items.executables {
            match processed {
                ProcessedItem::Entity(processed) => {
                    result.push(
                        generate_entity(&processed.entity, symtab.symtab(), &processed.type_state)
                            .report_failure(),
                    );
                }
                ProcessedItem::Pipeline(processed) => {
                    result.push(
                        generate_pipeline(&processed.pipeline, &processed.type_state, &mut symtab)
                            .report_failure(),
                    );
                }
            }
        }

        for (exp, res) in expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    }

    #[test]
    fn pipelines_work() {
        let code = r#"
            pipeline(3) pl(clk: clk, a: int<16>) -> int<16> {
                stage {
                    let reg x = a + a;
                }
                stage {
                    let reg y = x + a;
                }
                stage {
                    let reg res = y + y;
                }
                res
            }
        "#;

        let expected = entity!("pl"; (
                "_i_clk", n(3, "clk"), Type::Bool,
                "_i_a", n(0, "a"), Type::Int(16),
            ) -> Type::Int(16); {
                // Stage 0
                (e(0); Type::Int(16); Add; n(0, "a"), n(0, "a"));
                (n(10, "x"); Type::Int(16); Alias; e(0));
                (reg n(2, "a_s0"); Type::Int(16); clock(n(3, "clk")); n(0, "a"));
                (reg n(4, "x_s0"); Type::Int(16); clock(n(3, "clk")); n(10, "x"));

                // Stage 1
                (e(1); Type::Int(16); Add; n(4, "x_s0"), n(2, "a_s0"));
                (n(11, "y"); Type::Int(16); Alias; e(1));
                (reg n(21, "a_s1"); Type::Int(16); clock(n(3, "clk")); n(2, "a_s0"));
                (reg n(22, "x_s1"); Type::Int(16); clock(n(3, "clk")); n(4, "x_s0"));
                (reg n(23, "y_s1"); Type::Int(16); clock(n(3, "clk")); n(11, "y"));

                // Stage 3
                (e(2); Type::Int(16); Add; n(23, "y_s1"), n(23, "y_s1"));
                (n(6, "res"); Type::Int(16); Alias; e(2));
                (reg n(31, "a_s2"); Type::Int(16); clock(n(3, "clk")); n(21, "a_s1"));
                (reg n(32, "x_s2"); Type::Int(16); clock(n(3, "clk")); n(22, "x_s1"));
                (reg n(33, "y_s2"); Type::Int(16); clock(n(3, "clk")); n(23, "y_s1"));
                (reg n(34, "res_s2"); Type::Int(16); clock(n(3, "clk")); n(6, "res"));
            } => n(34, "res_s2")
        );

        let (processed, mut symbol_tracker) = parse_typecheck_pipeline(code);

        let result = generate_pipeline(
            &processed.pipeline,
            &processed.type_state,
            &mut symbol_tracker,
        )
        .report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn pipelines_returning_expressions_work() {
        let code = r#"
            pipeline(3) pl(clk: clk, a: int<16>) -> int<16> {
                stage {
                }
                stage {
                }
                stage {
                }
                a+a
            }
        "#;

        let expected = entity!("pl"; (
                "_i_clk", n(3, "clk"), Type::Bool,
                "_i_a", n(0, "a"), Type::Int(16),
            ) -> Type::Int(16); {
                // Stage 0
                (reg n(2, "a_s0"); Type::Int(16); clock(n(3, "clk")); n(0, "a"));

                // Stage 1
                (reg n(21, "a_s1"); Type::Int(16); clock(n(3, "clk")); n(2, "a_s0"));

                // Stage 3
                (reg n(31, "a_s2"); Type::Int(16); clock(n(3, "clk")); n(21, "a_s1"));

                // Output
                (e(3); Type::Int(16); Add; n(31, "a_s2"), n(31, "a_s2"));
            } => e(3)
        );

        let (processed, mut symbol_tracker) = parse_typecheck_pipeline(code);

        let result = generate_pipeline(
            &processed.pipeline,
            &processed.type_state,
            &mut symbol_tracker,
        )
        .report_failure();
        assert_same_mir!(&result, &expected);
    }

    #[ignore]
    #[test]
    fn enum_instantiation_works() {
        let code = r#"
            enum X {
                A(payload: bool),
                B
            }

            entity test(payload: bool) -> X {
                X::A(payload)
            }
        "#;

        let ParseTypececkResult { items, symtab } = parse_typecheck_module_body(code);

        let mut result = vec![];
        for processed in items.executables {
            match processed {
                ProcessedItem::Entity(processed) => {
                    result.push(
                        generate_entity(&processed.entity, symtab.symtab(), &processed.type_state)
                            .report_failure(),
                    );
                }
                _ => panic!("expected an entity"),
            }
        }

        let expected = todo!("Specify how enum instantiation should look at the MIR level");

        // for (exp, res) in expected.into_iter().zip(result.into_iter()) {
        //     assert_same_mir!(&res, &exp);
        // }
    }
}
