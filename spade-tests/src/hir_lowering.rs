#[cfg(test)]
mod tests {
    use crate::{build_and_compare_entities, build_entity, build_items, ResultExt};
    use colored::Colorize;
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
    fn bitwise_and_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a & b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Int(16); {
                (e(0); Type::Int(16); BitwiseAnd; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn xor_operator_codegens_correctly() {
        let code = r#"
        entity name(a: bool, b: bool) -> bool {
            a ^ b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Bool,
                "_i_b", n(1, "b"), Type::Bool
            ) -> Type::Bool; {
                (e(0); Type::Bool; Xor; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn bitwise_or_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> int<16> {
            a | b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Int(16); {
                (e(0); Type::Int(16); BitwiseOr; n(0, "a"), n(1, "b"))
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
    fn greater_than_or_equals_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a >= b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Ge; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn less_than_or_equals_operator_codegens_correctly() {
        let code = r#"
        entity name(a: int<16>, b: int<16>) -> bool {
            a <= b
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(16)
            ) -> Type::Bool; {
                (e(0); Type::Bool; Le; n(0, "a"), n(1, "b"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn usub_codegens_corectly() {
        let code = r#"
        entity name(a: int<16>) -> int<16> {
            -a
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
            ) -> Type::Int(16); {
                (e(0); Type::Int(16); USub; n(0, "a"))
            } => e(0)
        );

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn not_codegens_corectly() {
        let code = r#"
        entity name(a: bool) -> bool {
            !a
        }
        "#;

        let expected = entity!("name"; (
                "_i_a", n(0, "a"), Type::Bool,
            ) -> Type::Bool; {
                (e(0); Type::Bool; Not; n(0, "a"))
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
    fn registers_with_tuple_patterns_work() {
        let code = r#"
        entity name(clk: clk, a: (int<16>, int<8>)) -> int<16> {
            reg(clk) (x, y) = a;
            x
        }
        "#;

        let tup_inner = vec![Type::Int(16), Type::Int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = entity! {"name"; (
                "_i_clk", n(0, "clk"), Type::Bool,
                "_i_a", n(1, "a"), tup_type.clone(),
            ) -> Type::Int(16); {
                (reg e(0); tup_type; clock(n(0, "clk")); n(1, "a"));
                (n(2, "x"); Type::Int(16); IndexTuple((0, tup_inner.clone())); e(0));
                (n(3, "y"); Type::Int(8); IndexTuple((1, tup_inner)); e(0));
            } => n(2, "x")
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
    fn array_literals_work() {
        let code = r#"
            entity x() -> [int<2>; 3] {
                [0, 1, 2]
            }
        "#;

        let array_type = Type::Array {
            inner: Box::new(Type::Int(2)),
            length: 3,
        };

        let expected = entity!("x"; () -> array_type.clone(); {
            (const 0; Type::Int(2); ConstantValue::Int(0));
            (const 1; Type::Int(2); ConstantValue::Int(1));
            (const 2; Type::Int(2); ConstantValue::Int(2));
            (e(4); array_type.clone(); ConstructArray; e(0), e(1), e(2));
        } => e(4));

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn array_indexing_works() {
        let code = r#"
            entity x(a: [int<2>; 3]) -> int<2> {
                let idx: int<8> = 2;
                a[idx]
            }
        "#;

        let array_type = Type::Array {
            inner: Box::new(Type::Int(2)),
            length: 3,
        };

        let expected = entity!("x"; (
                "_i_a", n(0, "a"), array_type.clone(),
        ) -> Type::Int(2); {
            (const 0; Type::Int(8); ConstantValue::Int(2));
            (n(1, "idx"); Type::Int(8); Alias; e(0));
            (e(4); Type::Int(2); IndexArray((2)); n(0, "a"), n(1, "idx"));
        } => e(4));

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
    fn tuple_destructuring_works() {
        let code = r#"
        entity name(x: (int<16>, int<8>)) -> int<16> {
            let (a, b) = x;
            a
        }
        "#;

        let tup_inner = vec![Type::Int(16), Type::Int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = entity!("name"; (
                "_i_x", n(0, "x"), tup_type.clone(),
            ) -> Type::Int(16); {
                // NOTE: This line techinically isn't required in this case as it is just an alias,
                // but removing it seems a bit pointless as it would introduce a special case in
                // the code
                (e(0); tup_type; Alias; n(0, "x"));
                (n(1, "a"); Type::Int(16); IndexTuple((0, tup_inner.clone())); n(0, "x"));
                (n(2, "b"); Type::Int(8); IndexTuple((1, tup_inner)); n(0, "x"))
            } => n(1, "a")
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

        let mut expected = vec![
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

        let ParseTypececkResult {
            items_with_types,
            item_list,
            mut idtracker,
            mut symtab,
        } = parse_typecheck_module_body(code);

        let mut result = vec![];
        for processed in items_with_types.executables {
            match processed {
                ProcessedItem::Entity(processed) => {
                    result.push(
                        generate_entity(
                            &processed.entity,
                            &mut symtab,
                            &mut idtracker,
                            &processed.type_state,
                            &item_list,
                        )
                        .report_failure(code),
                    );
                }
                _ => panic!("expected an entity"),
            }
        }

        expected.sort_by_key(|e| e.name.clone());
        result.sort_by_key(|e| e.name.clone());

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

        let mut expected = vec![
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
        let mut idtracker = module.idtracker;

        let mut result = vec![];
        for processed in module.items_with_types.executables {
            match processed {
                ProcessedItem::Entity(processed) => {
                    result.push(
                        generate_entity(
                            &processed.entity,
                            &mut symtab,
                            &mut idtracker,
                            &processed.type_state,
                            &module.item_list,
                        )
                        .report_failure(code),
                    );
                }
                ProcessedItem::Pipeline(processed) => {
                    result.push(
                        generate_pipeline(
                            &processed.pipeline,
                            &processed.type_state,
                            &mut symtab,
                            &mut idtracker,
                            &module.item_list,
                        )
                        .report_failure(code),
                    );
                }
                ProcessedItem::EnumInstance => {}
                ProcessedItem::StructInstance => {}
            }
        }

        expected.sort_by_key(|e| e.name.clone());
        result.sort_by_key(|e| e.name.clone());

        for (exp, res) in expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    }

    #[test]
    fn pipelines_work() {
        let code = r#"
            pipeline(3) pl(clk: clk, a: int<16>) -> int<16> {
                stage {
                    let x = a + a;
                }
                stage {
                    let y = x + a;
                }
                stage {
                    let res = y + y;
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

        let (processed, mut symbol_tracker, mut idtracker, type_list) =
            parse_typecheck_pipeline(code);

        let result = generate_pipeline(
            &processed.pipeline,
            &processed.type_state,
            &mut symbol_tracker,
            &mut idtracker,
            &type_list,
        )
        .report_failure(code);
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

        let (processed, mut symbol_tracker, mut idtracker, type_list) =
            parse_typecheck_pipeline(code);

        let result = generate_pipeline(
            &processed.pipeline,
            &processed.type_state,
            &mut symbol_tracker,
            &mut idtracker,
            &type_list,
        )
        .report_failure(code);
        assert_same_mir!(&result, &expected);
    }

    #[test]
    fn struct_instantiation_works() {
        let code = r#"
            struct X (payload: bool)

            entity test(payload: bool) -> X {
                X$(payload)
            }
        "#;

        let mir_struct = Type::Tuple(vec![Type::Bool]);

        let expected = vec![entity!("test"; (
                "_i_payload", n(0, "payload"), Type::Bool,
            ) -> mir_struct.clone(); {
                (e(1); mir_struct; ConstructTuple; n(0, "payload"));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn struct_field_access_and_creation_works() {
        let code = r#"
        struct X (a: int<16>, b: int<8>)

        entity name(a: int<16>, b: int<8>) -> int<8> {
            let compound = X$(a, b);
            compound.b
        }
        "#;

        let tup_inner = vec![Type::Int(16), Type::Int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = vec![entity!("name"; (
                "_i_a", n(0, "a"), Type::Int(16),
                "_i_b", n(1, "b"), Type::Int(8),
            ) -> Type::Int(8); {
                (e(1); tup_type.clone(); ConstructTuple; n(0, "a"), n(1, "b"));
                (n(2, "compound"); tup_type; Alias; e(1));
                (e(0); Type::Int(8); IndexTuple((1, tup_inner)); n(2, "compound"));
            } => e(0)
        )];

        build_and_compare_entities!(code, &expected);
    }

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

        let mir_enum = Type::Enum(vec![vec![Type::Bool], vec![]]);

        let expected = vec![entity!("test"; (
                "_i_payload", n(0, "payload"), Type::Bool,
            ) -> mir_enum.clone(); {
                (e(1); mir_enum; ConstructEnum({variant: 0, variant_count: 2}); n(0, "payload"));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn enum_instantiation_with_subexpression_works() {
        let code = r#"
            enum X {
                A(payload: int<16>),
                B
            }

            entity test(payload: int<16>) -> X {
                X::A(payload + 1)
            }
        "#;

        let mir_enum = Type::Enum(vec![vec![Type::Int(16)], vec![]]);

        let expected = vec![entity!("test"; (
                "_i_payload", n(0, "payload"), Type::Int(16),
            ) -> mir_enum.clone(); {
                (const 3; Type::Int(16); ConstantValue::Int(1));
                (e(2); Type::Int(16); Add; n(0, "payload"), e(3));
                (e(1); mir_enum; ConstructEnum({variant: 0, variant_count: 2}); e(2));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn enum_instantiation_with_fixed_generics_works() {
        let code = r#"
            enum X {
                A(payload: int<5>),
                B
            }

            entity test(payload: int<5>) -> X {
                X::A(payload)
            }
        "#;

        let mir_enum = Type::Enum(vec![vec![Type::Int(5)], vec![]]);

        let expected = vec![entity!("test"; (
                "_i_payload", n(0, "payload"), Type::Int(5),
            ) -> mir_enum.clone(); {
                (e(1); mir_enum; ConstructEnum({variant: 0, variant_count: 2}); n(0, "payload"));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn enum_instantiation_with_full_generics_works() {
        let code = r#"
            enum Option<T> {
                Some(payload: T),
                None
            }

            entity test(payload: int<5>) -> Option<int<5>> {
                Option::Some(payload)
            }
        "#;

        let mir_enum = Type::Enum(vec![vec![Type::Int(5)], vec![]]);

        let expected = vec![entity!("test"; (
                "_i_payload", n(0, "payload"), Type::Int(5),
            ) -> mir_enum.clone(); {
                (e(1); mir_enum; ConstructEnum({variant: 0, variant_count: 2}); n(0, "payload"));
            } => e(1)
        )];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn enum_match_works() {
        let code = r#"
            enum Option<T> {
                Some(payload: T),
                None
            }

            entity unwrap_or_0(e: Option<int<16>>) -> int<16> {
                match e {
                    Option::Some(x) => x,
                    other => 0
                }
            }
        "#;

        let mir_type = Type::Enum(vec![vec![Type::Int(16)], vec![]]);

        let expected = vec![
            entity! {"unwrap_or_0"; ("_i_e", n(0, "e"), mir_type.clone()) -> Type::Int(16); {
                // Conditions for branches
                (n(1, "x"); Type::Int(16); EnumMember({variant: 0, member_index: 0, enum_type: mir_type.clone()}); n(0, "e"));
                (e(2); Type::Bool; IsEnumVariant({variant: 0, enum_type: mir_type.clone()}); n(0, "e"));
                (const 3; Type::Bool; ConstantValue::Bool(true));
                (const 5; Type::Int(16); ConstantValue::Int(0));
                (e(6); Type::Int(16); Match; e(2), n(1, "x"), e(3), e(5));
            } => e(6)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn boolean_patterns_work() {
        let code = r#"
            entity uwu(e: bool) -> bool {
                match e {
                    true => false,
                    false => true
                }
            }
        "#;

        let expected = vec![
            entity! {"uwu"; ("_i_e", n(0, "e"), Type::Bool) -> Type::Bool; {
                // Conditions for branches
                (const 3; Type::Bool; ConstantValue::Bool(false));
                (e(2); Type::Bool; LogicalNot; n(0, "e"));
                (const 4; Type::Bool; ConstantValue::Bool(true));
                (e(6); Type::Bool; Match; n(0, "e"), e(3), e(2), e(4));
            } => e(6)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn integer_patterns_work() {
        let code = r#"
            entity uwu(e: int<16>) -> bool {
                match e {
                    0 => true,
                }
            }
        "#;

        let expected = vec![
            entity! {"uwu"; ("_i_e", n(0, "e"), Type::Int(16)) -> Type::Bool; {
                // Conditions for branches
                (const 1; Type::Int(16); ConstantValue::Int(0));
                (e(2); Type::Bool; Eq; n(0, "e"), e(1));
                (const 4; Type::Bool; ConstantValue::Bool(true));
                (e(6); Type::Bool; Match; e(2), e(4));
            } => e(6)},
        ];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn tuple_patterns_conditions_work() {
        let code = r#"
            entity name(a: (bool, bool)) -> int<16> {
                match a {
                    (true, true) => 0,
                    (false, true) => 1,
                }
            }
        "#;

        let tup_inner = vec![Type::Bool, Type::Bool];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = entity! {"name"; (
                "_i_a", n(0, "a"), tup_type.clone()
            ) -> Type::Int(16); {
                (e(0); Type::Bool; IndexTuple((0, tup_inner.clone())); n(0, "a"));
                (e(1); Type::Bool; IndexTuple((1, tup_inner.clone())); n(0, "a"));
                (e(3); Type::Bool; LogicalAnd; e(0), e(1));
                (const 10; Type::Int(16); ConstantValue::Int(0));
                (e(20); Type::Bool; IndexTuple((0, tup_inner.clone())); n(0, "a"));
                (e(21); Type::Bool; IndexTuple((1, tup_inner)); n(0, "a"));
                (e(4); Type::Bool; LogicalNot; e(20));
                (e(5); Type::Bool; LogicalAnd; e(4), e(21));
                (const 11; Type::Int(16); ConstantValue::Int(1));
                // Condition for branch 1
                (e(6); Type::Int(16); Match; e(3), e(10), e(5), e(11))
            } => e(6)
        };

        assert_same_mir!(&build_entity!(code), &expected);
    }

    #[test]
    fn registers_with_struct_patterns_work() {
        let code = r#"
        struct X(a: int<16>, b: int<8>)

        entity name(clk: clk, a: X) -> int<16> {
            reg(clk) X(x, y) = a;
            x
        }
        "#;

        let tup_inner = vec![Type::Int(16), Type::Int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = vec![entity! {"name"; (
                "_i_clk", n(0, "clk"), Type::Bool,
                "_i_a", n(1, "a"), tup_type.clone(),
            ) -> Type::Int(16); {
                (reg e(0); tup_type; clock(n(0, "clk")); n(1, "a"));
                (n(2, "x"); Type::Int(16); IndexTuple((0, tup_inner.clone())); e(0));
                (n(3, "y"); Type::Int(8); IndexTuple((1, tup_inner)); e(0));
            } => n(2, "x")
        }];

        build_and_compare_entities!(code, expected);
    }

    #[test]
    fn registers_with_struct_patterns_with_named_bindings_work() {
        let code = r#"
        struct X(a: int<16>, b: int<8>)

        entity name(clk: clk, a: X) -> int<16> {
            reg(clk) X$(b: y, a: x) = a;
            x
        }
        "#;

        let tup_inner = vec![Type::Int(16), Type::Int(8)];
        let tup_type = Type::Tuple(tup_inner.clone());
        let expected = vec![entity! {"name"; (
                "_i_clk", n(0, "clk"), Type::Bool,
                "_i_a", n(1, "a"), tup_type.clone(),
            ) -> Type::Int(16); {
                (reg e(0); tup_type; clock(n(0, "clk")); n(1, "a"));
                (n(2, "x"); Type::Int(16); IndexTuple((0, tup_inner.clone())); e(0));
                (n(3, "y"); Type::Int(8); IndexTuple((1, tup_inner)); e(0));
            } => n(2, "x")
        }];

        build_and_compare_entities!(code, expected);
    }
}
