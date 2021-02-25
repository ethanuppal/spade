#[cfg(test)]
mod tests {
    use colored::*;
    use spade_parser::ast::*;
    use spade_parser::lexer::TokenKind;
    use spade_parser::*;

    use logos::Logos;

    use spade_common::location_info::{Loc, WithLocation};
    use spade_testutil::{ast_ident, ast_path};

    macro_rules! check_parse {
        ($string:expr , $method:ident, $expected:expr) => {
            let mut parser = Parser::new(TokenKind::lexer($string));
            let result = parser.$method();
            // This is needed because type inference fails for some unexpected reason
            let expected: Result<_> = $expected;

            if result != expected {
                println!("Parser state:\n{}", format_parse_stack(&parser.parse_stack));
                panic!(
                    "\n\n     {}: {:?}\n{}: {:?}",
                    "Got".red(),
                    result,
                    "Expected".green(),
                    expected
                );
            }
        };
    }

    #[test]
    fn parsing_identifier_works() {
        check_parse!("abc123_", identifier, Ok(ast_ident("abc123_")));
    }

    #[test]
    fn parsing_paths_works() {
        let expected = Path(vec![ast_ident("path"), ast_ident("to"), ast_ident("thing")]).nowhere();
        check_parse!("path::to::thing", path, Ok(expected));
    }

    #[test]
    fn addition_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            TokenKind::Plus,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a + b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn multiplications_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            TokenKind::Asterisk,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a * b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn multiplication_before_addition() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    TokenKind::Asterisk,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            TokenKind::Plus,
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a*b + c", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn equals_after_addition() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    TokenKind::Plus,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            TokenKind::Equals,
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a+b == c", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn and_after_equals() {
        {
            let expected_value = Expression::BinaryOperator(
                Box::new(
                    Expression::BinaryOperator(
                        Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                        TokenKind::Equals,
                        Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    )
                    .nowhere(),
                ),
                TokenKind::LogicalAnd,
                Box::new(Expression::Identifier(ast_path("c")).nowhere()),
            )
            .nowhere();

            check_parse!("a == b && c", expression, Ok(expected_value.clone()));
        }
        {
            let expected_value = Expression::BinaryOperator(
                Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                TokenKind::LogicalAnd,
                Box::new(
                    Expression::BinaryOperator(
                        Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                        TokenKind::Equals,
                        Box::new(Expression::Identifier(ast_path("c")).nowhere()),
                    )
                    .nowhere(),
                ),
            )
            .nowhere();

            check_parse!("a && b == c", expression, Ok(expected_value.clone()));
        }
    }

    #[test]
    fn bracketed_expressions_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            TokenKind::Asterisk,
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    TokenKind::Plus,
                    Box::new(Expression::Identifier(ast_path("c")).nowhere()),
                )
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!("a * (b + c)", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn repeated_bracketed_expressions_work() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    TokenKind::Plus,
                    Box::new(Expression::Identifier(ast_path("c")).nowhere()),
                )
                .nowhere(),
            ),
            TokenKind::Asterisk,
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
        )
        .nowhere();

        check_parse!("((b + c) * a)", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn literals_are_expressions() {
        check_parse!("123", expression, Ok(Expression::IntLiteral(123).nowhere()));
    }

    #[test]
    fn if_expressions_work() {
        let code = r#"
        if a {b} else {c}
        "#;

        let expected = Expression::If(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Box::new(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Expression::Identifier(ast_path("b")).nowhere(),
                }))
                .nowhere(),
            ),
            Box::new(
                Expression::Block(Box::new(Block {
                    statements: vec![],
                    result: Expression::Identifier(ast_path("c")).nowhere(),
                }))
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn blocks_work() {
        let code = r#"
            {
                let a = 0;
                1
            }
            "#;

        let expected = Block {
            statements: vec![Statement::Binding(
                ast_ident("a"),
                None,
                Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            result: Expression::IntLiteral(1).nowhere(),
        }
        .nowhere();

        check_parse!(code, block, Ok(Some(expected)));
    }

    #[test]
    fn blocks_are_expressions() {
        let code = r#"
            {
                let a = 0;
                1
            }
            "#;

        let expected = Expression::Block(Box::new(Block {
            statements: vec![Statement::Binding(
                ast_ident("a"),
                None,
                Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            result: Expression::IntLiteral(1).nowhere(),
        }))
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn bindings_work() {
        let expected = Statement::Binding(
            ast_ident("test"),
            None,
            Expression::IntLiteral(123).nowhere(),
        )
        .nowhere();
        check_parse!("let test = 123;", binding, Ok(Some(expected)));
    }

    #[test]
    fn bindings_with_types_work() {
        let expected = Statement::Binding(
            ast_ident("test"),
            Some(TypeSpec::Named(ast_path("bool"), vec![]).nowhere()),
            Expression::IntLiteral(123).nowhere(),
        )
        .nowhere();
        check_parse!("let test: bool = 123;", statement, Ok(Some(expected)));
    }

    #[test]
    fn entity_without_inputs() {
        let code = include_str!("../parser_test_code/entity_without_inputs.sp");
        let expected = Entity {
            name: Identifier("no_inputs".to_string()).nowhere(),
            inputs: vec![],
            output_type: None,
            body: Expression::Block(Box::new(Block {
                statements: vec![
                    Statement::Binding(
                        ast_ident("test"),
                        None,
                        Expression::IntLiteral(123).nowhere(),
                    )
                    .nowhere(),
                    Statement::Binding(
                        ast_ident("test2"),
                        None,
                        Expression::IntLiteral(123).nowhere(),
                    )
                    .nowhere(),
                ],
                result: Expression::Identifier(ast_path("test")).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, entity, Ok(Some(expected)));
    }

    #[test]
    fn entity_with_inputs() {
        let code = include_str!("../parser_test_code/entity_with_inputs.sp");
        let expected = Entity {
            name: ast_ident("with_inputs"),
            inputs: vec![
                (
                    Identifier("clk".to_string()).nowhere(),
                    TypeSpec::Named(ast_path("bool"), vec![]).nowhere(),
                ),
                (
                    Identifier("rst".to_string()).nowhere(),
                    TypeSpec::Named(ast_path("bool"), vec![]).nowhere(),
                ),
            ],
            output_type: Some(TypeSpec::Named(ast_path("bool"), vec![]).nowhere()),
            body: Expression::Block(Box::new(Block {
                statements: vec![],
                result: Expression::Identifier(ast_path("clk")).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, entity, Ok(Some(expected)));
    }

    #[test]
    fn entity_with_generics() {
        let code = include_str!("../parser_test_code/entity_with_generics.sp");
        let expected = Entity {
            name: ast_ident("with_generics"),
            inputs: vec![],
            output_type: None,
            body: Expression::Block(Box::new(Block {
                statements: vec![],
                result: Expression::Identifier(ast_path("clk")).nowhere(),
            }))
            .nowhere(),
            type_params: vec![
                TypeParam::TypeName(ast_ident("X").inner).nowhere(),
                TypeParam::Integer(ast_ident("Y")).nowhere(),
            ],
        }
        .nowhere();

        check_parse!(code, entity, Ok(Some(expected)));
    }

    #[test]
    fn parsing_register_without_reset_works() {
        let code = "reg(clk) name = 1;";

        let expected = Statement::Register(
            Register {
                name: ast_ident("name"),
                clock: Expression::Identifier(ast_path("clk")).nowhere(),
                reset: None,
                value: Expression::IntLiteral(1).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, statement, Ok(Some(expected)));
    }

    #[test]
    fn parsing_register_with_reset_works() {
        let code = "reg(clk) name reset (rst: 0) = 1;";

        let expected = Statement::Register(
            Register {
                name: ast_ident("name"),
                clock: Expression::Identifier(ast_path("clk")).nowhere(),
                reset: Some((
                    Expression::Identifier(ast_path("rst")).nowhere(),
                    Expression::IntLiteral(0).nowhere(),
                )),
                value: Expression::IntLiteral(1).nowhere(),
                value_type: None,
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, statement, Ok(Some(expected)));
    }

    #[test]
    fn parsing_register_with_reset_and_clock() {
        let code = "reg(clk) name: Type reset (rst: 0) = 1;";

        let expected = Statement::Register(
            Register {
                name: Identifier("name".to_string()).nowhere(),
                clock: Expression::Identifier(ast_path("clk")).nowhere(),
                reset: Some((
                    Expression::Identifier(ast_path("rst")).nowhere(),
                    Expression::IntLiteral(0).nowhere(),
                )),
                value: Expression::IntLiteral(1).nowhere(),
                value_type: Some(TypeSpec::Named(ast_path("Type"), vec![]).nowhere()),
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, statement, Ok(Some(expected)));
    }

    #[test]
    fn size_types_work() {
        let expected = TypeSpec::Named(
            ast_path("uint"),
            vec![TypeExpression::Integer(10).nowhere()],
        )
        .nowhere();
        check_parse!("uint<10>", type_spec, Ok(expected));
    }

    #[test]
    fn module_body_parsing_works() {
        let code = include_str!("../parser_test_code/multiple_entities.sp");

        let e1 = Entity {
            name: Identifier("e1".to_string()).nowhere(),
            inputs: vec![],
            output_type: None,
            body: Expression::Block(Box::new(Block {
                statements: vec![],
                result: Expression::IntLiteral(0).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        let e2 = Entity {
            name: Identifier("e2".to_string()).nowhere(),
            inputs: vec![],
            output_type: None,
            body: Expression::Block(Box::new(Block {
                statements: vec![],
                result: Expression::IntLiteral(1).nowhere(),
            }))
            .nowhere(),
            type_params: vec![],
        }
        .nowhere();

        let expected = ModuleBody {
            members: vec![Item::Entity(e1), Item::Entity(e2)],
        };

        check_parse!(code, module_body, Ok(expected));
    }

    #[test]
    fn function_declarations_work() {
        let code = "fn some_fn(self, a: bit) -> bit;";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: vec![(
                ast_ident("a"),
                TypeSpec::Named(ast_path("bit"), vec![]).nowhere(),
            )],
            return_type: Some(TypeSpec::Named(ast_path("bit"), vec![]).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, function_decl, Ok(Some(expected)));
    }

    #[test]
    fn function_declarations_with_only_self_arg_work() {
        let code = "fn some_fn(self) -> bit;";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: vec![],
            return_type: Some(TypeSpec::Named(ast_path("bit"), vec![]).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, function_decl, Ok(Some(expected)));
    }

    #[test]
    fn function_declarations_with_no_type_have_unit_type() {
        let code = "fn some_fn(self);";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: vec![],
            return_type: None,
            type_params: vec![],
        }
        .nowhere();

        check_parse!(code, function_decl, Ok(Some(expected)));
    }

    #[test]
    fn function_decls_with_generic_type_works() {
        let code = "fn some_fn<X>(self);";

        let expected = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: vec![],
            return_type: None,
            type_params: vec![TypeParam::TypeName(ast_ident("X").inner).nowhere()],
        }
        .nowhere();

        check_parse!(code, function_decl, Ok(Some(expected)));
    }

    #[test]
    fn trait_definitions_work() {
        let code = r#"
        trait SomeTrait {
            fn some_fn(self, a: bit) -> bit;
            fn another_fn(self) -> bit;
        }
        "#;

        let fn1 = FunctionDecl {
            name: ast_ident("some_fn"),
            self_arg: Some(().nowhere()),
            inputs: vec![(
                ast_ident("a"),
                TypeSpec::Named(ast_path("bit"), vec![]).nowhere(),
            )],
            return_type: Some(TypeSpec::Named(ast_path("bit"), vec![]).nowhere()),
            type_params: vec![],
        }
        .nowhere();
        let fn2 = FunctionDecl {
            name: ast_ident("another_fn"),
            self_arg: Some(().nowhere()),
            inputs: vec![],
            return_type: Some(TypeSpec::Named(ast_path("bit"), vec![]).nowhere()),
            type_params: vec![],
        }
        .nowhere();

        let expected = TraitDef {
            name: ast_ident("SomeTrait"),
            functions: vec![fn1, fn2],
        }
        .nowhere();

        check_parse!(code, trait_def, Ok(Some(expected)));
    }

    #[test]
    fn typenames_parse() {
        let code = "X";

        let expected = TypeParam::TypeName(ast_ident("X").inner).nowhere();

        check_parse!(code, type_param, Ok(expected));
    }

    #[test]
    fn typeints_parse() {
        let code = "#X";

        let expected = TypeParam::Integer(ast_ident("X")).nowhere();

        check_parse!(code, type_param, Ok(expected));
    }

    #[test]
    fn tuple_literals_parse() {
        let code = "(1, true)";

        let expected = Expression::TupleLiteral(vec![
            Expression::IntLiteral(1).nowhere(),
            Expression::BoolLiteral(true).nowhere(),
        ])
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_indexing_parsese() {
        let code = "a#0";

        let expected = Expression::TupleIndex(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Loc::new(0, ().nowhere().span),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_type_specs_work() {
        let code = "(int, bool)";

        let expected = TypeSpec::Tuple(vec![
            TypeSpec::Named(ast_path("int"), vec![]).nowhere(),
            TypeSpec::Named(ast_path("bool"), vec![]).nowhere(),
        ])
        .nowhere();

        check_parse!(code, type_spec, Ok(expected));
    }
}
