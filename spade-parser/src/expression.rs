use parse_tree_macros::trace_parser;
use spade_ast::{ArgumentList, BinaryOperator, Expression, UnaryOperator};
use spade_common::location_info::{lspan, Loc, WithLocation};

use crate::error::{Error, Result};
use crate::{lexer::TokenKind, ParseStackEntry, Parser};

macro_rules! operator_expr {
    ($this_operator:ident, $condition:ident, $next:ident $(,)?) => {
        fn $this_operator(&mut self) -> Result<Loc<Expression>> {
            self.binary_operator(Self::$next, Self::$condition, Self::$this_operator)
        }
    };
}

impl<'a> Parser<'a> {
    pub fn operator_from_kind(kind: TokenKind) -> BinaryOperator {
        match kind {
            TokenKind::Plus => BinaryOperator::Add,
            TokenKind::Minus => BinaryOperator::Sub,
            TokenKind::Asterisk => BinaryOperator::Mul,
            TokenKind::Equals => BinaryOperator::Equals,
            // We have to handle left and right shifts separately because otherwise
            // their parsing interferes with generic arguments
            TokenKind::Lt => BinaryOperator::Lt,
            TokenKind::Gt => BinaryOperator::Gt,
            TokenKind::Le => BinaryOperator::Le,
            TokenKind::Ge => BinaryOperator::Ge,
            TokenKind::RightShift => BinaryOperator::RightShift,
            TokenKind::LeftShift => BinaryOperator::LeftShift,
            TokenKind::LogicalOr => BinaryOperator::LogicalOr,
            TokenKind::LogicalAnd => BinaryOperator::LogicalAnd,
            TokenKind::BitwiseAnd => BinaryOperator::BitwiseAnd,
            TokenKind::BitwiseOr => BinaryOperator::BitwiseOr,
            TokenKind::Xor => BinaryOperator::Xor,
            x => unreachable!("{:?} ({}) is not an operator", x, x.as_str()),
        }
    }

    pub fn binary_operator(
        &mut self,
        lhs: impl Fn(&mut Self) -> Result<Loc<Expression>>,
        condition: impl Fn(&mut Self) -> Result<bool>,
        rhs: impl Fn(&mut Self) -> Result<Loc<Expression>>,
    ) -> Result<Loc<Expression>> {
        let start = lhs(self)?;

        if condition(self)? {
            let operator = self.eat_unconditional()?;
            let rest = rhs(self)?;

            let span = start.span.merge(rest.span);

            let op = Self::operator_from_kind(operator.kind);
            Ok(
                Expression::BinaryOperator(Box::new(start), op, Box::new(rest))
                    .at(self.file_id, &span),
            )
        } else {
            Ok(start)
        }
    }

    pub fn unary_operator(&mut self) -> Result<Option<Loc<Expression>>> {
        let operator = self.peek()?.and_then(|t| match t.kind {
            TokenKind::Minus => Some(UnaryOperator::Sub.at(self.file_id, &t.span)),
            TokenKind::Not => Some(UnaryOperator::Not.at(self.file_id, &t.span)),
            TokenKind::BitwiseNot => Some(UnaryOperator::BitwiseNot.at(self.file_id, &t.span)),
            _ => None,
        });

        Ok(match operator {
            Some(op) => {
                self.eat_unconditional()?;
                let expr = self.expression()?;
                Some(
                    Expression::UnaryOperator(op.inner.clone(), Box::new(expr.clone())).between(
                        self.file_id,
                        &op,
                        &expr,
                    ),
                )
            }
            None => None,
        })
    }

    // Expression parsing
    #[trace_parser]
    pub fn expression(&mut self) -> Result<Loc<Expression>> {
        self.custom_infix_operator(Self::logical_or_expression)
    }

    pub fn custom_infix_operator(
        &mut self,
        lhs: impl Fn(&mut Self) -> Result<Loc<Expression>>,
    ) -> Result<Loc<Expression>> {
        let lhs_val = lhs(self)?;

        if self.peek_kind(&TokenKind::InfixOperatorSeparator)? {
            let (name, _) = self.surrounded(
                &TokenKind::InfixOperatorSeparator,
                Self::path,
                &TokenKind::InfixOperatorSeparator,
            )?;

            let rhs_val = self.custom_infix_operator(lhs)?;

            Ok(Expression::FnCall(
                name,
                ArgumentList::Positional(vec![lhs_val.clone(), rhs_val.clone()]).between(
                    self.file_id,
                    &lhs_val,
                    &rhs_val,
                ),
            )
            .between(self.file_id, &lhs_val, &rhs_val))
        } else {
            Ok(lhs_val)
        }
    }

    operator_expr!(
        logical_or_expression,
        is_next_logical_or,
        logical_and_expression,
    );
    operator_expr!(
        logical_and_expression,
        is_next_logical_and,
        bitwise_or_expression,
    );
    operator_expr!(bitwise_or_expression, is_next_bitwise_or, xor_expression,);
    operator_expr!(xor_expression, is_next_xor, bitwise_and_expression,);
    operator_expr!(
        bitwise_and_expression,
        is_next_bitwise_and,
        comparison_operator,
    );
    operator_expr!(
        comparison_operator,
        is_next_comparison_operator,
        shift_expression,
    );
    operator_expr!(
        shift_expression,
        is_next_shift_operator,
        additive_expression,
    );
    operator_expr!(
        additive_expression,
        is_next_addition_operator,
        multiplicative_expression,
    );
    operator_expr!(
        multiplicative_expression,
        is_next_multiplication_operator,
        base_expression
    );

    #[trace_parser]
    pub fn base_expression(&mut self) -> Result<Loc<Expression>> {
        let expr = if let Some(tuple) = self.tuple_literal()? {
            Ok(tuple)
        } else if let Some(array) = self.array_literal()? {
            Ok(array)
        } else if let Some(instance) = self.entity_instance()? {
            Ok(instance)
        } else if let Some(val) = self.bool_literal()? {
            Ok(val.map(Expression::BoolLiteral))
        } else if let Some(val) = self.int_literal()? {
            Ok(val.map(Expression::IntLiteral))
        } else if let Some(block) = self.block(false)? {
            Ok(block.map(Box::new).map(Expression::Block))
        } else if let Some(if_expr) = self.if_expression()? {
            Ok(if_expr)
        } else if let Some(match_expr) = self.match_expression()? {
            Ok(match_expr)
        } else if let Some(operator) = self.unary_operator()? {
            Ok(operator)
        } else if let Some(stageref) = self.pipeline_reference()? {
            Ok(stageref)
        } else {
            match self.path() {
                Ok(path) => {
                    let span = path.span;
                    // Check if this is a function call by looking for an argument list
                    if let Some(args) = self.argument_list()? {
                        // Doing this avoids cloning result and args
                        let span = ().between(self.file_id, &path, &args);

                        Ok(Expression::FnCall(path, args).at_loc(&span))
                    } else {
                        Ok(Expression::Identifier(path).at(self.file_id, &span))
                    }
                }
                Err(Error::UnexpectedToken { got, .. }) => Err(Error::ExpectedExpression { got }),
                Err(e) => Err(e),
            }
        }?;

        self.expression_suffix(expr)
    }

    #[trace_parser]
    fn expression_suffix(&mut self, expr: Loc<Expression>) -> Result<Loc<Expression>> {
        let base = if let Some(hash) = self.peek_and_eat(&TokenKind::Hash)? {
            if let Some(index) = self.int_literal()? {
                let span = expr.span.merge(lspan(hash.span));
                Ok(Expression::TupleIndex(Box::new(expr), index).at(self.file_id, &span))
            } else {
                Err(Error::MissingTupleIndex {
                    hash_loc: Loc::new((), lspan(hash.span), self.file_id),
                })
            }
        } else if let Some(_) = self.peek_and_eat(&TokenKind::Dot)? {
            let field = self.identifier()?;

            Ok(
                Expression::FieldAccess(Box::new(expr.clone()), field.clone()).between(
                    self.file_id,
                    &expr,
                    &field,
                ),
            )
        } else if self.peek_kind(&TokenKind::OpenBracket)? {
            let (index, _) = self.surrounded(
                &TokenKind::OpenBracket,
                Self::expression,
                &TokenKind::CloseBracket,
            )?;

            Ok(
                Expression::Index(Box::new(expr.clone()), Box::new(index.clone())).between(
                    self.file_id,
                    &expr,
                    &index,
                ),
            )
        } else {
            return Ok(expr);
        }?;

        self.expression_suffix(base)
    }
}

#[cfg(test)]
mod test {
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_ast::*;

    use super::*;
    use crate::lexer::TokenKind;
    use crate::{check_parse, format_parse_stack};

    use colored::Colorize;
    use logos::Logos;

    use spade_common::location_info::WithLocation;

    #[test]
    fn addition_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::Add,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a + b", expression, Ok(expected_value.clone()));
    }

    #[ignore]
    #[test]
    fn subtraction_occurs_in_correct_order() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                    BinaryOperator::Sub,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Sub,
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a - b - c", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn unary_suptraction_works() {
        let expected_value = Expression::UnaryOperator(
            UnaryOperator::Sub,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("- b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn not_operator_works() {
        let expected_value = Expression::UnaryOperator(
            UnaryOperator::Not,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("!b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn bitwise_and_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::BitwiseAnd,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a & b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn bitwise_or_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::BitwiseOr,
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a | b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn multiplications_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            BinaryOperator::Mul,
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
                    BinaryOperator::Mul,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Add,
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
                    BinaryOperator::Add,
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Equals,
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
                        BinaryOperator::Equals,
                        Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    )
                    .nowhere(),
                ),
                BinaryOperator::LogicalAnd,
                Box::new(Expression::Identifier(ast_path("c")).nowhere()),
            )
            .nowhere();

            check_parse!("a == b && c", expression, Ok(expected_value.clone()));
        }
        {
            let expected_value = Expression::BinaryOperator(
                Box::new(Expression::Identifier(ast_path("a")).nowhere()),
                BinaryOperator::LogicalAnd,
                Box::new(
                    Expression::BinaryOperator(
                        Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                        BinaryOperator::Equals,
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
            BinaryOperator::Add,
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    BinaryOperator::Add,
                    Box::new(Expression::Identifier(ast_path("c")).nowhere()),
                )
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!("a + (b + c)", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn repeated_bracketed_expressions_work() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(ast_path("b")).nowhere()),
                    BinaryOperator::Add,
                    Box::new(Expression::Identifier(ast_path("c")).nowhere()),
                )
                .nowhere(),
            ),
            BinaryOperator::Add,
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
        )
        .nowhere();

        check_parse!("((b + c) + a)", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn functions_work() {
        let code = "test(1, 2)";

        let expected = Expression::FnCall(
            ast_path("test"),
            ArgumentList::Positional(vec![
                Expression::IntLiteral(1).nowhere(),
                Expression::IntLiteral(2).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn functions_with_named_arguments_work() {
        let code = "test$(a, b)";

        let expected = Expression::FnCall(
            ast_path("test"),
            ArgumentList::Named(vec![
                NamedArgument::Short(ast_ident("a")),
                NamedArgument::Short(ast_ident("b")),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
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
    fn array_literals_parse() {
        let code = "[1, 2, 3]";

        let expected = Expression::ArrayLiteral(vec![
            Expression::IntLiteral(1).nowhere(),
            Expression::IntLiteral(2).nowhere(),
            Expression::IntLiteral(3).nowhere(),
        ])
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn array_indexing_works() {
        let code = "a[0]";

        let expected = Expression::Index(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Box::new(Expression::IntLiteral(0).nowhere()),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_indexing_parsese() {
        let code = "a#0";

        let expected = Expression::TupleIndex(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Loc::new(0, ().nowhere().span, 0),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn field_access_parses() {
        let code = "a.b";
        let expected = Expression::FieldAccess(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            ast_ident("b"),
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
    fn if_expressions_do_not_require_blocks() {
        let code = r#"
        if a b else c
        "#;

        let expected = Expression::If(
            Box::new(Expression::Identifier(ast_path("a")).nowhere()),
            Box::new(Expression::Identifier(ast_path("b")).nowhere()),
            Box::new(Expression::Identifier(ast_path("c")).nowhere()),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn match_expressions_work() {
        let code = r#"
        match x {
            (0, y) => y,
            (x, y) => x,
        }
        "#;

        let expected = Expression::Match(
            Box::new(Expression::Identifier(ast_path("x")).nowhere()),
            vec![
                (
                    Pattern::Tuple(vec![Pattern::Integer(0).nowhere(), Pattern::name("y")])
                        .nowhere(),
                    Expression::Identifier(ast_path("y")).nowhere(),
                ),
                (
                    Pattern::Tuple(vec![Pattern::name("x"), Pattern::name("y")]).nowhere(),
                    Expression::Identifier(ast_path("x")).nowhere(),
                ),
            ],
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
                Pattern::name("a"),
                None,
                Expression::IntLiteral(0).nowhere(),
            )
            .nowhere()],
            result: Expression::IntLiteral(1).nowhere(),
        }
        .nowhere();

        check_parse!(code, block(false), Ok(Some(expected)));
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
                Pattern::name("a"),
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
    fn infix_operators_work() {
        let code = r#"
            1 `infix` 2
            "#;

        let expected = Expression::FnCall(
            ast_path("infix"),
            ArgumentList::Positional(vec![
                Expression::IntLiteral(1).nowhere(),
                Expression::IntLiteral(2).nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn infix_operator_precedence_is_unchanged() {
        // NOTE: the exact ordering here is somewhat unimportant, in general one
        // should probably put parentheses around infix operators anyway. The main
        // purpose of this test is to prevent accidental changes to the order in the future
        let code = r#"
            0 || 1 `infix` 2 `infix` 3
            "#;

        let expected = Expression::FnCall(
            ast_path("infix"),
            ArgumentList::Positional(vec![
                Expression::BinaryOperator(
                    Box::new(Expression::IntLiteral(0).nowhere()),
                    BinaryOperator::LogicalOr,
                    Box::new(Expression::IntLiteral(1).nowhere()),
                )
                .nowhere(),
                Expression::FnCall(
                    ast_path("infix"),
                    ArgumentList::Positional(vec![
                        Expression::IntLiteral(2).nowhere(),
                        Expression::IntLiteral(3).nowhere(),
                    ])
                    .nowhere(),
                )
                .nowhere(),
            ])
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn field_access_operator_does_not_require_parens() {
        let code = r#"x.y.z"#;

        let expected = Expression::FieldAccess(
            Box::new(
                Expression::FieldAccess(
                    Box::new(Expression::Identifier(ast_path("x")).nowhere()),
                    ast_ident("y"),
                )
                .nowhere(),
            ),
            ast_ident("z"),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn array_index_operator_precedence_is_correct() {
        let code = r#"x && y[z]"#;

        let expected = Expression::BinaryOperator(
            Box::new(Expression::Identifier(ast_path("x")).nowhere()),
            BinaryOperator::LogicalAnd,
            Box::new(
                Expression::Index(
                    Box::new(Expression::Identifier(ast_path("y")).nowhere()),
                    Box::new(Expression::Identifier(ast_path("z")).nowhere()),
                )
                .nowhere(),
            ),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn tuple_index_operator_precedence_is_correct() {
        let code = r#"y#1#2"#;

        let expected = Expression::TupleIndex(
            Box::new(
                Expression::TupleIndex(
                    Box::new(Expression::Identifier(ast_path("y")).nowhere()),
                    1u128.nowhere(),
                )
                .nowhere(),
            ),
            2.nowhere(),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn absolute_pipeline_references_parse() {
        let code = r#"stage(s).var"#;

        let expected = Expression::PipelineReference(
            PipelineReference::Absolute(ast_ident("s")),
            ast_ident("var"),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn relative_forward_pipeline_references_parse() {
        let code = r#"stage(+5).var"#;

        let expected = Expression::PipelineReference(
            PipelineReference::Relative(5.nowhere()),
            ast_ident("var"),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }

    #[test]
    fn relative_backward_pipeline_references_parse() {
        let code = r#"stage(-5).var"#;

        let expected = Expression::PipelineReference(
            PipelineReference::Relative((-5).nowhere()),
            ast_ident("var"),
        )
        .nowhere();

        check_parse!(code, expression, Ok(expected));
    }
}
