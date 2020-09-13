use colored::*;
use logos::Lexer;
use thiserror::Error;

use parse_tree_macros::trace_parser;

use crate::ast::{Block, Entity, Expression, Identifier, Register, Statement, Type};
use crate::lexer::TokenKind;
use crate::location_info::{lspan, Loc, WithLocation};

/// A token with location info
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: logos::Span,
}

impl Token {
    pub fn new(kind: TokenKind, lexer: &Lexer<TokenKind>) -> Self {
        Self {
            kind,
            span: lexer.span(),
        }
    }
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("End of file")]
    Eof,
    #[error("Lexer error at {}", 0.0)]
    LexerError(codespan::Span),
    #[error("Unexpected token. got {:?}, expected {expected:?}")]
    UnexpectedToken {
        got: Token,
        expected: Vec<&'static str>,
    },
    #[error("Expected to find a {} to match {friend:?}", expected.as_str())]
    UnmatchedPair { friend: Token, expected: TokenKind },

    #[error("Expected expression, got {got:?}")]
    ExpectedExpression { got: Token },

    #[error("Entity missing block for {for_what}")]
    ExpectedBlock {
        for_what: String,
        got: Token,
        loc: Loc<()>,
    },
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Parser<'a> {
    lex: Lexer<'a, TokenKind>,
    peeked: Option<Token>,
    parse_stack: Vec<ParseStackEntry>,
}

impl<'a> Parser<'a> {
    pub fn new(lex: Lexer<'a, TokenKind>) -> Self {
        Self {
            lex,
            peeked: None,
            parse_stack: vec![],
        }
    }
}

// Actual parsing functions
impl<'a> Parser<'a> {
    #[trace_parser]
    fn identifier(&mut self) -> Result<Loc<Identifier>> {
        let token = self.eat_cond(TokenKind::is_ident, "Identifier")?;

        if let TokenKind::Identifier(name) = token.kind {
            Ok(Identifier(name).at(lspan(token.span)))
        } else {
            unreachable!("eat_cond should have checked this");
        }
    }

    // Expression parsing
    #[trace_parser]
    fn expression(&mut self) -> Result<Loc<Expression>> {
        let start = self.multiplicative_expression()?;

        if self.is_next_addition_operator()? {
            let operator = self.eat_unconditional()?;
            let rest = self.expression()?;

            let span = start.span.merge(rest.span);
            Ok(Expression::BinaryOperator(Box::new(start), operator.kind, Box::new(rest)).at(span))
        } else {
            Ok(start)
        }
    }

    #[trace_parser]
    fn multiplicative_expression(&mut self) -> Result<Loc<Expression>> {
        let (start, start_span) = self.base_expression()?.separate();
        if self.is_next_multiplication_operator()? {
            let operator = self.eat_unconditional()?;
            let (rest, end_span) = self.base_expression()?.separate();
            // TODO: Do not use a string here
            Ok(
                Expression::BinaryOperator(Box::new(start), operator.kind, Box::new(rest))
                    .at(start_span.merge(end_span)),
            )
        } else {
            Ok(start)
        }
    }

    #[trace_parser]
    fn base_expression(&mut self) -> Result<Loc<Expression>> {
        if self.peek_and_eat_kind(&TokenKind::OpenParen)?.is_some() {
            let inner = self.expression()?;
            self.eat(&TokenKind::CloseParen)?;
            Ok(inner)
        } else if let Some(val) = self.int_literal()? {
            Ok(val.map(Expression::IntLiteral))
        } else if let Some(block) = self.block()? {
            Ok(block.map(Box::new).map(Expression::Block))
        } else if let Some(if_expr) = self.if_expression()? {
            Ok(if_expr)
        } else {
            match self.identifier() {
                Ok(ident) => {
                    let span = ident.span;
                    Ok(Expression::Identifier(ident).at(span))
                }
                Err(Error::UnexpectedToken { got, .. }) => Err(Error::ExpectedExpression { got }),
                Err(e) => Err(e),
            }
        }
    }

    #[trace_parser]
    pub fn if_expression(&mut self) -> Result<Option<Loc<Expression>>> {
        if let Some(start) = self.peek_and_eat_kind(&TokenKind::If)? {
            let cond = self.expression()?;
            let on_true = if let Some(block) = self.block()? {
                block
            } else {
                return Err(Error::ExpectedBlock {
                    for_what: "if".to_string(),
                    got: self.peek()?.unwrap(),
                    loc: Loc::new((), lspan(start.span).merge(cond.span)),
                });
            };
            let else_tok = self.eat(&TokenKind::Else)?;
            let (on_false, end_span) = if let Some(block) = self.block()? {
                block.separate()
            } else {
                return Err(Error::ExpectedBlock {
                    for_what: "else".to_string(),
                    got: self.peek()?.unwrap(),
                    loc: Loc::new((), lspan(else_tok.span)),
                });
            };

            Ok(Some(
                Expression::If(Box::new(cond), Box::new(on_true), Box::new(on_false))
                    .at(lspan(start.span).merge(end_span)),
            ))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn int_literal(&mut self) -> Result<Option<Loc<u128>>> {
        if self.peek_cond(TokenKind::is_integer, "integer")? {
            let token = self.eat_unconditional()?;
            match token.kind {
                TokenKind::Integer(val) => Ok(Some(Loc::new(val, lspan(token.span)))),
                _ => unreachable!(),
            }
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn block(&mut self) -> Result<Option<Loc<Block>>> {
        let start = if let Some(start) = self.peek_and_eat_kind(&TokenKind::OpenBrace)? {
            start
        } else {
            return Ok(None);
        };
        let statements = self.statements()?;
        let output_value = self.expression()?;
        let end_token = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(
            Block {
                statements,
                result: output_value,
            }
            .at(lspan(start.span).merge(lspan(end_token.span))),
        ))
    }

    // Types
    #[trace_parser]
    fn parse_type(&mut self) -> Result<Loc<Type>> {
        let (ident, span) = self.identifier()?.separate();

        // Check if it is a sized type
        if self.peek_kind(&TokenKind::OpenBracket)? {
            let (size, bracket_span) = self.surrounded(
                &TokenKind::OpenBracket,
                |s| s.expression().map(Some),
                &TokenKind::CloseBracket,
            )?;

            // Note: safe unwrap, if we got here, the expression must have matched
            // and so the size is present, otherwise we'd return early above
            let size = size.unwrap();

            Ok(
                Type::WithSize(Box::new(Type::Named(ident.strip()).at(span)), size)
                    .at(span.merge(bracket_span.span)),
            )
        } else {
            Ok(Type::Named(ident.strip()).at(span))
        }
    }

    /// A name with an associated type, as used in argument definitions as well
    /// as struct defintions
    ///
    /// name: Type
    // TODO: Use this for let bindings
    #[trace_parser]
    fn name_and_type(&mut self) -> Result<(Loc<Identifier>, Loc<Type>)> {
        let name = self.identifier()?;
        self.eat(&TokenKind::Colon)?;
        let t = self.parse_type()?;
        Ok((name, t))
    }

    // Statemenets

    #[trace_parser]
    fn binding(&mut self) -> Result<Option<Loc<Statement>>> {
        if self.peek_and_eat_kind(&TokenKind::Let)?.is_some() {
            let (ident, start_span) = self.identifier()?.separate();

            let t = if self.peek_and_eat_kind(&TokenKind::Colon)?.is_some() {
                Some(self.parse_type()?)
            } else {
                None
            };

            self.eat(&TokenKind::Assignment)?;
            let (value, end_span) = self.expression()?.separate();
            self.eat(&TokenKind::Semi)?;

            Ok(Some(
                Statement::Binding(ident, t, value).at(start_span.merge(end_span)),
            ))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    fn register_reset_definition(&mut self) -> Result<(Loc<Expression>, Loc<Expression>)> {
        let condition = self.expression()?;
        self.eat(&TokenKind::Colon)?;
        let value = self.expression()?;

        Ok((condition, value))
    }

    #[trace_parser]
    fn register(&mut self) -> Result<Option<Loc<Statement>>> {
        if let Some(start_token) = self.peek_and_eat_kind(&TokenKind::Reg)? {
            // Clock selection
            let (clock, _clock_paren_span) = self.surrounded(
                &TokenKind::OpenParen,
                |s| s.identifier().map(Some),
                &TokenKind::CloseParen,
            )?;

            // Identifier parsing can not fail since we map it into a Some. Therefore,
            // unwrap is safe
            let clock = clock.unwrap();

            // Name
            let name = self.identifier()?;

            // Optional type
            let value_type = if self.peek_and_eat_kind(&TokenKind::Colon)?.is_some() {
                Some(self.parse_type()?)
            } else {
                None
            };

            // Optional reset
            let reset = if self.peek_and_eat_kind(&TokenKind::Reset)?.is_some() {
                let (reset, _) = self.surrounded(
                    &TokenKind::OpenParen,
                    |s| s.register_reset_definition().map(Some),
                    &TokenKind::CloseParen,
                )?;
                reset
            } else {
                None
            };

            // Value
            self.eat(&TokenKind::Assignment)?;
            let (value, end_span) = self.expression()?.separate();

            let span = lspan(start_token.span).merge(end_span);
            let result = Statement::Register(
                Register {
                    name,
                    clock,
                    reset,
                    value,
                    value_type,
                }
                .at(span),
            )
            .at(span);
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    /// If the next token is the start of a statement, return that statement,
    /// otherwise None
    #[trace_parser]
    fn statement(&mut self) -> Result<Option<Loc<Statement>>> {
        self.first_successful(vec![&Self::binding, &Self::register])
    }

    #[trace_parser]
    fn statements(&mut self) -> Result<Vec<Loc<Statement>>> {
        let mut result = vec![];
        while let Some(statement) = self.statement()? {
            result.push(statement)
        }
        Ok(result)
    }

    // Entities
    #[trace_parser]
    pub fn entity(&mut self) -> Result<Loc<Entity>> {
        let start_token = self.eat(&TokenKind::Entity)?;
        let name = self.identifier()?;

        // Input types
        self.eat(&TokenKind::OpenParen)?;
        let inputs = self.comma_separated(Self::name_and_type, &TokenKind::CloseParen)?;
        let close_paren = self.eat(&TokenKind::CloseParen)?;

        // Return type
        let output_type = if self.peek_and_eat_kind(&TokenKind::SlimArrow)?.is_some() {
            Some(self.parse_type()?)
        } else {
            None
        };

        // Body (TODO: might want to make this a separate structure like a block)
        let (block, block_span) = if let Some(block) = self.block()? {
            block.separate()
        } else {
            // The end of the entity definition depends on wether or not
            // a type is present.
            let end_loc = output_type
                .map(|t| t.loc().span)
                .unwrap_or_else(|| lspan(close_paren.span));

            return Err(Error::ExpectedBlock {
                // NOTE: Unwrap should be safe becase we have already checked
                // if this is a { or not
                for_what: "entity".to_string(),
                got: self.peek()?.unwrap(),
                loc: Loc::new((), lspan(start_token.span).merge(end_loc)),
            });
        };

        Ok(Entity {
            name,
            inputs,
            output_type: output_type.unwrap_or(Type::UnitType.nowhere()),
            block,
        }
        .at(lspan(start_token.span).merge(block_span)))
    }
}

// Helper functions for checking the type of tokens
impl<'a> Parser<'a> {
    fn is_next_addition_operator(&mut self) -> Result<bool> {
        Ok(match self.peek()?.map(|token| token.kind) {
            Some(TokenKind::Plus) => true,
            Some(TokenKind::Minus) => true,
            _ => false,
        })
    }
    fn is_next_multiplication_operator(&mut self) -> Result<bool> {
        Ok(match self.peek()?.map(|token| token.kind) {
            Some(TokenKind::Asterisk) => true,
            Some(TokenKind::Slash) => true,
            _ => false,
        })
    }
}

// Helper functions for combining parsers
impl<'a> Parser<'a> {
    fn first_successful<T>(
        &mut self,
        parsers: Vec<&dyn Fn(&mut Self) -> Result<Option<T>>>,
    ) -> Result<Option<T>> {
        for parser in parsers {
            match parser(self) {
                Ok(Some(val)) => return Ok(Some(val)),
                Ok(None) => continue,
                Err(e) => return Err(e),
            }
        }
        Ok(None)
    }

    /// Attempts to parse an inner structure surrouned by two tokens, like `( x )`.
    ///
    /// If the `start` token is not found, an error is produced.
    ///
    /// If the `start` token is found, but the inner parser returns `None`, `None` is returned.
    ///
    /// If the end token is not found, return a missmatch error
    fn surrounded<T>(
        &mut self,
        start: &TokenKind,
        inner: impl Fn(&mut Self) -> Result<Option<T>>,
        end: &TokenKind,
    ) -> Result<(Option<T>, Loc<()>)> {
        let opener = self.eat(start)?;
        let result = inner(self)?;
        // TODO: Better error handling here. We are throwing away potential EOFs
        let end = self.eat(end).map_err(|_| Error::UnmatchedPair {
            friend: opener.clone(),
            expected: end.clone(),
        })?;

        Ok((
            result,
            Loc::new((), lspan(opener.span).merge(lspan(end.span))),
        ))
    }

    #[trace_parser]
    fn comma_separated<T>(
        &mut self,
        inner: impl Fn(&mut Self) -> Result<T>,
        // This end marker is used for allowing trailing commas. It should
        // be whatever ends the collection that is searched. I.e. (a,b,c,) should have
        // `)`, and {} should have `}`
        end_marker: &TokenKind,
    ) -> Result<Vec<T>> {
        let mut result = vec![];

        loop {
            // The list might be empty
            if self.peek_kind(end_marker)? {
                break;
            }
            result.push(inner(self)?);

            // Now we expect to either find a comma, in which case we resume the
            // search, or an end marker, in which case we abort
            if self.peek_kind(end_marker)? {
                break;
            } else {
                self.eat(&TokenKind::Comma)?;
            }
        }
        Ok(result)
    }
}

// Helper functions for advancing the token stream
impl<'a> Parser<'a> {
    fn eat(&mut self, expected: &TokenKind) -> Result<Token> {
        self.eat_cond(|k| k == expected, expected.as_str())
    }

    fn eat_cond(
        &mut self,
        condition: impl Fn(&TokenKind) -> bool,
        expected_description: &'static str,
    ) -> Result<Token> {
        // Check if we already have a peeked token
        let next = self.eat_unconditional()?;

        // Make sure we ate the correct token
        if !condition(&next.kind) {
            Err(Error::UnexpectedToken {
                got: next,
                expected: vec![expected_description],
            })
        } else {
            Ok(next)
        }
    }

    fn eat_unconditional(&mut self) -> Result<Token> {
        let food = self
            .peeked
            .take()
            .map(Ok)
            .unwrap_or_else(|| self.next_token())?;

        self.parse_stack.push(ParseStackEntry::Ate(food.clone()));
        Ok(food)
    }

    /// Peeks the next token. If it is the sepcified kind, returns that token, otherwise
    /// returns None
    fn peek_and_eat_kind(&mut self, kind: &TokenKind) -> Result<Option<Token>> {
        if self.peek_kind(kind)? {
            Ok(Some(self.eat_unconditional()?))
        } else {
            Ok(None)
        }
    }

    fn peek(&mut self) -> Result<Option<Token>> {
        if let Some(prev) = self.peeked.clone() {
            Ok(Some(prev))
        } else {
            let result = match self.next_token() {
                Ok(token) => Some(token),
                Err(Error::Eof) => None,
                Err(e) => return Err(e),
            };
            self.peeked = result.clone();
            Ok(result)
        }
    }

    fn peek_kind(&mut self, expected: &TokenKind) -> Result<bool> {
        let result = self.peek_cond_no_tracing(|kind| kind == expected)?;
        self.parse_stack
            .push(ParseStackEntry::PeekingFor(expected.clone(), result));
        Ok(result)
    }

    /// Peek the next token, returning true if the result satisfies the condition.
    ///
    /// If we reached EOF and the peek returns None, returns false
    fn peek_cond(&mut self, cond: impl Fn(&TokenKind) -> bool, msg: &str) -> Result<bool> {
        let result = self.peek_cond_no_tracing(cond)?;
        self.parse_stack.push(ParseStackEntry::PeekingWithCondition(
            msg.to_string(),
            result,
        ));
        Ok(result)
    }

    fn peek_cond_no_tracing(&mut self, cond: impl Fn(&TokenKind) -> bool) -> Result<bool> {
        self.peek().map(|token| {
            if let Some(inner) = token {
                cond(&inner.kind)
            } else {
                false
            }
        })
    }

    fn next_token(&mut self) -> Result<Token> {
        let kind = self.lex.next().ok_or(Error::Eof)?;

        if let TokenKind::Error = kind {
            Err(Error::LexerError(lspan(self.lex.span())))?
        };

        Ok(Token::new(kind, &self.lex))
    }
}

pub enum ParseStackEntry {
    Enter(String),
    Ate(Token),
    PeekingWithCondition(String, bool),
    PeekingFor(TokenKind, bool),
    Exit,
    ExitWithError(Error),
}
pub fn format_parse_stack(stack: &[ParseStackEntry]) -> String {
    let mut result = String::new();
    let mut indent_amount = 0;

    for entry in stack {
        let mut next_indent_amount = indent_amount;
        let message = match entry {
            ParseStackEntry::Enter(function) => {
                next_indent_amount += 1;
                format!("{} `{}`", "trying".white(), function.blue())
            }
            ParseStackEntry::Ate(token) => format!(
                "{} '{}'",
                "Eating".bright_yellow(),
                token.kind.as_str().bright_purple()
            ),
            ParseStackEntry::PeekingFor(kind, success) => format!(
                "{} {} {}",
                "peeking for".white(),
                kind.as_str().bright_blue(),
                if *success {
                    "✓".green()
                } else {
                    "𐄂".red()
                }
            ),
            ParseStackEntry::PeekingWithCondition(needle, success) => format!(
                "{} {} {}",
                "peeking conditionally for ".white(),
                needle.bright_blue(),
                if *success {
                    "✓".green()
                } else {
                    "𐄂".red()
                }
            ),
            ParseStackEntry::Exit => {
                next_indent_amount -= 1;
                format!("")
            }
            ParseStackEntry::ExitWithError(err) => {
                next_indent_amount -= 1;
                format!("{} {}", "Giving up: ".bright_red(), err)
            }
        };
        if let ParseStackEntry::Exit = entry {
        } else {
            for _ in 0..indent_amount {
                result += "| ";
            }
            result += &message;
            result += "\n"
        }
        indent_amount = next_indent_amount;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    use logos::Logos;

    pub fn _ident(name: &str) -> Loc<Identifier> {
        Identifier(name.to_string()).nowhere()
    }

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
        check_parse!("abc123_", identifier, Ok(_ident("abc123_")));
    }

    #[test]
    fn addition_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(_ident("a")).nowhere()),
            TokenKind::Plus,
            Box::new(Expression::Identifier(_ident("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a + b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn multiplications_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(_ident("a")).nowhere()),
            TokenKind::Asterisk,
            Box::new(Expression::Identifier(_ident("b")).nowhere()),
        )
        .nowhere();

        check_parse!("a * b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn multiplication_before_addition() {
        let expected_value = Expression::BinaryOperator(
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(_ident("a")).nowhere()),
                    TokenKind::Asterisk,
                    Box::new(Expression::Identifier(_ident("b")).nowhere()),
                )
                .nowhere(),
            ),
            TokenKind::Plus,
            Box::new(Expression::Identifier(_ident("c")).nowhere()),
        )
        .nowhere();

        check_parse!("a*b + c", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn bracketed_expressions_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier(_ident("a")).nowhere()),
            TokenKind::Asterisk,
            Box::new(
                Expression::BinaryOperator(
                    Box::new(Expression::Identifier(_ident("b")).nowhere()),
                    TokenKind::Plus,
                    Box::new(Expression::Identifier(_ident("c")).nowhere()),
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
                    Box::new(Expression::Identifier(_ident("b")).nowhere()),
                    TokenKind::Plus,
                    Box::new(Expression::Identifier(_ident("c")).nowhere()),
                )
                .nowhere(),
            ),
            TokenKind::Asterisk,
            Box::new(Expression::Identifier(_ident("a")).nowhere()),
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
            Box::new(Expression::Identifier(Identifier("a".to_string()).nowhere()).nowhere()),
            Box::new(
                Block {
                    statements: vec![],
                    result: Expression::Identifier(Identifier("b".to_string()).nowhere()).nowhere(),
                }
                .nowhere(),
            ),
            Box::new(
                Block {
                    statements: vec![],
                    result: Expression::Identifier(Identifier("c".to_string()).nowhere()).nowhere(),
                }
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
                Identifier("a".to_string()).nowhere(),
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
                Identifier("a".to_string()).nowhere(),
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
        let expected =
            Statement::Binding(_ident("test"), None, Expression::IntLiteral(123).nowhere())
                .nowhere();
        check_parse!("let test = 123;", binding, Ok(Some(expected)));
    }

    #[test]
    fn bindings_with_types_work() {
        let expected = Statement::Binding(
            Identifier("test".to_string()).nowhere(),
            Some(Type::Named(Identifier("bool".to_string())).nowhere()),
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
            output_type: Type::UnitType.nowhere(),
            block: Block {
                statements: vec![
                    Statement::Binding(
                        Identifier("test".to_string()).nowhere(),
                        None,
                        Expression::IntLiteral(123).nowhere(),
                    )
                    .nowhere(),
                    Statement::Binding(
                        Identifier("test2".to_string()).nowhere(),
                        None,
                        Expression::IntLiteral(123).nowhere(),
                    )
                    .nowhere(),
                ],
                result: Expression::Identifier(Identifier("test".to_string()).nowhere()).nowhere(),
            }
            .nowhere(),
        }
        .nowhere();

        check_parse!(code, entity, Ok(expected));
    }

    #[test]
    fn entity_with_inputs() {
        let code = include_str!("../parser_test_code/entity_with_inputs.sp");
        let expected = Entity {
            name: Identifier("with_inputs".to_string()).nowhere(),
            inputs: vec![
                (
                    Identifier("clk".to_string()).nowhere(),
                    Type::Named(Identifier("bool".to_string())).nowhere(),
                ),
                (
                    Identifier("rst".to_string()).nowhere(),
                    Type::Named(Identifier("bool".to_string())).nowhere(),
                ),
            ],
            output_type: Type::Named(Identifier("bool".to_string())).nowhere(),
            block: Block {
                statements: vec![],
                result: Expression::Identifier(Identifier("clk".to_string()).nowhere()).nowhere(),
            }
            .nowhere(),
        }
        .nowhere();

        check_parse!(code, entity, Ok(expected));
    }

    #[test]
    fn parsing_register_without_reset_works() {
        let code = "reg(clk) name = 1;";

        let expected = Statement::Register(
            Register {
                name: Identifier("name".to_string()).nowhere(),
                clock: Identifier("clk".to_string()).nowhere(),
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
                name: Identifier("name".to_string()).nowhere(),
                clock: Identifier("clk".to_string()).nowhere(),
                reset: Some((
                    Expression::Identifier(Identifier("rst".to_string()).nowhere()).nowhere(),
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
                clock: Identifier("clk".to_string()).nowhere(),
                reset: Some((
                    Expression::Identifier(Identifier("rst".to_string()).nowhere()).nowhere(),
                    Expression::IntLiteral(0).nowhere(),
                )),
                value: Expression::IntLiteral(1).nowhere(),
                value_type: Some(Type::Named(Identifier("Type".to_string())).nowhere()),
            }
            .nowhere(),
        )
        .nowhere();

        check_parse!(code, statement, Ok(Some(expected)));
    }

    #[test]
    fn size_types_work() {
        let expected = Type::WithSize(
            Box::new(Type::Named(Identifier("uint".to_string())).nowhere()),
            Expression::IntLiteral(10).nowhere(),
        )
        .nowhere();
        check_parse!("uint[10]", parse_type, Ok(expected));
    }
}
