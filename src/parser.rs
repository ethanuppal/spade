use colored::*;
use logos::Lexer;
use thiserror::Error;

use parse_tree_macros::trace_parser;

use crate::grammar::{Entity, Expression, Register, Statement, Type};
use crate::identifier::Identifier;
use crate::lexer::TokenKind;

/// A token with location info
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    kind: TokenKind,
    span: logos::Span,
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
    #[error("Lexer error")]
    LexerError,
    #[error("Unexpected token. got {}, expected {expected:?}", got.as_str())]
    UnexpectedToken {
        got: TokenKind,
        expected: Vec<&'static str>,
    },
    #[error("Expected to find a {} to match {friend:?}", expected.as_str())]
    UnmatchedPair { friend: Token, expected: TokenKind },

    // Non general errors
    #[error("A register clock must be specified")]
    RegisterClockMissing,
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
    fn identifier(&mut self) -> Result<Identifier> {
        let token = self.eat_cond(TokenKind::is_ident, "Identifier")?;

        if let TokenKind::Identifier(name) = token.kind {
            Ok(Identifier::Str(name))
        } else {
            unreachable!("eat_cond should have checked this");
        }
    }

    // Expression parsing
    #[trace_parser]
    fn expression(&mut self) -> Result<Expression> {
        let start = self.multiplicative_expression()?;

        if self.is_next_addition_operator()? {
            let operator = self.eat_unconditional()?;
            let rest = self.expression()?;
            // TODO: Do not use a string here
            Ok(Expression::BinaryOperator(
                Box::new(start),
                operator.kind,
                Box::new(rest),
            ))
        } else {
            Ok(start)
        }
    }

    #[trace_parser]
    fn multiplicative_expression(&mut self) -> Result<Expression> {
        let start = self.base_expression()?;
        if self.is_next_multiplication_operator()? {
            let operator = self.eat_unconditional()?;
            let rest = self.base_expression()?;
            // TODO: Do not use a string here
            Ok(Expression::BinaryOperator(
                Box::new(start),
                operator.kind,
                Box::new(rest),
            ))
        } else {
            Ok(start)
        }
    }

    #[trace_parser]
    fn base_expression(&mut self) -> Result<Expression> {
        if self.peek_and_eat_kind(&TokenKind::OpenParen)? {
            let inner = self.expression()?;
            self.eat(&TokenKind::CloseParen)?;
            Ok(inner)
        } else if self.peek_cond(TokenKind::is_integer, "integer")? {
            match self.eat_unconditional()?.kind {
                TokenKind::Integer(val) => Ok(Expression::IntLiteral(val)),
                _ => unreachable!(),
            }
        } else {
            self.identifier().map(Expression::Identifier)
        }
    }

    // Types
    #[trace_parser]
    fn parse_type(&mut self) -> Result<Type> {
        Ok(Type::Named(self.identifier()?))
    }

    /// A name with an associated type, as used in argument definitions as well
    /// as struct defintions
    ///
    /// name: Type
    // TODO: Use this for let bindings
    #[trace_parser]
    fn name_and_type(&mut self) -> Result<(Identifier, Type)> {
        let name = self.identifier()?;
        self.eat(&TokenKind::Colon);
        let t = self.parse_type()?;
        Ok((name, t))
    }

    // Statemenets

    #[trace_parser]
    fn binding(&mut self) -> Result<Option<Statement>> {
        if self.peek_and_eat_kind(&TokenKind::Let)? {
            let ident = self.identifier()?;

            let t = if self.peek_and_eat_kind(&TokenKind::Colon)? {
                Some(self.parse_type()?)
            } else {
                None
            };

            self.eat(&TokenKind::Assignment)?;
            let value = self.expression()?;
            self.eat(&TokenKind::Semi)?;

            Ok(Some(Statement::Binding(ident, t, value)))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    fn register_reset_definition(&mut self) -> Result<(Expression, Expression)> {
        let condition = self.expression()?;
        self.eat(&TokenKind::Colon)?;
        let value = self.expression()?;

        Ok((condition, value))
    }

    #[trace_parser]
    fn register(&mut self) -> Result<Option<Statement>> {
        if self.peek_and_eat_kind(&TokenKind::Reg)? {
            // Clock selection
            let clock = self
                .surrounded(
                    &TokenKind::OpenParen,
                    |s| s.identifier().map(Some),
                    &TokenKind::CloseParen,
                )
                .map_err(|_| Error::RegisterClockMissing)?
                // Identifier parsing can not fail since we map it into a Some. Therefore,
                // unwrap is safe
                .unwrap();

            // Name
            let name = self.identifier()?;

            // Optional type
            let value_type = if self.peek_and_eat_kind(&TokenKind::Colon)? {
                Some(self.parse_type()?)
            } else {
                None
            };

            // Optional reset
            let reset = if self.peek_and_eat_kind(&TokenKind::Reset)? {
                self.surrounded(
                    &TokenKind::OpenParen,
                    |s| s.register_reset_definition().map(Some),
                    &TokenKind::CloseParen,
                )?
            } else {
                None
            };

            // Value
            self.eat(&TokenKind::Assignment)?;
            let value = self.expression()?;

            Ok(Some(Statement::Register(Register {
                name,
                clock,
                reset,
                value,
                value_type,
            })))
        } else {
            Ok(None)
        }
    }

    /// If the next token is the start of a statement, return that statement,
    /// otherwise None
    #[trace_parser]
    fn statement(&mut self) -> Result<Option<Statement>> {
        self.first_successful(vec![&Self::binding, &Self::register])
    }

    #[trace_parser]
    fn statements(&mut self) -> Result<Vec<Statement>> {
        let mut result = vec![];
        while let Some(statement) = self.statement()? {
            result.push(statement)
        }
        Ok(result)
    }

    // Entities
    #[trace_parser]
    fn entity(&mut self) -> Result<Entity> {
        self.eat(&TokenKind::Entity)?;
        let name = self.identifier()?;

        // Input types
        self.eat(&TokenKind::OpenParen)?;
        let inputs = self.comma_separated(Self::name_and_type, &TokenKind::CloseParen)?;
        self.eat(&TokenKind::CloseParen)?;

        // Return type
        let output_type = if self.peek_and_eat_kind(&TokenKind::SlimArrow)? {
            Some(self.parse_type()?)
        } else {
            None
        }
        .unwrap_or(Type::UnitType);

        // Body (TODO: might want to make this a separate structure like a block)
        self.eat(&TokenKind::OpenBrace)?;
        let statements = self.statements()?;
        let output_value = self.expression()?;
        self.eat(&TokenKind::CloseBrace)?;

        Ok(Entity {
            name: name.to_string(),
            inputs,
            statements,
            output_type,
            output_value,
        })
    }

    // Helpers
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
            Some(TokenKind::Multiplication) => true,
            Some(TokenKind::Division) => true,
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
    ) -> Result<Option<T>> {
        let opener = self.eat(start)?;
        let result = inner(self)?;
        // TODO: Better error handling here. We are throwing away potential EOFs
        self.eat(end).map_err(|_| Error::UnmatchedPair {
            friend: opener,
            expected: end.clone(),
        })?;
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
                got: next.kind,
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

    /// Peeks the next token, checks if it matches `kind`. If so, it eats it
    /// and returns true, otherwise it returns false.
    fn peek_and_eat_kind(&mut self, kind: &TokenKind) -> Result<bool> {
        if self.peek_kind(kind)? {
            self.eat_unconditional()?;
            Ok(true)
        } else {
            Ok(false)
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
            Err(Error::LexerError)?
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
        check_parse!("abc123_", identifier, Ok("abc123_".into()));
    }

    #[test]
    fn addition_operatoins_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier("a".into())),
            TokenKind::Plus,
            Box::new(Expression::Identifier("b".into())),
        );

        check_parse!("a + b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn multiplications_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier("a".into())),
            TokenKind::Multiplication,
            Box::new(Expression::Identifier("b".into())),
        );

        check_parse!("a * b", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn multiplication_before_addition() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::BinaryOperator(
                Box::new(Expression::Identifier("a".into())),
                TokenKind::Multiplication,
                Box::new(Expression::Identifier("b".into())),
            )),
            TokenKind::Plus,
            Box::new(Expression::Identifier("c".into())),
        );

        check_parse!("a*b + c", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn bracketed_expressions_are_expressions() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::Identifier("a".into())),
            TokenKind::Multiplication,
            Box::new(Expression::BinaryOperator(
                Box::new(Expression::Identifier("b".into())),
                TokenKind::Plus,
                Box::new(Expression::Identifier("c".into())),
            )),
        );

        check_parse!("a * (b + c)", expression, Ok(expected_value.clone()));
    }
    #[test]
    fn repeated_bracketed_expressions_work() {
        let expected_value = Expression::BinaryOperator(
            Box::new(Expression::BinaryOperator(
                Box::new(Expression::Identifier("b".into())),
                TokenKind::Plus,
                Box::new(Expression::Identifier("c".into())),
            )),
            TokenKind::Multiplication,
            Box::new(Expression::Identifier("a".into())),
        );

        check_parse!("((b + c) * a)", expression, Ok(expected_value.clone()));
    }

    #[test]
    fn literals_are_expressions() {
        check_parse!("123", expression, Ok(Expression::IntLiteral(123)));
    }

    #[test]
    fn bindings_work() {
        let expected = Statement::Binding(
            Identifier::Str("test".to_string()),
            None,
            Expression::IntLiteral(123),
        );
        check_parse!("let test = 123;", statement, Ok(Some(expected)));
    }

    #[test]
    fn bindings_with_types_work() {
        let expected = Statement::Binding(
            Identifier::Str("test".to_string()),
            Some(Type::Named(Identifier::Str("bool".to_string()))),
            Expression::IntLiteral(123),
        );
        check_parse!("let test: bool = 123;", statement, Ok(Some(expected)));
    }

    #[test]
    fn entity_without_inputs() {
        let code = include_str!("../parser_test_code/entity_without_inputs.sp");
        let expected = Entity {
            name: "no_inputs".to_string(),
            inputs: vec![],
            statements: vec![
                Statement::Binding(
                    Identifier::Str("test".to_string()),
                    None,
                    Expression::IntLiteral(123),
                ),
                Statement::Binding(
                    Identifier::Str("test2".to_string()),
                    None,
                    Expression::IntLiteral(123),
                ),
            ],
            output_type: Type::UnitType,
            output_value: Expression::Identifier(Identifier::Str("test".to_string())),
        };

        check_parse!(code, entity, Ok(expected));
    }

    #[test]
    fn entity_with_inputs() {
        let code = include_str!("../parser_test_code/entity_with_inputs.sp");
        let expected = Entity {
            name: "with_inputs".to_string(),
            inputs: vec![
                (
                    Identifier::Str("clk".to_string()),
                    Type::Named(Identifier::Str("bool".to_string())),
                ),
                (
                    Identifier::Str("rst".to_string()),
                    Type::Named(Identifier::Str("bool".to_string())),
                ),
            ],
            statements: vec![],
            output_type: Type::Named(Identifier::Str("bool".to_string())),
            output_value: Expression::Identifier(Identifier::Str("clk".to_string())),
        };

        check_parse!(code, entity, Ok(expected));
    }

    #[test]
    fn parsing_register_without_reset_works() {
        let code = "reg(clk) name = 1;";

        let expected = Statement::Register(Register {
            name: Identifier::Str("name".to_string()),
            clock: Identifier::Str("clk".to_string()),
            reset: None,
            value: Expression::IntLiteral(1),
            value_type: None,
        });

        check_parse!(code, statement, Ok(Some(expected)));
    }

    #[test]
    fn parsing_register_with_reset_works() {
        let code = "reg(clk) name reset (rst: 0) = 1;";

        let expected = Statement::Register(Register {
            name: Identifier::Str("name".to_string()),
            clock: Identifier::Str("clk".to_string()),
            reset: Some((
                Expression::Identifier(Identifier::Str("rst".to_string())),
                Expression::IntLiteral(0),
            )),
            value: Expression::IntLiteral(1),
            value_type: None,
        });

        check_parse!(code, statement, Ok(Some(expected)));
    }

    #[test]
    fn parsing_register_with_reset_and_clock() {
        let code = "reg(clk) name: Type reset (rst: 0) = 1;";

        let expected = Statement::Register(Register {
            name: Identifier::Str("name".to_string()),
            clock: Identifier::Str("clk".to_string()),
            reset: Some((
                Expression::Identifier(Identifier::Str("rst".to_string())),
                Expression::IntLiteral(0),
            )),
            value: Expression::IntLiteral(1),
            value_type: Some(Type::Named(Identifier::Str("Type".to_string()))),
        });

        check_parse!(code, statement, Ok(Some(expected)));
    }
}
