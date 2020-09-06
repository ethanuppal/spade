use colored::*;
use logos::Lexer;
use thiserror::Error;

use parse_tree_macros::trace_parser;

use crate::grammar::{Expression, Statement, Type};
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
        if self.peek_kind(&TokenKind::OpenParen)? {
            self.eat_unconditional()?;
            let inner = self.expression()?;
            self.eat(TokenKind::CloseParen)?;
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

    // Statemenets
    #[trace_parser]
    fn statement(&mut self) -> Result<Statement> {
        self.eat(TokenKind::Let)?;
        let ident = self.identifier()?;

        let t = if self.peek_kind(&TokenKind::Colon)? {
            self.eat_unconditional()?;
            Some(self.parse_type()?)
        } else {
            None
        };

        self.eat(TokenKind::Assignment)?;
        let value = self.expression()?;
        self.eat(TokenKind::Semi)?;

        Ok(Statement::Binding(ident, t, value))
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

// Helper functions for advancing the token stream
impl<'a> Parser<'a> {
    fn eat(&mut self, expected: TokenKind) -> Result<Token> {
        self.eat_cond(|k| k == &expected, expected.as_str())
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
        check_parse!("let test = 123;", statement, Ok(expected));
    }

    #[test]
    fn bindings_with_types_work() {
        let expected = Statement::Binding(
            Identifier::Str("test".to_string()),
            Some(Type::Named(Identifier::Str("bool".to_string()))),
            Expression::IntLiteral(123),
        );
        check_parse!("let test: bool = 123;", statement, Ok(expected));
    }
}
