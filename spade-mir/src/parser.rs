use spade_common::location_info::{lspan, Loc, WithLocation};

use logos::Lexer;
use thiserror::Error;
use colored::*;
use parse_tree_macros::trace_parser;

use crate::{Binding, Statement, ValueName};
use crate::lexer::TokenKind;

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
    #[error("Unexpected token. got {}, expected {expected:?}", got.kind.as_str())]
    UnexpectedToken {
        got: Token,
        expected: Vec<&'static str>,
    },

    #[error("Expected name {}", got.kind.as_str())]
    ExpectedName{got: Token},
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Parser<'a> {
    lex: Lexer<'a, TokenKind>,
    peeked: Option<Token>,
    pub parse_stack: Vec<ParseStackEntry>,
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
    fn value_name(&mut self) -> Result<ValueName> {
        let tok = self.eat_unconditional()?;
        match tok.kind() {
            TokenKind::NameID(id) => Ok(ValueName::Named(id)),
            TokenKind::ExprID(id) => Ok(ValueName::Expr(id))
            TokenKind::Integer(_) => {}
            TokenKind::True => {}
            TokenKind::False => {}
            TokenKind::Reg => {}
            TokenKind::Assignment => {}
            TokenKind::Whitespace => {}
            TokenKind::Comment => {}
            TokenKind::Error => {}
        }
    }

    #[trace_parser]
    fn binding(&mut self) -> Result<Option<Binding>> {
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
