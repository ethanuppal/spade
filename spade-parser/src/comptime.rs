use spade_ast::comptime::ComptimeCondOp;
use spade_ast::{comptime::ComptimeCondition, ComptimeConfig};
use spade_common::location_info::{Loc, WithLocation};

use crate::error::{Error, Result};
use crate::lexer::TokenKind;
use crate::Parser;

impl<'a> Parser<'a> {
    pub fn maybe_comptime_condition<T>(
        &mut self,
        inner_parser: &impl Fn(&mut Self) -> Result<Option<Loc<T>>>,
        wrapper: &impl Fn(ComptimeCondition<Loc<T>>) -> T,
    ) -> Result<Option<Loc<T>>>
    where
        T: WithLocation,
    {
        if let Some(start) = self.peek_and_eat(&TokenKind::ComptimeIf)? {
            let name = self.path()?;

            let op_tok = self.eat_unconditional()?;
            let op = match op_tok.kind {
                TokenKind::Equals => ComptimeCondOp::Eq,
                TokenKind::Gt => ComptimeCondOp::Gt,
                TokenKind::Lt => ComptimeCondOp::Lt,
                TokenKind::Ge => ComptimeCondOp::Ge,
                TokenKind::Le => ComptimeCondOp::Le,
                _ => {
                    return Err(Error::UnexpectedToken {
                        got: op_tok,
                        expected: vec!["<", ">", "<=", ">="],
                        context: None,
                    })
                }
            };

            let val = if let Some(val) = self.int_literal()? {
                val
            } else {
                return Err(Error::UnexpectedToken {
                    got: self.eat_unconditional()?,
                    expected: vec!["integer"],
                    context: None,
                });
            };

            let (inner, inner_loc) = self.surrounded(
                &TokenKind::OpenBrace,
                |s| s.maybe_comptime_condition(inner_parser, wrapper),
                &TokenKind::CloseBrace,
            )?;

            // TODO: Do we want to return None here, or should we throw an error
            if let Some(inner) = inner {
                // TODO: Handle else
                Ok(Some(
                    wrapper(ComptimeCondition {
                        condition: (name, op, val),
                        on_true: Box::new(inner),
                        on_false: None,
                    })
                    .between(self.file_id, &start, &inner_loc),
                ))
            } else {
                Ok(None)
            }
        } else {
            inner_parser(self)
        }
    }
}
