use spade_ast::comptime::ComptimeCondOp;
use spade_ast::comptime::ComptimeCondition;
use spade_ast::comptime::MaybeComptime;
use spade_ast::IntLiteral;
use spade_common::location_info::{Loc, WithLocation};
use spade_diagnostics::Diagnostic;

use crate::error::{Result, UnexpectedToken};
use crate::lexer::TokenKind;
use crate::Parser;

impl<'a> Parser<'a> {
    /// Tries to parse a comptime condition containing an ast node T. If there
    /// is no comptime condition present, Ok(None) is returned
    pub fn comptime_condition<I, T>(
        &mut self,
        inner_parser: &impl Fn(&mut Self) -> Result<I>,
        wrapper: &impl Fn(ComptimeCondition<I>, Loc<()>) -> Loc<T>,
    ) -> Result<Option<Loc<T>>> {
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
                    return Err(Diagnostic::from(UnexpectedToken {
                        got: op_tok,
                        expected: vec!["<", ">", "<=", ">="],
                    }))
                }
            };

            let val = if let Some(val) = self.int_literal()? {
                val
            } else {
                return Err(Diagnostic::from(UnexpectedToken {
                    got: self.eat_unconditional()?,
                    expected: vec!["integer"],
                }));
            };

            let (on_true, on_true_loc) =
                self.surrounded(&TokenKind::OpenBrace, inner_parser, &TokenKind::CloseBrace)?;

            let (on_false, on_false_loc) = if self.peek_and_eat(&TokenKind::ComptimeElse)?.is_some()
            {
                let (inner, on_false_loc) =
                    self.surrounded(&TokenKind::OpenBrace, inner_parser, &TokenKind::CloseBrace)?;

                (Some(Box::new(inner)), Some(on_false_loc))
            } else {
                (None, None)
            };

            Ok(Some(wrapper(
                ComptimeCondition {
                    condition: (name, op, val.map(IntLiteral::as_signed)),
                    on_true: Box::new(on_true),
                    on_false,
                },
                ().between(self.file_id, &start, &on_false_loc.unwrap_or(on_true_loc)),
            )))
        } else {
            Ok(None)
        }
    }

    pub fn maybe_comptime<I>(
        &mut self,
        inner_parser: &impl Fn(&mut Self) -> Result<Loc<I>>,
    ) -> Result<Loc<MaybeComptime<Loc<I>>>> {
        if let Some(comptime) =
            self.comptime_condition(inner_parser, &|inner, loc| inner.at_loc(&loc))?
        {
            let loc = comptime.loc();
            Ok(MaybeComptime::Comptime(comptime).at_loc(&loc))
        } else {
            let inner = inner_parser(self)?;
            let loc = inner.loc();
            Ok(MaybeComptime::Raw(inner).at_loc(&loc))
        }
    }
}
