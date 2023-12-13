// Utilities related to argument matching between callers and callees. Lives in spade-hir
// because this is required twice in the compilation process: first during type inference,
// and then again during hir lowering

use std::collections::HashSet;

use itertools::Itertools;
use spade_diagnostics::Diagnostic;
use thiserror::Error;

use spade_common::{location_info::Loc, name::Identifier};

use crate::expression::NamedArgument;
use crate::{ArgumentList, Expression, Parameter, ParameterList, TypeSpec};

#[derive(Error, Debug, PartialEq, Clone)]
pub enum ArgumentError {
    #[error("Too few arguments")]
    TooFewArguments {
        got: usize,
        expected: usize,
        missing: Vec<Identifier>,
        at: Loc<()>,
    },
    #[error("Too many arguments")]
    TooManyArguments {
        got: usize,
        expected: usize,
        extra: Vec<Loc<Expression>>,
        at: Loc<()>,
    },
    #[error("No argument named {name}")]
    NoSuchArgument { name: Loc<Identifier> },
    #[error("Missing arguments")]
    MissingArguments {
        missing: Vec<Identifier>,
        at: Loc<()>,
    },
    #[error("{new} was bound more than once")]
    DuplicateNamedBindings {
        new: Loc<Identifier>,
        prev_loc: Loc<()>,
    },
}

impl From<ArgumentError> for Diagnostic {
    fn from(error: ArgumentError) -> Self {
        match error {
            ArgumentError::TooManyArguments {
                expected,
                got,
                extra,
                at,
            } => {
                let plural = if expected == 1 { "" } else { "s" };
                let mut base = Diagnostic::error(
                    at,
                    format!("Too many arguments. Expected {expected}, got {got}"),
                )
                .primary_label(format!("Expected {expected} argument{plural}"));

                for e in extra {
                    base = base.secondary_label(e, "Unexpected argument".to_string())
                }
                base
            }
            ArgumentError::TooFewArguments {
                expected,
                got,
                missing,
                at,
            } => {
                let missing_plural = if missing.len() == 1 { "" } else { "s" };

                let leading_comma = if got == 0 { "" } else { ", " };
                let suggestion = format!(
                    "{leading_comma}{}",
                    missing.iter().map(|p| format!("/* {p} */")).join(", ")
                );

                Diagnostic::error(
                    at,
                    format!("Too few arguments. Expected {expected}, got {got}"),
                )
                .primary_label(format!(
                    "Missing {count} argument{missing_plural}",
                    count = missing.len()
                ))
                .span_suggest_insert_after(
                    format!("Consider providing the argument{missing_plural}"),
                    at,
                    suggestion,
                )
            }
            ArgumentError::NoSuchArgument { name } => {
                Diagnostic::error(&name, format!("No such argument: {name}"))
                    .primary_label("No such argument")
            }
            ArgumentError::MissingArguments { mut missing, at } => {
                let plural = if missing.len() == 1 { "" } else { "s" };

                missing.sort_by_key(|arg| arg.0.clone());

                let arg_list = missing
                    .iter()
                    .map(|i| format!("{i}"))
                    .collect::<Vec<_>>()
                    .join(", ");

                Diagnostic::error(at, format!("Missing argument{plural}: {arg_list}"))
                    .primary_label(format!("Missing argument{plural}: {arg_list}"))
            }
            ArgumentError::DuplicateNamedBindings { new, prev_loc } => {
                Diagnostic::error(&new, format!("{new} specified multiple times"))
                    .primary_label("Later specified here")
                    .secondary_label(prev_loc, "First specified here")
            }
        }
    }
}

pub enum ArgumentKind {
    Positional,
    Named,
    ShortNamed,
}

pub struct Argument<'a> {
    pub target: &'a Loc<Identifier>,
    pub value: &'a Loc<Expression>,
    pub target_type: &'a Loc<TypeSpec>,
    pub kind: ArgumentKind,
}

/// Matches the arguments passed in an argument list with the parameters of a parameter list. If
/// the arguments match (correct amount of positional arguments, or unique mapping of named
/// arguments), the mapping from argument to parameter is returned as a vector in positional order
/// (but with named argument targets included for better diagnostics)
pub fn match_args_with_params<'a>(
    arg_list: &'a Loc<ArgumentList>,
    params: &'a ParameterList,
    is_method: bool,
) -> Result<Vec<Argument<'a>>, ArgumentError> {
    match &arg_list.inner {
        ArgumentList::Positional(inner) => {
            let inner_loc = arg_list.shrink_left("(").shrink_right(")");

            if inner.len() < params.0.len() {
                return Err(ArgumentError::TooFewArguments {
                    got: inner.len() - if is_method { 1 } else { 0 },
                    expected: params.0.len() - if is_method { 1 } else { 0 },
                    missing: params
                        .0
                        .iter()
                        .skip(inner.len())
                        .map(|p| p.name.clone().inner)
                        .collect(),
                    at: inner_loc,
                });
            }

            if inner.len() > params.0.len() {
                return Err(ArgumentError::TooManyArguments {
                    got: inner.len() - if is_method { 1 } else { 0 },
                    expected: params.0.len() - if is_method { 1 } else { 0 },
                    extra: inner.iter().skip(params.0.len()).cloned().collect(),
                    at: inner_loc,
                });
            }

            Ok(inner
                .iter()
                .zip(params.0.iter())
                .map(|(arg, param)| Argument {
                    target: &param.name,
                    target_type: &param.ty,
                    value: arg,
                    kind: ArgumentKind::Positional,
                })
                .collect())
        }
        ArgumentList::Named(inner) => {
            let mut bound: HashSet<Loc<Identifier>> = HashSet::new();
            let mut unbound = params
                .0
                .iter()
                .map(|Parameter { name: ident, .. }| ident.inner.clone())
                .collect::<HashSet<_>>();

            let mut result = inner
                .iter()
                .map(|arg| {
                    let (target, expr, kind) = match arg {
                        NamedArgument::Full(i, e) => (i, e, ArgumentKind::Named),
                        NamedArgument::Short(i, e) => (i, e, ArgumentKind::ShortNamed),
                    };

                    // Check if this is a new binding
                    if let Some(prev) = bound.get(target) {
                        return Err(ArgumentError::DuplicateNamedBindings {
                            new: target.clone(),
                            prev_loc: prev.loc(),
                        });
                    }
                    bound.insert(target.clone());

                    let target_type = if let Some(t) = params.try_get_arg_type(target) {
                        t
                    } else {
                        return Err(ArgumentError::NoSuchArgument {
                            name: target.clone(),
                        });
                    };

                    unbound.remove(target);

                    // NOTE: Safe unwrap, we already checked that the parameter
                    // list has this arg
                    let index = params.arg_index(target).unwrap();

                    Ok((
                        index,
                        Argument {
                            target,
                            value: expr,
                            target_type,
                            kind,
                        },
                    ))
                })
                .collect::<Result<Vec<_>, ArgumentError>>()?;

            result.sort_by_key(|(i, _)| *i);

            let result = result.into_iter().map(|(_, arg)| arg).collect();

            if !unbound.is_empty() {
                return Err(ArgumentError::MissingArguments {
                    missing: unbound.into_iter().collect(),
                    at: arg_list.loc(),
                });
            };

            Ok(result)
        }
    }
}
