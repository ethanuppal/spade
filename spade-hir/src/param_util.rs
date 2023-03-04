// Utilities related to argument matching between callers and callees. Lives in spade-hir
// because this is required twice in the compilation process: first during type inference,
// and then again during hir lowering

use std::collections::HashSet;

use spade_diagnostics::Diagnostic;
use thiserror::Error;

use spade_common::{location_info::Loc, name::Identifier};

use crate::expression::NamedArgument;
use crate::{ArgumentList, Expression, ParameterList, TypeSpec};

#[derive(Error, Debug, PartialEq, Clone)]
pub enum ArgumentError {
    #[error("Argument list length mismatch, expected {expected} got {got}")]
    ArgumentListLengthMismatch {
        expected: usize,
        got: usize,
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
            ArgumentError::ArgumentListLengthMismatch { expected, got, at } => {
                Diagnostic::error(at, format!("Expected {expected} arguments, got {got}"))
                    .primary_label(format!("Expected {expected} arguments"))
            }
            ArgumentError::NoSuchArgument { name } => {
                Diagnostic::error(&name, format!("No such argument: {name}"))
                    .primary_label("No such argument")
            }
            ArgumentError::MissingArguments { mut missing, at } => {
                let plural = if missing.len() == 1 {
                    "argument"
                } else {
                    "arguments"
                };

                missing.sort_by_key(|arg| arg.0.clone());

                let arg_list = missing
                    .iter()
                    .map(|i| format!("{i}"))
                    .collect::<Vec<_>>()
                    .join(", ");

                Diagnostic::error(at, format!("Missing {plural}: {arg_list}"))
                    .primary_label(format!("Missing {plural}: {arg_list}"))
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
            if inner.len() != params.0.len() {
                return Err(ArgumentError::ArgumentListLengthMismatch {
                    expected: params.0.len() - if is_method { 1 } else { 0 },
                    got: inner.len() - if is_method { 1 } else { 0 },
                    at: arg_list.loc(),
                });
            }

            Ok(inner
                .iter()
                .zip(params.0.iter())
                .map(|(arg, param)| Argument {
                    target: &param.0,
                    target_type: &param.1,
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
                .map(|(ident, _)| ident.inner.clone())
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
