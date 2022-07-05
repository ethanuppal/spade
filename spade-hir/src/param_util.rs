// Utilities related to argument matching between callers and callees. Lives in spade-hir
// because this is required twice in the compilation process: first during type inference,
// and then again during hir lowering

use std::collections::HashSet;

use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::term::{self, termcolor::Buffer};
use thiserror::Error;

use spade_common::error_reporting::{codespan_config, AsLabel, CodeBundle, CompilationError};
use spade_common::{location_info::Loc, name::Identifier};

use crate::expression::NamedArgument;
use crate::{ArgumentList, Expression, ParameterList, TypeSpec};

#[derive(Error, Debug, PartialEq, Clone)]
pub enum ArgumentError {
    #[error("Argument list length mismatch, expected {expected} got {got}")]
    ArgumentListLenghtMismatch {
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

impl CompilationError for ArgumentError {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle) {
        let diag = match self {
            Self::ArgumentListLenghtMismatch { expected, got, at } => Diagnostic::error()
                .with_message(format!("Expected {} arguments, got {}", expected, got))
                .with_labels(vec![at
                    .primary_label()
                    .with_message(format!("Expected {} arguments", expected))]),
            Self::NoSuchArgument { name } => Diagnostic::error()
                .with_message(format!("No such argument: {}", name))
                .with_labels(vec![name
                    .primary_label()
                    .with_message(format!("No such argument"))]),
            Self::MissingArguments { missing, at } => {
                let plural = if missing.len() == 1 {
                    "argument"
                } else {
                    "arguments"
                };

                let arg_list = missing
                    .iter()
                    .map(|i| format!("{}", i))
                    .collect::<Vec<_>>()
                    .join(", ");

                Diagnostic::error()
                    .with_message(format!("Missing {}: {}", plural, arg_list))
                    .with_labels(vec![at
                        .primary_label()
                        .with_message(format!("Missing {}: {}", plural, arg_list))])
            }
            Self::DuplicateNamedBindings { new, prev_loc } => Diagnostic::error()
                .with_message(format!("{} specified multiple times", new))
                .with_labels(vec![
                    new.primary_label().with_message("Later specified here"),
                    prev_loc
                        .secondary_label()
                        .with_message(format!("First specified here")),
                ]),
        };

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
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
) -> Result<Vec<Argument<'a>>, ArgumentError> {
    match &arg_list.inner {
        ArgumentList::Positional(inner) => {
            if inner.len() != params.0.len() {
                return Err(ArgumentError::ArgumentListLenghtMismatch {
                    expected: params.0.len(),
                    got: inner.len(),
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
                            target_type: &target_type,
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
