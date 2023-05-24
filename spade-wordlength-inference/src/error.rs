use codespan_reporting::{diagnostic::Diagnostic, term::termcolor::Buffer};
use spade_common::location_info::{AsLabel, Loc};
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};
use thiserror::Error;

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("Unification Type Error")]
    TypeError(Loc<spade_typeinference::error::UnificationError>),
    #[error("The wordlength isn't what we infered it to")]
    WordlengthMismatch {
        infered: Loc<u32>,
        typechecked: Loc<u32>,
    },
}

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, _diag_handler: &mut DiagHandler) {
        let diag = match self {
            Error::TypeError(_e) => Diagnostic::error().with_message(format!(
                "Failed to unify some types while infering wordlengths"
            )),

            Error::WordlengthMismatch {
                infered,
                typechecked,
            } if infered.is_same_loc(typechecked) => {
                Diagnostic::error().with_labels(vec![typechecked.primary_label().with_message(
                    format!(
                    "This expression requires {} bits but the typechecker claims it needs {} bits",
                    infered.inner, typechecked.inner
                ),
                )])
            }

            Error::WordlengthMismatch {
                infered,
                typechecked,
            } => Diagnostic::error()
                .with_message(format!("The size of these ints does not add up"))
                .with_labels(vec![
                    typechecked
                        .primary_label()
                        .with_message(format!("Here we require {} bits", typechecked.inner)),
                    infered
                        .primary_label()
                        .with_message(format!("But the compiler infered {} bits", infered.inner)),
                ]),
        };

        codespan_reporting::term::emit(
            buffer,
            &spade_diagnostics::emitter::codespan_config(),
            &code.files,
            &diag,
        )
        .unwrap()
    }
}

pub type Result<T> = std::result::Result<T, Error>;
