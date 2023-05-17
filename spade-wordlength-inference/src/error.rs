use codespan_reporting::{diagnostic::Diagnostic, term::termcolor::Buffer};
use spade_common::location_info::{AsLabel, Loc};
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};
use thiserror::Error;

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("Unit")]
    Unit,

    #[error("Unification Type Error")]
    TypeError(Loc<spade_typeinference::error::UnificationError>),
    #[error("The wordlength isn't what we infered it to")]
    WordlengthMismatch(Loc<u32>, Loc<u32>),
}

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, _diag_handler: &mut DiagHandler) {
        let diag = match self {
            Error::Unit => Diagnostic::error().with_message(format!("This is an error!")),

            Error::TypeError(_e) => Diagnostic::error().with_message(format!(
                "Failed to unify some types while infering wordlengths"
            )),

            Error::WordlengthMismatch(ty, inf) if ty.is_same_loc(inf) => Diagnostic::error()
                .with_labels(vec![ty.primary_label().with_message(format!(
                    "This expression requires {} bits but claims to need {} bits",
                    ty.inner, inf.inner
                ))]),

            Error::WordlengthMismatch(ty, inf) => Diagnostic::error()
                .with_message(format!("The size of these ints does not add up"))
                .with_labels(vec![
                    ty.primary_label()
                        .with_message(format!("Here we require {} bits", ty.inner)),
                    inf.primary_label()
                        .with_message(format!("And here we require {} bits", inf.inner)),
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
