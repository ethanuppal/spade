use codespan_reporting::{diagnostic::Diagnostic, term::termcolor::Buffer};
use spade_common::location_info::Loc;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};
use thiserror::Error;

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("Unit")]
    Unit,

    #[error("Unification Type Error")]
    TypeError(Loc<spade_typeinference::error::UnificationError>),
    #[error("The wordlength isn't what we infered it to")]
    WordlengthMismatch(u32, u32, Loc<()>),
}

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, diag_handler: &mut DiagHandler) {
        let diag = match self {
            Error::Unit => Diagnostic::error().with_message(format!("This is an error!")),

            Error::TypeError(_e) => Diagnostic::error().with_message(format!(
                "Failed to unify some types while infering wordlengths"
            )),

            Error::WordlengthMismatch(ty, inf, loc) if ty > inf => Diagnostic::error().with_message(format!(
                "The specified wordlength is larger than it has to be (you specified {} bits), but you only need {} bits",
                ty, inf
            )),
            Error::WordlengthMismatch(ty, inf, loc) if ty < inf => Diagnostic::error().with_message(format!(
                "The specified wordlength is too small (you specified {} bits), but it needs to hold {} bits",
                ty, inf
            )),
            Error::WordlengthMismatch(ty, inf, _loc) => panic!("Invalid error, these are the same size! {}, {}", ty, inf),
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
