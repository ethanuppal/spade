use codespan_reporting::{diagnostic::Diagnostic, term::termcolor::Buffer};
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};
use thiserror::Error;

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("Unit")]
    Unit,
}

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, diag_handler: &mut DiagHandler) {
        let diag = match self {
            Error::Unit => Diagnostic::error().with_message(format!("This is an error!")),
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
