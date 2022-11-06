use codespan_reporting::term::termcolor::Buffer;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};

use crate::Error;

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, diag_handler: &mut DiagHandler) {
        match self {
            Error::ArgumentError(e) => {
                e.report(buffer, code, diag_handler);
            }
            Error::LookupError(e) => {
                e.report(buffer, code, diag_handler);
            }
            Error::SpadeDiagnostic(diag) => {
                diag_handler.emit(diag, buffer, code);
            }
        }
    }
}
