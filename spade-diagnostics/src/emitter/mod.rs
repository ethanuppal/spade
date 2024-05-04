use codespan_reporting::term::termcolor::Buffer;

use crate::diagnostic::Diagnostic;
use crate::CodeBundle;

pub use codespan_emitter::{codespan_config, CodespanEmitter};

pub mod codespan_emitter;
mod panik;

/// Something that can format and emit diagnostics.
pub trait Emitter {
    /// Emit a diagnostic, e.g. print it.
    fn emit_diagnostic(&mut self, diag: &Diagnostic, buffer: &mut Buffer, code: &CodeBundle);
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.labels.message.as_str())
    }
}

impl std::error::Error for Diagnostic {}
