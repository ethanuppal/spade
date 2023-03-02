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

// Glue so we can stuff our fancy new diagnostics in a thiserror. This should be removed when we
// don't have any Error-enums left.

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unimplemented!()
    }
}

impl std::error::Error for Diagnostic {}
