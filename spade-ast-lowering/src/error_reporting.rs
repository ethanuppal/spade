use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::term::{self, termcolor::Buffer};
use spade_common::location_info::AsLabel;
use spade_diagnostics::emitter::codespan_config;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};
use spade_hir::symbol_table::{DeclarationError, UniqueNameError};

use crate::Error;

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, diag_handler: &mut DiagHandler) {
        match self {
            Error::ArgumentError(e) => {
                e.report(buffer, code, diag_handler);
                return;
            }
            Error::LookupError(e) => {
                e.report(buffer, code, diag_handler);
                return;
            }
            _ => {}
        }
        let diag = match self {
            Error::ArgumentError(_) | Error::LookupError(_) => unreachable!("Already handled"),
            Error::DeclarationError(DeclarationError::DuplicateDeclaration { old, new }) => {
                Diagnostic::error()
                    .with_message(format!("A previous declaration of {} exists", new))
                    .with_labels(vec![
                        new.primary_label()
                            .with_message(format!("{} was declared more than once", new)),
                        old.primary_label()
                            .with_message(format!("Previously declared here")),
                    ])
            }
            Error::UniquenessError(UniqueNameError::MultipleDefinitions { new, prev }) => {
                Diagnostic::error()
                    .with_message(format!("Multiple definitions of {new}"))
                    .with_labels(vec![
                        new.primary_label()
                            .with_message(format!("Multiple items named {new}")),
                        prev.secondary_label()
                            .with_message(format!("Previous definition here")),
                    ])
            }
            Error::EarlyPipelineReturn { expression } => Diagnostic::error()
                .with_message(format!("Unexpected return expression"))
                .with_labels(vec![expression
                    .primary_label()
                    .with_message(format!("Did not expect an value in this stage"))])
                .with_notes(vec![format!(
                    "Only the last stage of a pipeline can return values"
                )]),
            Error::DeclarationOfNonReg {
                at,
                declaration_location,
            } => Diagnostic::error()
                .with_message("Declared variables can only be defined by registers")
                .with_labels(vec![
                    at.primary_label().with_message(format!("Not a register")),
                    declaration_location
                        .secondary_label()
                        .with_message(format!("{} declared here", at)),
                ]),
            Error::SpadeDiagnostic(diag) => {
                return diag_handler.emit(diag, buffer, code);
            }
        };

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}
