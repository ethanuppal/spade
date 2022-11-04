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
            Error::DuplicateTypeVariable { found, previously } => Diagnostic::error()
                .with_message(format!("Duplicate typename: `{}`", found.inner))
                .with_labels(vec![
                    found.primary_label().with_message("Duplicate typename"),
                    previously
                        .secondary_label()
                        .with_message("Previously used here"),
                ]),
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
            Error::IncorrectStageCount {
                got,
                expected,
                pipeline,
            } => Diagnostic::error()
                .with_message(format!("Expected {} pipeline stages", expected))
                .with_labels(vec![
                    pipeline
                        .primary_label()
                        .with_message(format!("Found {} stages", got)),
                    expected
                        .secondary_label()
                        .with_message(format!("{} specified here", expected)),
                ]),
            Error::EarlyPipelineReturn { expression } => Diagnostic::error()
                .with_message(format!("Unexpected return expression"))
                .with_labels(vec![expression
                    .primary_label()
                    .with_message(format!("Did not expect an value in this stage"))])
                .with_notes(vec![format!(
                    "Only the last stage of a pipeline can return values"
                )]),
            Error::MissingPipelineClock { at_loc } => Diagnostic::error()
                .with_message(format!("Missing clock argument."))
                .with_labels(vec![at_loc
                    .primary_label()
                    .with_message(format!("Expected clock argument"))])
                .with_notes(vec![format!("All pipelines take a clock as an argument")]),
            Error::DuplicatePipelineStage { stage, previous } => Diagnostic::error()
                .with_message(format!("Stage {stage} was already defined"))
                .with_labels(vec![
                    stage
                        .primary_label()
                        .with_message(format!("duplicate pipeline stage")),
                    previous
                        .secondary_label()
                        .with_message("Previous definition"),
                ]),
            Error::MultipleStageLabels { new, previous } => Diagnostic::error()
                .with_message(format!("Stage already has label {previous}"))
                .with_labels(vec![
                    new.primary_label().with_message(format!("Duplicate label")),
                    previous
                        .secondary_label()
                        .with_message(format!("Previously labeled here")),
                ]),
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
            Error::UndefinedDeclaration(name) => Diagnostic::error()
                .with_message(format!("{name} is declared but not defined"))
                .with_labels(vec![name
                    .primary_label()
                    .with_message("declaration without definition")])
                .with_notes(vec![format!(
                    "Consider defining {name} with a let or reg binding"
                )]),
            Error::SpadeDiagnostic(diag) => {
                return diag_handler.emit(diag, buffer, code);
            }
        };

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}
