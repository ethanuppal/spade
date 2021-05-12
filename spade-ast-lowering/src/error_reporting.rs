use std::path::Path;

use crate::Error;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{codespan_config, color_choice, CompilationError};
use spade_hir::symbol_table::Error as LookupError;

impl CompilationError for Error {
    fn report(self, filename: &Path, file_content: &str, no_color: bool) {
        let mut files = SimpleFiles::new();
        let file_id = files.add(filename.to_string_lossy(), file_content);
        let diag = match self {
            Error::DuplicateTypeVariable { found, previously } => Diagnostic::error()
                .with_message(format!("Duplicate typename: `{}`", found.inner))
                .with_labels(vec![
                    Label::primary(file_id, found.span).with_message("Duplicate typename"),
                    Label::secondary(file_id, previously.span).with_message("Previously used here"),
                ]),
            Error::LookupError(LookupError::NoSuchSymbol(path)) => Diagnostic::error()
                .with_message(format!("Use of undeclared name {}", path))
                .with_labels(vec![
                    Label::primary(file_id, path.span).with_message("Undeclared name")
                ]),
            Error::LookupError(LookupError::NotATypeSymbol(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a type", path))
                .with_labels(vec![
                    Label::primary(file_id, path.span).with_message(format!("Expected type")),
                    Label::secondary(file_id, got.loc().span).with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAVariable(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a variable", path))
                .with_labels(vec![
                    Label::primary(file_id, path.span).with_message(format!("Expected variable")),
                    Label::secondary(file_id, got.loc().span).with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAnEntity(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be an enity", path))
                .with_labels(vec![
                    Label::primary(file_id, path.span).with_message(format!("Expected entity")),
                    Label::secondary(file_id, got.loc().span).with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAPipeline(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a pipeline", path))
                .with_labels(vec![
                    Label::primary(file_id, path.span).with_message(format!("Expected pipeline")),
                    Label::secondary(file_id, got.loc().span).with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAFunction(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a function", path))
                .with_labels(vec![
                    Label::primary(file_id, path.span).with_message(format!("Expected function")),
                    Label::secondary(file_id, got.loc().span).with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::ArgumentListLenghtMismatch { expected, got, at } => Diagnostic::error()
                .with_message(format!("Expected {} arguments, got {}", expected, got))
                .with_labels(vec![Label::primary(file_id, at.span)
                    .with_message(format!("Expected {} arguments", expected))]),
            Error::DuplicateNamedBindings { new, prev_loc } => Diagnostic::error()
                .with_message(format!("Multiple bindings to {}", new))
                .with_labels(vec![Label::primary(file_id, prev_loc.span)
                    .with_message(format!("previously bound here"))]),
            Error::NoSuchArgument { name } => Diagnostic::error()
                .with_message(format!("{}: No such argument to", name))
                .with_labels(vec![
                    Label::primary(file_id, name.span).with_message(format!("No such argument"))
                ]),
            Error::MissingArguments { missing, at } => {
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
                    .with_labels(vec![
                        Label::primary(file_id, at.span)
                            .with_message(format!("Missing {}", plural)),
                        Label::secondary(file_id, at.span)
                            .with_message(format!("Missing {}", arg_list)),
                    ])
            }
            Error::MissingPipelineReturn { in_stage } => Diagnostic::error()
                .with_message(format!("Missing return expression"))
                .with_labels(vec![Label::primary(file_id, in_stage.span)
                    .with_message(format!("Missing return expression"))])
                .with_notes(vec![format!(
                    "The last stage of a pipeline must return a value"
                )]),
            Error::NoPipelineStages { pipeline } => Diagnostic::error()
                .with_message("Missing pipeline stages")
                .with_labels(vec![Label::primary(file_id, pipeline.span)
                    .with_message(format!("Pipelien must have at least one stage"))]),
            Error::IncorrectStageCount {
                got,
                expected,
                pipeline,
            } => Diagnostic::error()
                .with_message(format!("Expected {} pipeline stages", expected))
                .with_labels(vec![
                    Label::primary(file_id, pipeline.span)
                        .with_message(format!("Found {} stages", got)),
                    Label::secondary(file_id, expected.span)
                        .with_message(format!("{} specified here", expected)),
                ]),
            Error::EarlyPipelineReturn { expression } => Diagnostic::error()
                .with_message(format!("Unexpected return expression"))
                .with_labels(vec![Label::primary(file_id, expression.span)
                    .with_message(format!("Did not expect an value in this stage"))])
                .with_notes(vec![format!(
                    "Only the last stage of a pipeline can return values"
                )]),
            Error::PipelineDepthMissmatch { expected, got } => Diagnostic::error()
                .with_message(format!(
                    "Pipeline depth mismatch. Expected {} got {}",
                    expected, got
                ))
                .with_labels(vec![Label::primary(file_id, got.span)
                    .with_message(format!("Expected {}", expected))]),
            Error::MissingPipelineClock { at_loc } => Diagnostic::error()
                .with_message(format!("Missing clock argument."))
                .with_labels(vec![Label::primary(file_id, at_loc.span)
                    .with_message(format!("Expected clock argument"))])
                .with_notes(vec![format!("All pipelines take a clock as an argument")]),
            Error::GenericsGivenForGeneric { at_loc, for_type } => Diagnostic::error()
                .with_message("Generic arguments given for a generic type")
                .with_labels(vec![Label::primary(file_id, at_loc.span)
                    .with_message(format!("{} is a generic type", for_type))])
                .with_notes(vec![format!(
                    "A generic argument can not have generic types"
                )]),
        };

        let writer = StandardStream::stderr(color_choice(no_color));

        term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
    }
}
