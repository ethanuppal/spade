use std::path::Path;

use crate::Error;
use codespan::Span;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{codespan_config, color_choice, CompilationError};

impl CompilationError for Error {
    fn report(self, filename: &Path, file_content: &str, no_color: bool) {
        let mut files = SimpleFiles::new();
        let file_id = files.add(filename.to_string_lossy(), file_content);
        let diag = match self {
            Error::Eof => Diagnostic::error().with_message("Reached end of file when parsing"),
            Error::LexerError(location) => Diagnostic::error()
                .with_message("Lexer error, unexpected symbol")
                .with_labels(vec![Label::primary(file_id, location)]),
            Error::UnexpectedToken { got, expected } => {
                let expected_list = format!(
                    "[{}]",
                    expected
                        .iter()
                        .map(|s| s.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                let message = format!(
                    "Unexpected token. Got `{}`, expected one of {}",
                    got.kind.as_str(),
                    expected_list,
                );

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(file_id, got.span)
                        .with_message(format!("expected one of {}", expected_list))])
            }
            Error::UnmatchedPair { friend, expected } => Diagnostic::error()
                .with_message(format!("Expected closing {}", expected.as_str()))
                .with_labels(vec![
                    Label::primary(file_id, friend.span).with_message(format!("to close this"))
                ]),
            Error::ExpectedExpression { got } => {
                let message = format!(
                    "Unexpected token. Got {} expected expression",
                    got.kind.as_str(),
                );

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(file_id, got.span)
                        .with_message(format!("expected expression here"))])
            }
            Error::ExpectedBlock { for_what, got, loc } => {
                let message = format!("Expected a block for {}", for_what);

                let expected_loc = Span::new(loc.span.end(), loc.span.end());
                Diagnostic::error().with_message(message).with_labels(vec![
                    Label::primary(file_id, expected_loc).with_message("expected block here"),
                    Label::primary(file_id, got.span).with_message("found this instead"),
                    Label::secondary(file_id, loc.span)
                        .with_message(format!("for this {}", for_what)),
                ])
            }
            Error::MissingTupleIndex { hash_loc } => {
                let message = format!("Expected an index after #");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![
                        Label::primary(file_id, hash_loc.span).with_message("expected index")
                    ])
            }
            Error::ExpectedArgumentList(for_what) => {
                let message = format!("Expected arguments for {}", for_what);

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(file_id, for_what.span)
                        .with_message("Expected an argument list")])
            }
            Error::ExpectedPipelineDepth { got } => {
                let message = format!("Expected pipeline depth");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![
                        Label::primary(file_id, got.span).with_message("Expected pipeline depth")
                    ])
                    .with_notes(vec![
                        format!("Found {}", got.kind.as_str()),
                        format!("Pipeline depth can only be fixed integers"),
                    ])
            }
            Error::ExpectedType(found) => Diagnostic::error()
                .with_message(format!(
                    "Unexpected token. Got `{}`, expected type",
                    found.kind.as_str()
                ))
                .with_labels(vec![
                    Label::primary(file_id, found.span).with_message("Expected a type")
                ]),
            Error::ExpectedExpressionOrStage { got } => {
                let message = format!("Expected return expression or pipeline stage");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(file_id, got.span)
                        .with_message("Expected expression or stage")])
                    .with_notes(vec![format!("Found {}", got.kind.as_str())])
            }
        };

        let writer = StandardStream::stderr(color_choice(no_color));

        term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
    }
}
