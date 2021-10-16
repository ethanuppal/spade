use std::path::Path;

use crate::{Error, Token};
use codespan::Span;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{codespan_config, color_choice, CompilationError};

fn unexpected_token_list<'a>(expected: impl IntoIterator<Item = &'a str>) -> String {
    let expected = expected
        .into_iter()
        .map(|s| format!("`{}`", s))
        .collect::<Vec<_>>();

    let count = expected.len();
    if count == 1 {
        format!("{}", expected[0])
    } else {
        format!(
            "{}, or {}",
            expected[0..(count - 1)].join(", "),
            expected[count - 1]
        )
    }
}

fn unexpected_token_message<'a>(got: &Token, expected_list: &str) -> String {
    format!(
        "Unexpected `{}`, expected {}",
        got.kind.as_str(),
        expected_list,
    )
}

fn unexpected_token<'a>(
    file_id: usize,
    got: Token,
    expected: impl IntoIterator<Item = &'a str>,
) -> Diagnostic<usize> {
    let expected_list = unexpected_token_list(expected);
    let message = unexpected_token_message(&got, &expected_list);

    Diagnostic::error().with_message(message).with_labels(vec![
        Label::primary(file_id, got.span).with_message(format!("expected {}", expected_list))
    ])
}

impl CompilationError for Error {
    fn report(self, filename: &Path, file_content: &str, no_color: bool) {
        let mut files = SimpleFiles::new();
        let file_id = files.add(filename.to_string_lossy(), file_content);
        let diag = match self {
            Error::Eof => Diagnostic::error().with_message("Reached end of file when parsing"),
            Error::LexerError(location) => Diagnostic::error()
                .with_message("Lexer error, unexpected symbol")
                .with_labels(vec![Label::primary(file_id, location)]),
            Error::UnexpectedToken { got, expected } => unexpected_token(file_id, got, expected),
            Error::UnexpectedEndOfArgList { got, expected } => {
                unexpected_token(file_id, got, expected.iter().map(|tok| tok.as_str()))
            }
            Error::UnmatchedPair { friend, expected } => Diagnostic::error()
                .with_message(format!("Expected closing {}", expected.as_str()))
                .with_labels(vec![
                    Label::primary(file_id, friend.span).with_message(format!("to close this"))
                ]),
            Error::ExpectedExpression { got } => {
                let message = format!("Unexpected `{}`, expected expression", got.kind.as_str(),);

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
            Error::EmptyDeclStatement { at } => Diagnostic::error()
                .with_message("Found empty decl statement")
                .with_labels(vec![
                    Label::primary(file_id, at.span).with_message("decl doesn't declare anything")
                ]),
        };

        let writer = StandardStream::stderr(color_choice(no_color));

        term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unexpected_token_works_for_single_token() {
        let got = Token {
            span: 0..0,
            kind: crate::lexer::TokenKind::Assignment,
        };
        let expected_list = unexpected_token_list(vec!["=="]);
        let result = unexpected_token_message(&got, &expected_list);
        assert_eq!(result, "Unexpected `=`, expected `==`");
    }

    #[test]
    fn unexpected_token_works_for_multiple_tokens() {
        let got = Token {
            span: 0..0,
            kind: crate::lexer::TokenKind::Assignment,
        };
        let expected_list = unexpected_token_list(vec!["x", "y", "z"]);
        let result = unexpected_token_message(&got, &expected_list);
        assert_eq!(result, "Unexpected `=`, expected `x`, `y`, or `z`");
    }
}
