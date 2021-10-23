use crate::lexer::TokenKind;
use crate::{Error, Token};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{
    codespan_config, color_choice, AsLabel, CodeBundle, CompilationError,
};

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

fn unexpected_token_message<'a>(got: &TokenKind, expected_list: &str) -> String {
    format!("Unexpected `{}`, expected {}", got.as_str(), expected_list,)
}

fn unexpected_token<'a>(
    file_id: usize,
    got: Token,
    expected: impl IntoIterator<Item = &'a str>,
) -> Diagnostic<usize> {
    let expected_list = unexpected_token_list(expected);
    let message = unexpected_token_message(&got.kind, &expected_list);

    Diagnostic::error().with_message(message).with_labels(vec![
        Label::primary(file_id, got.span).with_message(format!("expected {}", expected_list))
    ])
}

impl CompilationError for Error {
    fn report(self, code: &CodeBundle, no_color: bool) {
        let diag = match self {
            Error::Eof => Diagnostic::error().with_message("Reached end of file when parsing"),
            Error::LexerError(file_id, location) => Diagnostic::error()
                .with_message("Lexer error, unexpected symbol")
                .with_labels(vec![Label::primary(file_id, location)]),
            Error::UnexpectedToken { got, expected } => {
                unexpected_token(got.file_id, got, expected)
            }
            Error::UnexpectedEndOfArgList { got, expected } => {
                unexpected_token(got.file_id, got, expected.iter().map(|tok| tok.as_str()))
            }
            Error::UnmatchedPair {
                friend,
                expected,
                got,
            } => Diagnostic::error()
                .with_message(format!(
                    "Expected closing `{}`, got `{}`",
                    expected.as_str(),
                    got.kind.as_str()
                ))
                .with_labels(vec![
                    Label::primary(got.file_id, got.span)
                        .with_message(format!("Expected `{}`", expected.as_str())),
                    friend
                        .secondary_label()
                        .with_message(format!("to close this")),
                ]),
            Error::ExpectedExpression { got } => {
                let message = format!("Unexpected `{}`, expected expression", got.kind.as_str(),);

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(got.file_id, got.span)
                        .with_message(format!("expected expression here"))])
            }
            Error::ExpectedBlock { for_what, got, loc } => {
                let message = format!("Expected a block for {}", for_what);

                Diagnostic::error().with_message(message).with_labels(vec![
                    loc.primary_label().with_message("expected block here"),
                    got.primary_label().with_message("found this instead"),
                    loc.secondary_label()
                        .with_message(format!("for this {}", for_what)),
                ])
            }
            Error::MissingTupleIndex { hash_loc } => {
                let message = format!("Expected an index after #");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![hash_loc
                        .primary_label()
                        .with_message("expected index")])
            }
            Error::ExpectedArgumentList(for_what) => {
                let message = format!("Expected arguments for {}", for_what);

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![for_what
                        .primary_label()
                        .with_message("Expected an argument list")])
            }
            Error::ExpectedPipelineDepth { got } => {
                let message = format!("Expected pipeline depth");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![got
                        .primary_label()
                        .with_message("Expected pipeline depth")])
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
                .with_labels(vec![found.primary_label().with_message("Expected a type")]),
            Error::ExpectedExpressionOrStage { got } => {
                let message = format!("Expected return expression or pipeline stage");

                Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![got
                        .primary_label()
                        .with_message("Expected expression or stage")])
                    .with_notes(vec![format!("Found {}", got.kind.as_str())])
            }
            Error::EmptyDeclStatement { at } => Diagnostic::error()
                .with_message("Found empty decl statement")
                .with_labels(vec![at
                    .primary_label()
                    .with_message("decl doesn't declare anything")]),
        };

        let writer = StandardStream::stderr(color_choice(no_color));

        term::emit(&mut writer.lock(), &codespan_config(), &code.files, &diag).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unexpected_token_works_for_single_token() {
        let got = crate::lexer::TokenKind::Assignment;
        let expected_list = unexpected_token_list(vec!["=="]);
        let result = unexpected_token_message(&got, &expected_list);
        assert_eq!(result, "Unexpected `=`, expected `==`");
    }

    #[test]
    fn unexpected_token_works_for_multiple_tokens() {
        let got = crate::lexer::TokenKind::Assignment;
        let expected_list = unexpected_token_list(vec!["x", "y", "z"]);
        let result = unexpected_token_message(&got, &expected_list);
        assert_eq!(result, "Unexpected `=`, expected `x`, `y`, or `z`");
    }
}
