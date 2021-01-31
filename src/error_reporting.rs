use std::path::Path;

use codespan::Span;
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{
    self,
    termcolor::{ColorChoice, StandardStream},
};
use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    term::termcolor::{Color, ColorSpec},
};

use crate::parser::Error as ParseError;
use crate::semantic_analysis::Error as SemanticError;
use crate::typeinference::result::Error as InferenceError;
use crate::types::Error as TypeError;

pub fn codespan_config() -> codespan_reporting::term::Config {
    let mut primary_label_error = ColorSpec::new();
    primary_label_error
        .set_fg(Some(Color::Red))
        .set_intense(true);

    let style = codespan_reporting::term::Styles {
        primary_label_error,
        ..Default::default()
    };
    codespan_reporting::term::Config {
        styles: style,
        ..Default::default()
    }
}

pub fn report_parse_error(filename: &Path, file_content: &str, err: ParseError) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag = match err {
        ParseError::Eof => Diagnostic::error().with_message("Reached end of file when parsing"),
        ParseError::LexerError(location) => Diagnostic::error()
            .with_message("Lexer error, unexpected symbol")
            .with_labels(vec![Label::primary(file_id, location)]),
        ParseError::UnexpectedToken { got, expected } => {
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
        ParseError::UnmatchedPair { friend, expected } => Diagnostic::error()
            .with_message(format!("Expected closing {}", expected.as_str()))
            .with_labels(vec![
                Label::primary(file_id, friend.span).with_message(format!("to close this"))
            ]),
        ParseError::ExpectedExpression { got } => {
            let message = format!(
                "Unexpected token. Got {} expected expression",
                got.kind.as_str(),
            );

            Diagnostic::error()
                .with_message(message)
                .with_labels(vec![Label::primary(file_id, got.span)
                    .with_message(format!("expected expression here"))])
        }
        ParseError::ExpectedBlock { for_what, got, loc } => {
            let message = format!("Expected a block for {}", for_what);

            let expected_loc = Span::new(loc.span.end(), loc.span.end());
            Diagnostic::error().with_message(message).with_labels(vec![
                Label::primary(file_id, expected_loc).with_message("expected block here"),
                Label::primary(file_id, got.span).with_message("found this instead"),
                Label::secondary(file_id, loc.span).with_message(format!("for this {}", for_what)),
            ])
        }
    };

    let writer = StandardStream::stderr(ColorChoice::Always);

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
}

pub fn report_semantic_error(filename: &Path, file_content: &str, err: SemanticError) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag = match err {
        SemanticError::UndefinedPath(path) => {
            let (path, span) = path.split();
            Diagnostic::error()
                .with_message(format!("Use of undeclared name `{}`", path))
                .with_labels(vec![Label::primary(file_id, span)])
        }
        SemanticError::DuplicateTypeVariable { found, previously } => Diagnostic::error()
            .with_message(format!("Duplicate typename: `{}`", found.inner))
            .with_labels(vec![
                Label::primary(file_id, found.span).with_message("Duplicate typename"),
                Label::secondary(file_id, previously.span).with_message("Previously used here"),
            ]),
        SemanticError::InvalidType(err, loc) => match err {
            TypeError::UnknownTypeName(name) => {
                let (name, span) = name.split();
                Diagnostic::error()
                    .with_message(format!("Unknown type name `{}`", name))
                    .with_labels(vec![Label::primary(file_id, span)])
            }
            TypeError::BitWidthRequired(name) => Diagnostic::error()
                .with_message(format!("{} requires a bit width", name))
                .with_labels(vec![Label::primary(file_id, loc.span)])
                .with_notes(vec![format!("Try using `{}[<width>]`", name)]),
            TypeError::NamedTypesUnsupported => Diagnostic::error()
                .with_message("Types with arbitrary names are unsupported")
                .with_labels(vec![Label::primary(file_id, loc.span)
                    .with_message("Types with arbitrary names are unsupported")]),
            TypeError::NonLiteralTypeSize(loc) => Diagnostic::error()
                .with_message("Types with non-literals generic parameters are unsupported")
                .with_labels(vec![Label::primary(file_id, loc.span)]),
            TypeError::GenericNonIntegersUnsupported(loc) => Diagnostic::error()
                .with_message("Arbitrary generics are unsupported")
                .with_labels(vec![Label::primary(file_id, loc.span)]),
        },
    };

    let writer = StandardStream::stderr(ColorChoice::Always);

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
}

pub fn report_typeinference_error(filename: &Path, file_content: &str, err: InferenceError) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag = match err {
        InferenceError::GenericTypeInstanciation => todo![],
        InferenceError::UnknownType(expr) => Diagnostic::error()
            .with_message(format!(
                "Tried looking up the type of {:?} but it was not found",
                expr
            ))
            .with_notes(vec!["This is an internal compiler error".to_string()]),
        InferenceError::TypeMissmatch(lhs, rhs) => Diagnostic::error()
            .with_message(format!(
                "Type missmatch. {} is incompatible with {}",
                lhs, rhs
            ))
            .with_notes(vec!["This is an internal compiler error".to_string()]),
        InferenceError::EntityOutputTypeMissmatch {
            expected,
            got,
            type_spec,
            output_expr,
        } => Diagnostic::error()
            .with_message(format!("Type error"))
            .with_labels(vec![
                Label::primary(file_id, output_expr.loc().span)
                    .with_message(format!("Found type {}", got)),
                Label::secondary(file_id, type_spec.loc().span)
                    .with_message(format!("{} type specified here", expected)),
            ])
            .with_notes(vec![
                format!("Expected: {}", expected),
                format!("     Got: {}", got),
            ]),
        InferenceError::UnspecifiedTypeError { expected, got, loc } => Diagnostic::error()
            .with_message(format!("Expected type {}, got {}", expected, got))
            .with_labels(vec![Label::primary(file_id, loc.loc().span)
                .with_message(format!("Expected {}", expected))]),
        InferenceError::IntLiteralIncompatible { .. } => {
            todo! {}
        }
        InferenceError::NonBooleanCondition { got, loc } => Diagnostic::error()
            .with_message(format!("If condition must be a bool, got {}", got))
            .with_labels(vec![
                Label::primary(file_id, loc.loc().span).with_message("Expected boolean")
            ])
            .with_notes(vec![
                format!("Expected: {}", crate::types::Type::Bool),
                format!("     Got: {}", got),
            ]),
        InferenceError::IfConditionMissmatch {
            expected,
            got,
            first_branch,
            incorrect_branch,
        } => Diagnostic::error()
            .with_message(format!("If branches have incompatible type"))
            .with_labels(vec![
                Label::primary(file_id, first_branch.loc().span)
                    .with_message(format!("This branch has type {}", expected)),
                Label::primary(file_id, incorrect_branch.loc().span)
                    .with_message(format!("But this one has type {}", got)),
            ])
            .with_notes(vec![
                format!("Expected: {}", expected),
                format!("     Got: {}", got),
            ]),
    };

    let writer = StandardStream::stderr(ColorChoice::Always);

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
}
