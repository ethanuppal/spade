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

use crate::semantic_analysis::Error as SemanticError;
use crate::symbol_table::Error as LookupError;
use crate::typeinference::result::Error as InferenceError;
use crate::codegen::Error as CodegenError;
use crate::{parser::Error as ParseError, typeinference::result::UnificationTrace};

fn color_choice(no_color: bool) -> ColorChoice {
    if no_color {
        ColorChoice::Never
    } else {
        ColorChoice::Auto
    }
}

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

pub fn report_parse_error(filename: &Path, file_content: &str, err: ParseError, no_color: bool) {
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
        ParseError::MissingTupleIndex { hash_loc } => {
            let message = format!("Expected an index after #");

            Diagnostic::error()
                .with_message(message)
                .with_labels(vec![
                    Label::primary(file_id, hash_loc.span).with_message("expected index")
                ])
        }
    };

    let writer = StandardStream::stderr(color_choice(no_color));

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
}

pub fn report_semantic_error(
    filename: &Path,
    file_content: &str,
    err: SemanticError,
    no_color: bool,
) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag = match err {
        SemanticError::DuplicateTypeVariable { found, previously } => Diagnostic::error()
            .with_message(format!("Duplicate typename: `{}`", found.inner))
            .with_labels(vec![
                Label::primary(file_id, found.span).with_message("Duplicate typename"),
                Label::secondary(file_id, previously.span).with_message("Previously used here"),
            ]),
        SemanticError::LookupError(LookupError::NoSuchSymbol(path)) => Diagnostic::error()
            .with_message(format!("Use of undeclared name {}", path))
            .with_labels(vec![
                Label::primary(file_id, path.span).with_message("Undeclared name")
            ]),
        SemanticError::LookupError(LookupError::NotATypeSymbol(path, got)) => Diagnostic::error()
            .with_message(format!("Expected {} to be a type", path))
            .with_labels(vec![
                Label::primary(file_id, path.span).with_message(format!("Expected type")),
                Label::secondary(file_id, got.loc().span).with_message(format!(
                    "{} is a {}",
                    path,
                    got.kind_string()
                )),
            ]),
        SemanticError::LookupError(LookupError::NotAVariable(path, got)) => Diagnostic::error()
            .with_message(format!("Expected {} to be a variable", path))
            .with_labels(vec![
                Label::primary(file_id, path.span).with_message(format!("Expected variable")),
                Label::secondary(file_id, got.loc().span).with_message(format!(
                    "{} is a {}",
                    path,
                    got.kind_string()
                )),
            ]),
    };

    let writer = StandardStream::stderr(color_choice(no_color));

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
}

pub fn type_missmatch_notes(got: UnificationTrace, expected: UnificationTrace) -> Vec<String> {
    let mut result = vec![];

    result.push(format!("Expected: {}", expected.failing));
    if let Some(_) = got.inside {
        result.push(format!("      in: {}", expected.outer()))
    }
    result.push(format!("     Got: {}", got.failing));
    if let Some(_) = got.inside {
        result.push(format!("      in: {}", got.outer()))
    }
    result
}

pub fn report_typeinference_error(
    filename: &Path,
    file_content: &str,
    err: InferenceError,
    no_color: bool,
) {
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
            .with_notes(type_missmatch_notes(got, expected)),
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
                format!("Expected: {}", "bool"), // TODO: Specify full path to the type
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
            .with_notes(type_missmatch_notes(got, expected)),
        InferenceError::NonClockClock { expected, got, loc } => Diagnostic::error()
            .with_message("Register clock must be a type clock")
            .with_labels(vec![
                Label::primary(file_id, loc.span).with_message(format!("Found type {}", got))
            ])
            .with_notes(type_missmatch_notes(got, expected)),
        InferenceError::NonBoolReset { expected, got, loc } => Diagnostic::error()
            .with_message("Register reset must be a bool")
            .with_labels(vec![
                Label::primary(file_id, loc.span).with_message(format!("Found type {}", got))
            ])
            .with_notes(type_missmatch_notes(got, expected)),
        InferenceError::RegisterResetMissmatch { expected, got, loc } => Diagnostic::error()
            .with_message("Register reset value missmatch")
            .with_labels(vec![
                Label::primary(file_id, loc.span).with_message(format!("Found type {}", got))
            ])
            .with_notes(type_missmatch_notes(got, expected)),
        InferenceError::UnspecedEntityOutputTypeMissmatch {
            expected,
            got,
            output_expr,
        } => Diagnostic::error()
            .with_message(format!("Output type missmatch"))
            .with_labels(vec![Label::primary(file_id, output_expr.loc().span)
                .with_message(format!("Found type {}", got))])
            .with_notes(type_missmatch_notes(got, expected)),
        InferenceError::TupleIndexOfGeneric { loc } => Diagnostic::error()
            .with_message(format!("Type of tuple indexee must be known at this point"))
            .with_labels(vec![
                Label::primary(file_id, loc.span).with_message("The type of this must be known")
            ]),
        InferenceError::TupleIndexOfNonTuple { got, loc } => Diagnostic::error()
            .with_message(format!("Attempt to use tuple indexing on non-tuple"))
            .with_labels(vec![
                Label::primary(file_id, loc.span).with_message(format!("expected tuple"))
            ])
            .with_notes(vec![
                format!("Expected: tuple"),
                format!("     Got: {}", got),
            ]),
        InferenceError::TupleIndexOutOfBounds { index, actual_size } => Diagnostic::error()
            .with_message(format!("Tuple index out of bounds"))
            .with_labels(vec![Label::primary(file_id, index.span)
                .with_message(format!("Tuple only has {} elements", actual_size))])
            .with_notes(vec![
                format!("     Index: {}", index),
                format!("Tuple size: {}", actual_size),
            ]),
    };

    let writer = StandardStream::stderr(color_choice(no_color));

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
}

pub fn report_codegen_error(
    filename: &Path,
    file_content: &str,
    err: CodegenError,
    no_color: bool,
) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag = match err {
        CodegenError::UsingGenericType { expr, t } => {
            Diagnostic::error()
                .with_message(format!("Type of expression is not fully known"))
                .with_labels(vec![
                    Label::primary(file_id, expr.span).with_message(format!("Incomplete type")),
                ])
                .with_notes(vec![
                    format!("Found incomplete type: {}", t)
                ])
        }
    };

    let writer = StandardStream::stderr(color_choice(no_color));

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();

}
