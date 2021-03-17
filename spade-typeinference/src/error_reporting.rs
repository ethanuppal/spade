use std::path::Path;

use crate::{result::UnificationTrace, Error};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{codespan_config, color_choice};

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

pub fn report_typeinference_error(filename: &Path, file_content: &str, err: Error, no_color: bool) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag =
        match err {
            Error::GenericTypeInstanciation => todo![],
            Error::UnknownType(expr) => Diagnostic::error()
                .with_message(format!(
                    "Tried looking up the type of {:?} but it was not found",
                    expr
                ))
                .with_notes(vec!["This is an internal compiler error".to_string()]),
            Error::TypeMissmatch(lhs, rhs) => Diagnostic::error()
                .with_message(format!(
                    "Type missmatch. {} is incompatible with {}",
                    lhs, rhs
                ))
                .with_notes(vec!["This is an internal compiler error".to_string()]),
            Error::EntityOutputTypeMissmatch {
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
            Error::UnspecifiedTypeError { expected, got, loc } => Diagnostic::error()
                .with_message(format!("Expected type {}, got {}", expected, got))
                .with_labels(vec![Label::primary(file_id, loc.loc().span)
                    .with_message(format!("Expected {}", expected))]),
            Error::IntLiteralIncompatible { .. } => {
                todo! {}
            }
            Error::NonBooleanCondition { got, loc } => Diagnostic::error()
                .with_message(format!("If condition must be a bool, got {}", got))
                .with_labels(vec![
                    Label::primary(file_id, loc.loc().span).with_message("Expected boolean")
                ])
                .with_notes(vec![
                    format!("Expected: {}", "bool"), // TODO: Specify full path to the type
                    format!("     Got: {}", got),
                ]),
            Error::IfConditionMissmatch {
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
            Error::NonClockClock { expected, got, loc } => Diagnostic::error()
                .with_message("Register clock must be a type clock")
                .with_labels(vec![
                    Label::primary(file_id, loc.span).with_message(format!("Found type {}", got))
                ])
                .with_notes(type_missmatch_notes(got, expected)),
            Error::NonBoolReset { expected, got, loc } => Diagnostic::error()
                .with_message("Register reset must be a bool")
                .with_labels(vec![
                    Label::primary(file_id, loc.span).with_message(format!("Found type {}", got))
                ])
                .with_notes(type_missmatch_notes(got, expected)),
            Error::RegisterResetMissmatch { expected, got, loc } => Diagnostic::error()
                .with_message("Register reset value missmatch")
                .with_labels(vec![
                    Label::primary(file_id, loc.span).with_message(format!("Found type {}", got))
                ])
                .with_notes(type_missmatch_notes(got, expected)),
            Error::UnspecedEntityOutputTypeMissmatch {
                expected,
                got,
                output_expr,
            } => Diagnostic::error()
                .with_message(format!("Output type missmatch"))
                .with_labels(vec![Label::primary(file_id, output_expr.loc().span)
                    .with_message(format!("Found type {}", got))])
                .with_notes(type_missmatch_notes(got, expected)),
            Error::TupleIndexOfGeneric { loc } => Diagnostic::error()
                .with_message(format!("Type of tuple indexee must be known at this point"))
                .with_labels(vec![Label::primary(file_id, loc.span)
                    .with_message("The type of this must be known")]),
            Error::TupleIndexOfNonTuple { got, loc } => Diagnostic::error()
                .with_message(format!("Attempt to use tuple indexing on non-tuple"))
                .with_labels(vec![
                    Label::primary(file_id, loc.span).with_message(format!("expected tuple"))
                ])
                .with_notes(vec![
                    format!("Expected: tuple"),
                    format!("     Got: {}", got),
                ]),
            Error::TupleIndexOutOfBounds { index, actual_size } => Diagnostic::error()
                .with_message(format!("Tuple index out of bounds"))
                .with_labels(vec![Label::primary(file_id, index.span)
                    .with_message(format!("Tuple only has {} elements", actual_size))])
                .with_notes(vec![
                    format!("     Index: {}", index),
                    format!("Tuple size: {}", actual_size),
                ]),
            Error::NamedArgumentMissmatch {
                expr,
                expected,
                got,
                ..
            } => Diagnostic::error()
                .with_message("Argument type missmatch")
                .with_labels(vec![Label::primary(file_id, expr.span)
                    .with_message(format!("Expected {}", expected))])
                .with_notes(vec![
                    format!("Expected: {}", expected),
                    format!("     Got: {}", got),
                ]),
            Error::ShortNamedArgumentMissmatch {
                name,
                expected,
                got,
            } => Diagnostic::error()
                .with_message("Argument type missmatch")
                .with_labels(vec![Label::primary(file_id, name.span)
                    .with_message(format!("Expected {}", expected))])
                .with_notes(vec![
                    format!("Expected: {}", expected),
                    format!("     Got: {}", got),
                ]),
            Error::PositionalArgumentMissmatch {
                expr,
                expected,
                got,
                ..
            } => Diagnostic::error()
                .with_message("Argument type missmatch")
                .with_labels(vec![Label::primary(file_id, expr.span)
                    .with_message(format!("Expected {}", expected))])
                .with_notes(vec![
                    format!("Expected: {}", expected),
                    format!("     Got: {}", got),
                ]),
        };

    let writer = StandardStream::stderr(color_choice(no_color));

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
}
