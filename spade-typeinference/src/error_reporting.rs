use crate::{result::UnificationTrace, Error};
use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{
    codespan_config, color_choice, AsLabel, CodeBundle, CompilationError,
};

pub fn type_mismatch_notes(got: UnificationTrace, expected: UnificationTrace) -> Vec<String> {
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

impl CompilationError for Error {
    fn report(self, code: &CodeBundle, no_color: bool) {
        let diag = match self {
            Error::GenericTypeInstanciation => todo![],
            Error::UnknownType(expr) => Diagnostic::error()
                .with_message(format!(
                    "Tried looking up the type of {:?} but it was not found",
                    expr
                ))
                .with_notes(vec!["This is an internal compiler error".to_string()]),
            Error::TypeMismatch(lhs, rhs) => Diagnostic::error()
                .with_message(format!(
                    "Type mismatch. {} is incompatible with {}",
                    lhs, rhs
                ))
                .with_notes(vec!["This is an internal compiler error".to_string()]),
            Error::EntityOutputTypeMismatch {
                expected,
                got,
                type_spec,
                output_expr,
            } => Diagnostic::error()
                .with_message(format!("Type error"))
                .with_labels(vec![
                    output_expr
                        .primary_label()
                        .with_message(format!("Found type {}", got)),
                    type_spec
                        .secondary_label()
                        .with_message(format!("{} type specified here", expected)),
                ])
                .with_notes(type_mismatch_notes(got, expected)),
            Error::UnspecifiedTypeError { expected, got, loc } => Diagnostic::error()
                .with_message(format!("Expected type {}, got {}", expected, got))
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("Expected {}", expected))]),
            Error::IntLiteralIncompatible { .. } => {
                todo! {}
            }
            Error::NonBooleanCondition { got, loc } => Diagnostic::error()
                .with_message(format!("If condition must be a bool, got {}", got))
                .with_labels(vec![loc.primary_label().with_message("Expected boolean")])
                .with_notes(vec![
                    format!("Expected: {}", "bool"), // TODO: Specify full path to the type
                    format!("     Got: {}", got),
                ]),
            Error::IfConditionMismatch {
                expected,
                got,
                first_branch,
                incorrect_branch,
            } => Diagnostic::error()
                .with_message(format!("If branches have incompatible type"))
                .with_labels(vec![
                    first_branch
                        .primary_label()
                        .with_message(format!("This branch has type {}", expected)),
                    incorrect_branch
                        .primary_label()
                        .with_message(format!("But this one has type {}", got)),
                ])
                .with_notes(type_mismatch_notes(got, expected)),
            Error::MatchBranchMissmatch {
                expected,
                got,
                first_branch,
                incorrect_branch,
            } => Diagnostic::error()
                .with_message(format!("Match branches have incompatible type"))
                .with_labels(vec![
                    first_branch
                        .primary_label()
                        .with_message(format!("This branch has type {}", expected)),
                    incorrect_branch
                        .primary_label()
                        .with_message(format!("But this one has type {}", got)),
                ])
                .with_notes(type_mismatch_notes(got, expected)),
            Error::NonClockClock { expected, got, loc } => Diagnostic::error()
                .with_message("Register clock must be a type clock")
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("Found type {}", got))])
                .with_notes(type_mismatch_notes(got, expected)),
            Error::NonBoolReset { expected, got, loc } => Diagnostic::error()
                .with_message("Register reset must be a bool")
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("Found type {}", got))])
                .with_notes(type_mismatch_notes(got, expected)),
            Error::RegisterResetMismatch { expected, got, loc } => Diagnostic::error()
                .with_message("Register reset value mismatch")
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("Found type {}", got))])
                .with_notes(type_mismatch_notes(got, expected)),
            Error::UnspecedEntityOutputTypeMismatch {
                expected,
                got,
                output_expr,
            } => Diagnostic::error()
                .with_message(format!("Output type mismatch"))
                .with_labels(vec![output_expr
                    .primary_label()
                    .with_message(format!("Found type {}", got))])
                .with_notes(type_mismatch_notes(got, expected)),
            Error::TupleIndexOfGeneric { loc } => Diagnostic::error()
                .with_message(format!("Type of tuple indexee must be known at this point"))
                .with_labels(vec![loc
                    .primary_label()
                    .with_message("The type of this must be known")]),
            Error::TupleIndexOfNonTuple { got, loc } => Diagnostic::error()
                .with_message(format!("Attempt to use tuple indexing on non-tuple"))
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("expected tuple"))])
                .with_notes(vec![
                    format!("Expected: tuple"),
                    format!("     Got: {}", got),
                ]),
            Error::TupleIndexOutOfBounds { index, actual_size } => Diagnostic::error()
                .with_message(format!("Tuple index out of bounds"))
                .with_labels(vec![index
                    .primary_label()
                    .with_message(format!("Tuple only has {} elements", actual_size))])
                .with_notes(vec![
                    format!("     Index: {}", index),
                    format!("Tuple size: {}", actual_size),
                ]),
            Error::NamedArgumentMismatch {
                expr,
                expected,
                got,
                ..
            } => Diagnostic::error()
                .with_message("Argument type mismatch")
                .with_labels(vec![expr
                    .primary_label()
                    .with_message(format!("Expected {}", expected))])
                .with_notes(vec![
                    format!("Expected: {}", expected),
                    format!("     Got: {}", got),
                ]),
            Error::ShortNamedArgumentMismatch {
                name,
                expected,
                got,
            } => Diagnostic::error()
                .with_message("Argument type mismatch")
                .with_labels(vec![name
                    .primary_label()
                    .with_message(format!("Expected {}", expected))])
                .with_notes(vec![
                    format!("Expected: {}", expected),
                    format!("     Got: {}", got),
                ]),
            Error::PositionalArgumentMismatch {
                expr,
                expected,
                got,
                ..
            } => Diagnostic::error()
                .with_message("Argument type mismatch")
                .with_labels(vec![expr
                    .primary_label()
                    .with_message(format!("Expected {}", expected))])
                .with_notes(vec![
                    format!("Expected: {}", expected),
                    format!("     Got: {}", got),
                ]),
            Error::PatternTypeMissmatch {
                pattern,
                expected,
                got,
            } => Diagnostic::error()
                .with_message("Pattern type missmatch")
                .with_labels(vec![pattern
                    .primary_label()
                    .with_message(format!("expected {}", expected))])
                .with_notes(vec![
                    format!("Expected: {}", expected),
                    format!("     Got: {}", got),
                ]),
            Error::FirstPipelineArgNotClock { expected, spec } => Diagnostic::error()
                .with_message(format!(
                    "First pipeline argument must be a clock. Got {}",
                    spec
                ))
                .with_labels(vec![spec
                    .primary_label()
                    .with_message(format!("Expected {}", expected))]),
        };

        let writer = StandardStream::stderr(color_choice(no_color));

        term::emit(&mut writer.lock(), &codespan_config(), &code.files, &diag).unwrap();
    }
}
