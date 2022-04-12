use crate::constraints::ConstraintSource;
use crate::{result::UnificationTrace, Error};
use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::term::{self, termcolor::Buffer};
use spade_common::error_reporting::{codespan_config, AsLabel, CodeBundle, CompilationError};

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
    fn report(self, buffer: &mut Buffer, code: &CodeBundle) {
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
                    .with_message(format!("Expected {} here", expected))]),
            Error::ConstraintMismatch {
                expected,
                got,
                source,
                loc,
            } => Diagnostic::error()
                .with_message(format!("Expected type {}, got {}", expected, got))
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("Expected {}, got {}", expected, got))])
                .with_notes(vec![match source {
                    ConstraintSource::AdditionOutput => format!(
                        "Addition creates one more output bit than the input to avoid overflow"
                    ),
                    ConstraintSource::MultOutput => {
                        format!("The size of a multiplication is the sum of the operand sizes")
                    }
                    ConstraintSource::ArrayIndexing => {
                        // NOTE: This error message could probably be improved
                        format!("because the value is used as an index to an array")
                    }
                    ConstraintSource::Concatenation => {
                        format!("The size of a concatenation is the sum of the operand sizes")
                    }
                }]),
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
            Error::MatchBranchMismatch {
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
            Error::ArrayElementMismatch {
                expected,
                got,
                loc,
                first_element,
            } => Diagnostic::error()
                .with_message(format!(
                    "Array element type mismatch. Expected {}",
                    expected
                ))
                .with_labels(vec![
                    loc.primary_label()
                        .with_message(format!("Expected {}", expected)),
                    first_element
                        .primary_label()
                        .with_message(format!("To match this")),
                ])
                .with_notes(vec![
                    format!("Expected: {}", expected),
                    format!("     Got: {}", got),
                ]),
            Error::IndexMustBeInteger { got, loc } => Diagnostic::error()
                .with_message(format!("Index must be an integer, got {}", got))
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("Expected integer"))]),
            Error::IndexeeMustBeArray { got, loc } => Diagnostic::error()
                .with_message(format!("Index target must be an array, got {}", got))
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("Expected array"))]),
            Error::FieldAccessOnEnum { loc, actual_type } => Diagnostic::error()
                .with_message(format!("Field access on an enum type"))
                .with_labels(vec![
                    loc.primary_label().with_message("Expected a struct"),
                    loc.secondary_label()
                        .with_message(format!("Expression has type {}", actual_type)),
                ])
                .with_notes(vec!["Field access is only allowed on structs".to_string()]),
            Error::FieldAccessOnPrimitive { loc, actual_type } => Diagnostic::error()
                .with_message(format!("Field access on a primitive type"))
                .with_labels(vec![
                    loc.primary_label().with_message("Expected a struct"),
                    loc.secondary_label()
                        .with_message(format!("Expression has type {}", actual_type)),
                ])
                .with_notes(vec!["Field access is only allowed on structs".to_string()]),
            Error::FieldAccessOnGeneric { loc, name } => Diagnostic::error()
                .with_message(format!("Field access on a generic type"))
                .with_labels(vec![
                    loc.primary_label().with_message("Expected a struct"),
                    loc.secondary_label()
                        .with_message(format!("Expression has type {}", name)),
                ])
                .with_notes(vec!["Field access is only allowed on structs".to_string()]),
            Error::FieldAccessOnInteger { loc } => Diagnostic::error()
                .with_message(format!("Field access on a type level integer"))
                .with_labels(vec![
                    loc.primary_label().with_message("Expected a struct"),
                    loc.secondary_label()
                        .with_message(format!("Expression is a type level integer")),
                ])
                .with_notes(vec!["Field access is only allowed on structs".to_string()]),
            Error::FieldAccessOnIncomplete { loc } => Diagnostic::error()
                .with_message(format!("Field access on incomplete type"))
                .with_labels(vec![loc.primary_label().with_message("Incomplete type")])
                .with_notes(vec![
                    "Try specifiying the type of the expression".to_string()
                ]),
            Error::FieldAccessOnNonStruct { loc, got } => Diagnostic::error()
                .with_message(format!("Field access on {} which is not a struct", got))
                .with_labels(vec![loc
                    .primary_label()
                    .with_message(format!("Expected strcut, found {}", got))]),
            Error::NoSuchField { field, _struct } => Diagnostic::error()
                .with_message(format!("{_struct} has no field named {field}"))
                .with_labels(vec![field
                    .primary_label()
                    .with_message(format!("Not a field of {_struct}"))]),
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
            Error::PatternTypeMismatch {
                pattern,
                expected,
                got,
            } => Diagnostic::error()
                .with_message("Pattern type mismatch")
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

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}
