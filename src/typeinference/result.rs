use thiserror::Error;

use super::equation::{TypeVar, TypedExpression};
use crate::location_info::Loc;

pub type UnificationError = (TypeVar, TypeVar);

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("The specified expression has no type information {}", 0.0)]
    UnknownType(TypedExpression),
    #[error("Type missmatch between {0:?} and {1:?}")]
    TypeMissmatch(TypeVar, TypeVar),

    #[error("Entity output type missmatch")]
    EntityOutputTypeMissmatch {
        expected: TypeVar,
        got: TypeVar,
        // The location of the type specification
        type_spec: Loc<()>,
        // The location of the output expression with the offending type
        output_expr: Loc<()>,
    },
    #[error("Type error: expected {expected}, got: {got}")]
    UnspecifiedTypeError {
        expected: TypeVar,
        got: TypeVar,
        loc: Loc<()>,
    },
    #[error("Int literal not compatible")]
    IntLiteralIncompatible { got: TypeVar, loc: Loc<()> },
    #[error("If condition must be boolean")]
    NonBooleanCondition { got: TypeVar, loc: Loc<()> },
    #[error("If condition missmatch")]
    IfConditionMissmatch {
        expected: TypeVar,
        got: TypeVar,
        first_branch: Loc<()>,
        incorrect_branch: Loc<()>,
    },
    #[error("Non clock used as register clock")]
    NonClockClock {
        expected: TypeVar,
        got: TypeVar,
        loc: Loc<()>,
    },

    #[error("Attempting to instanciate generic type")]
    GenericTypeInstanciation,
}
pub type Result<T> = std::result::Result<T, Error>;
