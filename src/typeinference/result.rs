use thiserror::Error;

use super::equation::{TypeVar, TypedExpression};

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("The specified expression has no type information {}", 0.0)]
    UnknownType(TypedExpression),
    #[error("Type missmatch between {0:?} and {1:?}")]
    TypeMissmatch(TypeVar, TypeVar),
}
pub type Result<T> = std::result::Result<T, Error>;
