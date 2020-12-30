use std::collections::HashMap;

use crate::hir::Path;
use crate::location_info::Loc;
use crate::types::Type;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

#[derive(Debug, Clone)]
pub enum TypeVar {
    /// The type is known. If the type is known through a type signature specified by
    /// the user, that signature is the second argument, otherwise None
    Known(Type, Option<Loc<()>>),
    /// The type is completely unknown
    Generic(u64),
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(t, _) => write!(f, "{}", t),
            TypeVar::Generic(id) => write!(f, "<{}>", id),
        }
    }
}

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeVar::Known(t1, _), TypeVar::Known(t2, _)) => t1 == t2,
            (TypeVar::Known(_, _), TypeVar::Generic(_)) => false,
            (TypeVar::Generic(_), TypeVar::Known(_, _)) => false,
            (TypeVar::Generic(t1), TypeVar::Generic(t2)) => t1 == t2,
        }
    }
}

#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum TypedExpression {
    Id(u64),
    Name(Path),
}
