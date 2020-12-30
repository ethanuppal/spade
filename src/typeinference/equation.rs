use std::collections::HashMap;

use crate::hir::Path;
use crate::location_info::Loc;
use crate::types::Type;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

#[derive(PartialEq, Debug, Clone)]
pub enum TypeVar {
    /// The type is known. If the type is known through a type signature specified by
    /// the user, that signature is the second argument, otherwise None
    Known(Type, Option<Loc<Type>>),
    /// The type is completely unknown
    Generic(u64),
}

#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum TypedExpression {
    Id(u64),
    Name(Path),
}
