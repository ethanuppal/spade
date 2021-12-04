use std::collections::HashMap;

use spade_common::{location_info::Loc, name::NameID};
use spade_types::KnownType;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

#[derive(Debug, Clone)]
pub enum TypeVar {
    /// The type is known. If the type is known through a type signature specified by
    /// the user, that signature is the second argument, otherwise None
    Known(KnownType, Vec<TypeVar>, Option<Loc<()>>),
    Tuple(Vec<TypeVar>),
    Array {
        inner: Box<TypeVar>,
        size: Box<TypeVar>,
    },
    /// The type is completely unknown
    Unknown(u64),
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(t, params, _) => {
                let generics = if params.is_empty() {
                    format!("")
                } else {
                    format!(
                        "<{}>",
                        params
                            .iter()
                            .map(|p| format!("{}", p))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                write!(f, "{}{}", t, generics)
            }
            TypeVar::Tuple(inner) => {
                write!(
                    f,
                    "({})",
                    inner
                        .iter()
                        .map(|t| format!("{}", t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeVar::Array { inner, size } => {
                write!(f, "[{}; {}]", inner, size)
            }
            TypeVar::Unknown(id) => write!(f, "t{}", id),
        }
    }
}

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeVar::Known(t1, p1, _), TypeVar::Known(t2, p2, _)) => t1 == t2 && p1 == p2,
            (TypeVar::Known(_, _, _), TypeVar::Unknown(_)) => false,
            (TypeVar::Unknown(_), TypeVar::Known(_, _, _)) => false,
            (TypeVar::Tuple(i1), TypeVar::Tuple(i2)) => i1 == i2,
            (
                TypeVar::Array {
                    inner: i1,
                    size: s1,
                },
                TypeVar::Array {
                    inner: i2,
                    size: s2,
                },
            ) => i1 == i2 && s1 == s2,
            (TypeVar::Tuple(_), _) => false,
            (_, TypeVar::Tuple(_)) => false,
            (TypeVar::Array { .. }, _) => false,
            (_, TypeVar::Array { .. }) => false,
            (TypeVar::Unknown(t1), TypeVar::Unknown(t2)) => t1 == t2,
        }
    }
}

#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum TypedExpression {
    Id(u64),
    Name(NameID),
}

impl std::fmt::Display for TypedExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedExpression::Id(i) => {
                write!(f, "%{}", i)
            }
            TypedExpression::Name(p) => {
                write!(f, "{}", p)
            }
        }
    }
}
