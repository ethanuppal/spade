use std::collections::HashMap;

use itertools::Itertools;

use num::BigUint;
use serde::{Deserialize, Serialize};
use spade_common::{location_info::WithLocation, name::NameID};
use spade_types::KnownType;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

/// A type variable represents the type of something in the program. It is mapped
/// to expressions by type equations in the TypeState.
///
/// When TypeVars are passed externally into TypeState, they must be checked for replacement,
/// as the type inference process might have refined them.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TypeVar {
    /// The base type is known and has a list of parameters
    Known(KnownType, Vec<TypeVar>),
    /// The type is completely unknown
    Unknown(u64),
}

impl WithLocation for TypeVar {}

impl TypeVar {
    pub fn array(inner: TypeVar, size: TypeVar) -> Self {
        TypeVar::Known(KnownType::Array, vec![inner, size])
    }

    pub fn tuple(inner: Vec<TypeVar>) -> Self {
        TypeVar::Known(KnownType::Tuple, inner)
    }

    pub fn wire(inner: TypeVar) -> Self {
        TypeVar::Known(KnownType::Wire, vec![inner])
    }

    pub fn backward(inner: TypeVar) -> Self {
        TypeVar::Known(KnownType::Backward, vec![inner])
    }

    pub fn inverted(inner: TypeVar) -> Self {
        TypeVar::Known(KnownType::Inverted, vec![inner])
    }

    pub fn expect_known<T, U, K, O>(&self, on_known: K, on_unknown: U) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&KnownType, &[TypeVar]) -> T,
    {
        match self {
            TypeVar::Unknown(_) => on_unknown(),
            TypeVar::Known(k, v) => on_known(k, v),
        }
    }

    pub fn expect_named<T, U, K, O>(&self, on_named: K, on_unknown: U, on_other: O) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&NameID, &[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_) => on_unknown(),
            TypeVar::Known(KnownType::Named(name), params) => on_named(name, params),
            other => on_other(other),
        }
    }

    /// Expect a named type, or TypeVar::Inverted(named), or a recursive inversion.
    /// inverted_now is stateful and used to track if we are currently in an
    /// inverted context.
    /// The first argument of the on_named function specifies whether or not
    /// the final named type we found was inverted or not. I.e. if we ran it on
    /// `~T`, it would be called with (true, T), and if we ran it on `T` it would
    /// be called with `(false, T)`
    pub fn expect_named_or_inverted<T, U, K, O>(
        &self,
        inverted_now: bool,
        on_named: K,
        on_unknown: U,
        on_other: O,
    ) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(bool, &NameID, &[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_) => on_unknown(),
            TypeVar::Known(KnownType::Inverted, params) => {
                if params.len() != 1 {
                    panic!("Found wire with {} params", params.len())
                }
                params[0].expect_named_or_inverted(!inverted_now, on_named, on_unknown, on_other)
            }
            TypeVar::Known(KnownType::Named(name), params) => on_named(inverted_now, name, params),
            other => on_other(other),
        }
    }

    pub fn expect_specific_named<T, U, K, O>(
        &self,
        name: NameID,
        on_correct: K,
        on_unknown: U,
        on_other: O,
    ) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_) => on_unknown(),
            TypeVar::Known(k, v) if k == &KnownType::Named(name) => on_correct(v),
            other => on_other(other),
        }
    }

    /// Assumes that this type is KnownType::Integer(size) and calls on_integer then. Otherwise
    /// calls on_unknown or on_other depending on the type. If the integer is given type params,
    /// panics
    pub fn expect_integer<T, U, K, O>(&self, on_integer: K, on_unknown: U, on_other: O) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(BigUint) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Known(KnownType::Integer(size), params) => {
                assert!(params.is_empty());
                on_integer(size.clone())
            }
            TypeVar::Unknown(_) => on_unknown(),
            other => on_other(other),
        }
    }
}

impl std::fmt::Debug for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(KnownType::Named(t), params) => {
                let generics = if params.is_empty() {
                    format!("")
                } else {
                    format!(
                        "<{}>",
                        params
                            .iter()
                            .map(|p| format!("{:?}", p))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                write!(f, "{}{}", t, generics)
            }
            TypeVar::Known(KnownType::Integer(inner), _) => {
                write!(f, "{inner}")
            }
            TypeVar::Known(KnownType::Tuple, params) => {
                write!(
                    f,
                    "({})",
                    params
                        .iter()
                        .map(|t| format!("{:?}", t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeVar::Known(KnownType::Array, params) => {
                write!(f, "[{:?}; {:?}]", params[0], params[1])
            }
            TypeVar::Known(KnownType::Backward, params) => write!(f, "&mut {:?}", params[0]),
            TypeVar::Known(KnownType::Wire, params) => write!(f, "&{:?}", params[0]),
            TypeVar::Known(KnownType::Inverted, params) => write!(f, "~{:?}", params[0]),
            TypeVar::Known(KnownType::Traits(inner), _) => {
                write!(f, "{}", inner.iter().map(|t| format!("{t}")).join(" + "))
            }
            TypeVar::Unknown(id) => write!(f, "t{id}"),
        }
    }
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(KnownType::Named(t), params) => {
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
            TypeVar::Known(KnownType::Integer(inner), _) => {
                write!(f, "{inner}")
            }
            TypeVar::Known(KnownType::Tuple, params) => {
                write!(
                    f,
                    "({})",
                    params
                        .iter()
                        .map(|t| format!("{}", t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeVar::Known(KnownType::Array, params) => {
                write!(f, "[{}; {}]", params[0], params[1])
            }
            TypeVar::Known(KnownType::Backward, params) => write!(f, "&mut {}", params[0]),
            TypeVar::Known(KnownType::Wire, params) => write!(f, "&{}", params[0]),
            TypeVar::Known(KnownType::Inverted, params) => write!(f, "~{}", params[0]),
            TypeVar::Known(KnownType::Traits(traits), _) => write!(
                f,
                "impl {}",
                traits.iter().map(|t| format!("{t}")).join("+")
            ),
            TypeVar::Unknown(_) => write!(f, "_"),
        }
    }
}

#[derive(Eq, PartialEq, Hash, Debug, Clone, Serialize, Deserialize)]
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
                write!(f, "{}#{}", p, p.0)
            }
        }
    }
}
