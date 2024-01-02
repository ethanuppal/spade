use std::collections::HashMap;

use itertools::Itertools;

use num::BigUint;
use serde::{Deserialize, Serialize};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::NameID,
};
use spade_types::KnownType;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TraitReq {
    pub name: NameID,
    pub type_params: Vec<TypeVar>,
}

impl std::fmt::Display for TraitReq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.type_params.is_empty() {
            write!(f, "{}", self.name)
        } else {
            write!(
                f,
                "{}<{}>",
                self.name,
                self.type_params.iter().map(|t| format!("{t}")).join(", ")
            )
        }
    }
}
impl std::fmt::Debug for TraitReq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.type_params.is_empty() {
            write!(f, "{}", self.name)
        } else {
            write!(
                f,
                "{}<{}>",
                self.name,
                self.type_params.iter().map(|t| format!("{t:?}")).join(", ")
            )
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraitList {
    pub inner: Vec<TraitReq>,
}

impl TraitList {
    pub fn empty() -> Self {
        Self { inner: vec![] }
    }

    pub fn from_vec(inner: Vec<TraitReq>) -> Self {
        Self { inner }
    }

    pub fn get_trait(&self, name: &NameID) -> Option<&TraitReq> {
        self.inner.iter().find(|t| &t.name == name)
    }
}

// NOTE: The trait imformation is currently carried along with the type vars, but
// the trait information should not be involved in comparisons
impl PartialEq for TraitList {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl Eq for TraitList {}
impl std::hash::Hash for TraitList {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}
impl PartialOrd for TraitList {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        Some(std::cmp::Ordering::Equal)
    }
}
impl Ord for TraitList {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// A type variable represents the type of something in the program. It is mapped
/// to expressions by type equations in the TypeState.
///
/// When TypeVars are passed externally into TypeState, they must be checked for replacement,
/// as the type inference process might have refined them.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TypeVar {
    /// The base type is known and has a list of parameters
    Known(Loc<()>, KnownType, Vec<TypeVar>),
    /// The type is unknown, but must satisfy the specified traits. When the generic substitution
    /// is done, the TypeVars will be carried over to the KnownType type vars
    Unknown(u64, TraitList),
}

impl WithLocation for TypeVar {}

impl TypeVar {
    pub fn array(loc: Loc<()>, inner: TypeVar, size: TypeVar) -> Self {
        TypeVar::Known(loc, KnownType::Array, vec![inner, size])
    }

    pub fn tuple(loc: Loc<()>, inner: Vec<TypeVar>) -> Self {
        TypeVar::Known(loc, KnownType::Tuple, inner)
    }

    pub fn wire(loc: Loc<()>, inner: TypeVar) -> Self {
        TypeVar::Known(loc, KnownType::Wire, vec![inner])
    }

    pub fn backward(loc: Loc<()>, inner: TypeVar) -> Self {
        TypeVar::Known(loc, KnownType::Backward, vec![inner])
    }

    pub fn inverted(loc: Loc<()>, inner: TypeVar) -> Self {
        TypeVar::Known(loc, KnownType::Inverted, vec![inner])
    }

    pub fn expect_known<T, U, K, O>(&self, on_known: K, on_unknown: U) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&KnownType, &[TypeVar]) -> T,
    {
        match self {
            TypeVar::Unknown(_, _) => on_unknown(),
            TypeVar::Known(_, k, v) => on_known(k, v),
        }
    }

    pub fn expect_named<T, U, K, O>(&self, on_named: K, on_unknown: U, on_other: O) -> T
    where
        U: FnOnce() -> T,
        K: FnOnce(&NameID, &[TypeVar]) -> T,
        O: FnOnce(&TypeVar) -> T,
    {
        match self {
            TypeVar::Unknown(_, _) => on_unknown(),
            TypeVar::Known(_, KnownType::Named(name), params) => on_named(name, params),
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
            TypeVar::Unknown(_, _) => on_unknown(),
            TypeVar::Known(_, KnownType::Inverted, params) => {
                if params.len() != 1 {
                    panic!("Found wire with {} params", params.len())
                }
                params[0].expect_named_or_inverted(!inverted_now, on_named, on_unknown, on_other)
            }
            TypeVar::Known(_, KnownType::Named(name), params) => {
                on_named(inverted_now, name, params)
            }
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
            TypeVar::Unknown(_, _) => on_unknown(),
            TypeVar::Known(_, k, v) if k == &KnownType::Named(name) => on_correct(v),
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
            TypeVar::Known(_, KnownType::Integer(size), params) => {
                assert!(params.is_empty());
                on_integer(size.clone())
            }
            TypeVar::Unknown(_, _) => on_unknown(),
            other => on_other(other),
        }
    }
}

impl std::fmt::Debug for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let generics = if params.is_empty() {
                    String::new()
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
            TypeVar::Known(_, KnownType::Integer(inner), _) => {
                write!(f, "{inner}")
            }
            TypeVar::Known(_, KnownType::Tuple, params) => {
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
            TypeVar::Known(_, KnownType::Array, params) => {
                write!(f, "[{:?}; {:?}]", params[0], params[1])
            }
            TypeVar::Known(_, KnownType::Backward, params) => write!(f, "&mut {:?}", params[0]),
            TypeVar::Known(_, KnownType::Wire, params) => write!(f, "&{:?}", params[0]),
            TypeVar::Known(_, KnownType::Inverted, params) => write!(f, "~{:?}", params[0]),
            TypeVar::Known(_, KnownType::Traits(inner), _) => {
                write!(f, "{}", inner.iter().map(|t| format!("{t}")).join(" + "))
            }
            TypeVar::Unknown(id, traits) => write!(
                f,
                "t{id}({})",
                traits.inner.iter().map(|t| format!("{t}")).join("+")
            ),
        }
    }
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeVar::Known(_, KnownType::Named(t), params) => {
                let generics = if params.is_empty() {
                    String::new()
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
            TypeVar::Known(_, KnownType::Integer(inner), _) => {
                write!(f, "{inner}")
            }
            TypeVar::Known(_, KnownType::Tuple, params) => {
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
            TypeVar::Known(_, KnownType::Array, params) => {
                write!(f, "[{}; {}]", params[0], params[1])
            }
            TypeVar::Known(_, KnownType::Backward, params) => write!(f, "&mut {}", params[0]),
            TypeVar::Known(_, KnownType::Wire, params) => write!(f, "&{}", params[0]),
            TypeVar::Known(_, KnownType::Inverted, params) => write!(f, "~{}", params[0]),
            TypeVar::Known(_, KnownType::Traits(traits), _) => write!(
                f,
                "impl {}",
                traits.iter().map(|t| format!("{t}")).join("+")
            ),
            TypeVar::Unknown(_, traits) if traits.inner.is_empty() => write!(f, "_"),
            TypeVar::Unknown(_, traits) => {
                write!(
                    f,
                    "{}",
                    traits.inner.iter().map(|t| format!("{t}")).join("+"),
                )
            }
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
