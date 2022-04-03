use std::collections::HashMap;

use spade_common::name::NameID;
use spade_types::KnownType;

pub type TypeEquations = HashMap<TypedExpression, InnerTypeVar>;

/// An owned type variable. Should only be owned by the TypeState struct in a context
/// where the type state replaces TypeVars after unification. Any external owners of
/// TypeVars must use TypeVarRef
///
/// `clone` is derived to simplify the implementation through allowing derives, but
/// should not be used outside the unification code
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum InnerTypeVar {
    /// The type is known. If the type is known through a type signature specified by
    /// the user, that signature is the second argument, otherwise None
    Known(KnownType, Vec<InnerTypeVar>),
    Tuple(Vec<InnerTypeVar>),
    Array {
        inner: Box<InnerTypeVar>,
        size: Box<InnerTypeVar>,
    },
    /// The type is completely unknown
    Unknown(u64),
}

impl std::fmt::Display for InnerTypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InnerTypeVar::Known(t, params) => {
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
            InnerTypeVar::Tuple(inner) => {
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
            InnerTypeVar::Array { inner, size } => {
                write!(f, "[{}; {}]", inner, size)
            }
            InnerTypeVar::Unknown(id) => write!(f, "t{}", id),
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
                write!(f, "{}#{}", p, p.0)
            }
        }
    }
}
