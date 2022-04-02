use std::collections::HashMap;

use spade_common::{location_info::Loc, name::NameID};
use spade_types::KnownType;

use crate::TypeState;

pub type TypeEquations = HashMap<TypedExpression, InnerTypeVar>;

/// An owned type variable. Should only be owned by the TypeState struct in a context
/// where the type state replaces TypeVars after unification. Any external owners of
/// TypeVars must use TypeVarRef
///
/// `clone` is derived to simplify the implementation through allowing derives, but
/// should not be used outside the unification code
#[derive(Debug, Clone, Hash, Eq)]
pub enum InnerTypeVar {
    /// The type is known. If the type is known through a type signature specified by
    /// the user, that signature is the second argument, otherwise None
    Known(KnownType, Vec<InnerTypeVar>, Option<Loc<()>>),
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
            InnerTypeVar::Known(t, params, _) => {
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

impl PartialEq for InnerTypeVar {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (InnerTypeVar::Known(t1, p1, _), InnerTypeVar::Known(t2, p2, _)) => {
                t1 == t2 && p1 == p2
            }
            (InnerTypeVar::Known(_, _, _), InnerTypeVar::Unknown(_)) => false,
            (InnerTypeVar::Unknown(_), InnerTypeVar::Known(_, _, _)) => false,
            (InnerTypeVar::Tuple(i1), InnerTypeVar::Tuple(i2)) => i1 == i2,
            (
                InnerTypeVar::Array {
                    inner: i1,
                    size: s1,
                },
                InnerTypeVar::Array {
                    inner: i2,
                    size: s2,
                },
            ) => i1 == i2 && s1 == s2,
            (InnerTypeVar::Tuple(_), _) => false,
            (_, InnerTypeVar::Tuple(_)) => false,
            (InnerTypeVar::Array { .. }, _) => false,
            (_, InnerTypeVar::Array { .. }) => false,
            (InnerTypeVar::Unknown(t1), InnerTypeVar::Unknown(t2)) => t1 == t2,
        }
    }
}

#[derive(Debug, Clone)]
enum RefKind<'a> {
    Owned(InnerTypeVar),
    Ref(&'a InnerTypeVar),
}

/// An owned type variable with a limited lifetime. Has a lifetime to ensure that it is only valid
/// until the corresponding type state is modified. Can not simply be a normal reference
/// as temporary ownership of the underlying TypeVar is sometimes required, for example,
/// when creating type vars with new_generic
#[derive(Debug, Clone)]
pub struct TypeVarRef<'a> {
    var: RefKind<'a>,
    _0: std::marker::PhantomData<&'a ()>,
}

impl<'a> TypeVarRef<'a> {
    pub fn from_owned(inner: InnerTypeVar, _state: &'a TypeState) -> TypeVarRef<'a> {
        Self {
            var: RefKind::Owned(inner),
            _0: Default::default(),
        }
    }

    pub fn from_ref<'b: 'a>(inner: &'a InnerTypeVar, _state: &'b TypeState) -> TypeVarRef<'a> {
        Self {
            var: RefKind::Ref(inner),
            _0: Default::default(),
        }
    }

    pub fn as_free(&self) -> FreeTypeVar {
        match &self.var {
            RefKind::Owned(inner) => FreeTypeVar(inner.clone()),
            RefKind::Ref(inner) => FreeTypeVar((*inner).clone()),
        }
    }
}

// Constructors which construct InnerTypeVars from refs with the same lifetime
// as the refs.
impl<'a> TypeVarRef<'a> {
    pub fn known(base: KnownType, args: Vec<TypeVarRef<'a>>, loc: Option<Loc<()>>) -> Self {
        Self {
            var: RefKind::Owned(InnerTypeVar::Known(
                base,
                args.iter().map(|arg| arg.as_ref().clone()).collect(),
                loc,
            )),
            _0: Default::default(),
        }
    }

    pub fn tuple(inner: Vec<TypeVarRef<'a>>) -> Self {
        Self {
            var: RefKind::Owned(InnerTypeVar::Tuple(
                inner.iter().map(|t| t.as_ref().clone()).collect(),
            )),
            _0: Default::default(),
        }
    }

    pub fn array(inner: TypeVarRef<'a>, size: TypeVarRef<'a>) -> Self {
        Self {
            var: RefKind::Owned(InnerTypeVar::Array {
                inner: Box::new(inner.as_ref().clone()),
                size: Box::new(size.as_ref().clone()),
            }),
            _0: Default::default(),
        }
    }
}

impl<'a> AsRef<InnerTypeVar> for TypeVarRef<'a> {
    fn as_ref(&self) -> &InnerTypeVar {
        match &self.var {
            RefKind::Owned(inner) => &inner,
            RefKind::Ref(inner) => inner,
        }
    }
}

impl<'a> std::fmt::Display for TypeVarRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.var {
            RefKind::Owned(inner) => write!(f, "{}", inner),
            RefKind::Ref(inner) => write!(f, "{}", inner),
        }
    }
}

impl<'a> PartialEq for TypeVarRef<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

/// A type variable no longer associated with a type state.
#[derive(Debug, PartialEq, Clone)]
pub struct FreeTypeVar(InnerTypeVar);

impl FreeTypeVar {
    pub fn new(inner: InnerTypeVar) -> Self {
        Self(inner)
    }

    /// Returns the inner type var. Must only be called if the type state is no
    /// longer going to be modified, such as during MIR lowering.
    pub fn danger_inner(&self) -> &InnerTypeVar {
        &self.0
    }
}

impl std::fmt::Display for FreeTypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
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
