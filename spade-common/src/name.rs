use crate::location_info::{Loc, WithLocation};

#[derive(PartialEq, Debug, Clone, Eq, Hash)]
pub struct Identifier(pub String);

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl WithLocation for Identifier {}

#[derive(PartialEq, Debug, Clone, Eq, Hash)]
pub struct Path(pub Vec<Loc<Identifier>>);
impl WithLocation for Path {}

impl Path {
    pub fn as_strs(&self) -> Vec<&str> {
        self.0.iter().map(|id| id.inner.0.as_ref()).collect()
    }
    pub fn as_strings(&self) -> Vec<String> {
        self.0.iter().map(|id| id.inner.0.clone()).collect()
    }
    /// Generate a path from a list of strings
    pub fn from_strs(elems: &[&str]) -> Self {
        Path(
            elems
                .iter()
                .map(|x| Identifier(x.to_string()).nowhere())
                .collect(),
        )
    }

    pub fn ident(ident: Loc<Identifier>) -> Self {
        Self(vec![ident])
    }

    pub fn push_ident(&self, ident: Loc<Identifier>) -> Path {
        let mut result = self.clone();
        result.0.push(ident);
        result
    }

    pub fn pop(&self) -> Self {
        let mut result = self.clone();
        result.0.pop().expect("Failed to pop identifier from path");
        result
    }

    pub fn join(&self, other: Path) -> Path {
        let mut result = self.clone();
        for ident in other.0 {
            result = result.push_ident(ident);
        }
        return result;
    }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_strs().join("::"))
    }
}

/// Anything named will get assigned a unique name ID during AST lowering in order to avoid caring
/// about scopes once HIR has been generated. This is the type of those IDs
///
/// The associated string is only used for formating when printing. The hash and eq methods do not
/// use it
#[derive(Clone)]
pub struct NameID(pub u64, pub Path);
impl WithLocation for NameID {}

impl std::cmp::PartialEq for NameID {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl std::cmp::Eq for NameID {}

impl std::hash::Hash for NameID {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl std::fmt::Debug for NameID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}#{}", self.1, self.0)
    }
}
impl std::fmt::Display for NameID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.1)
    }
}

pub mod testutil {
    use super::*;
    pub fn name_id(id: u64, name: &str) -> Loc<NameID> {
        NameID(id, Path::from_strs(&[name])).nowhere()
    }

    /// Shorthand for creating a name_id with static strs as name
    pub fn name_id_p(id: u64, name: &[&str]) -> Loc<NameID> {
        NameID(id, Path::from_strs(name)).nowhere()
    }
}
