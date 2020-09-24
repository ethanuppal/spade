use super::Identifier;
use crate::location_info::{Loc, WithLocation};

#[derive(PartialEq, Debug, Clone, Eq, Hash)]
pub struct Path(pub Vec<Loc<Identifier>>);

impl WithLocation for Path {}

impl Path {
    pub fn from_strs(names: &[&str]) -> Self {
        Self(
            names
                .iter()
                .map(|s| s.to_string())
                .map(Identifier::Named)
                .map(Loc::nowhere)
                .collect(),
        )
    }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let result = self
            .0
            .iter()
            .map(Loc::strip_ref)
            .map(|id| format!("{}", id))
            .collect::<Vec<_>>()
            .join("::");

        write!(f, "{}", result)
    }
}
