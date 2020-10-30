use crate::hir::Path;
use crate::location_info::{Loc, WithLocation};

#[derive(PartialEq, Debug, Clone, Eq, Hash)]
pub enum Identifier {
    Named(String),
    Anonymous(u64),
}

impl Loc<Identifier> {
    pub fn to_path(self) -> Path {
        Path(vec![self])
    }
}

impl WithLocation for Identifier {}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Identifier::Named(inner) => write!(f, "{}", inner),
            Identifier::Anonymous(inner) => write!(f, "%{}", inner),
        }
    }
}
