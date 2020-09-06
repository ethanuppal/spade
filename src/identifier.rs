#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Identifier {
    Str(String),
    Id(usize),
}

// Conversion impls
impl From<&str> for Identifier {
    fn from(other: &str) -> Self {
        Identifier::Str(other.into())
    }
}
impl From<String> for Identifier {
    fn from(other: String) -> Self {
        other.as_str().into()
    }
}
impl From<usize> for Identifier {
    fn from(other: usize) -> Self {
        Identifier::Id(other)
    }
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Identifier::Str(name) => write!(f, "{}", name),
            Identifier::Id(id) => write!(f, "%{}", id),
        }
    }
}
