use super::Identifier;
use crate::location_info::WithLocation;

#[derive(PartialEq, Debug, Clone, Eq, Hash)]
pub struct Path(pub Vec<Identifier>);

impl WithLocation for Path {}

impl Path {
    pub fn from_strs(names: &[&str]) -> Self {
        Self(
            names
                .iter()
                .map(|s| s.to_string())
                .map(Identifier::Named)
                .collect(),
        )
    }

    pub fn with_ident(&self, new: Identifier) -> Self {
        let mut result = self.0.clone();
        result.push(new);
        Self(result)
    }

    pub fn mangle(&self) -> String {
        format!(
            "_m_{}",
            self.0
                .iter()
                .map(|l| format!("{}", l))
                .collect::<Vec<_>>()
                .join("_")
        )
    }

    pub fn maybe_identifier(&self) -> Option<&Identifier> {
        if self.0.len() == 1 {
            Some(&self.0[0])
        } else {
            None
        }
    }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let result = self
            .0
            .iter()
            .map(|id| format!("{}", id))
            .collect::<Vec<_>>()
            .join("::");

        write!(f, "{}", result)
    }
}
