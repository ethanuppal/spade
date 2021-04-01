use std::collections::HashMap;

use spade_common::name::NameID;

#[derive(Clone)]
pub struct Substitutions {
    inner: HashMap<NameID, NameID>,
}

impl Substitutions {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn replace(&mut self, from: NameID, to: NameID) {
        self.inner.insert(from, to);
    }

    /// Return substituted name for `original` if there is such a name,
    /// otherwise return `original`
    pub fn lookup(&self, original: &NameID) -> NameID {
        self.inner
            .get(original)
            .cloned()
            .unwrap_or(original.clone())
    }
}
