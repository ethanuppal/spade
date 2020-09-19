use crate::ast::{Identifier, Path};
use crate::location_info::Loc;
use std::collections::HashMap;

pub struct SymbolTable {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    symbols: Vec<HashMap<Vec<String>, Loc<()>>>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            symbols: vec![HashMap::new()],
        }
    }
    pub fn new_scope(&mut self) {
        self.symbols.push(HashMap::new())
    }

    pub fn close_scope(&mut self) {
        self.symbols.pop();
    }

    pub fn add_ident(&mut self, name: &Loc<Identifier>) {
        self.add_symbol(name.clone().map(|id| vec![id.0]))
    }

    pub fn add_symbol(&mut self, name: Loc<Vec<String>>) {
        self.symbols
            .last_mut()
            .expect("At least one scope must be present to add a scope")
            .insert(name.inner.clone(), name.loc());
    }

    pub fn has_symbol(&self, name: &[String]) -> bool {
        self.symbols.iter().any(|i| i.contains_key(name))
    }
    pub fn has_path(&self, name: &Path) -> bool {
        self.has_symbol(&name.as_strings())
    }
}
