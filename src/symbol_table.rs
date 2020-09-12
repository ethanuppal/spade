use crate::location_info::Loc;
use std::collections::HashMap;

pub struct SymbolTable {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    symbols: Vec<HashMap<String, Loc<()>>>,
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

    pub fn add_symbol(&mut self, name: Loc<String>) {
        self.symbols
            .last_mut()
            .expect("At least one scope must be present to add a scope")
            .insert(name.inner.clone(), name.loc());
    }

    pub fn has_symbol(&self, name: &String) -> bool {
        self.symbols.iter().any(|i| i.contains_key(name))
    }
}
