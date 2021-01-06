use crate::hir::Identifier;
use crate::location_info::Loc;
use std::collections::HashMap;

/// A table of scoped symbols defined locally. Global symbols, i.e. paths are
/// tracked by the [crate::global_symbols::GlobalSymbols] struct
pub struct SymbolTable {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    symbols: Vec<HashMap<Identifier, Loc<()>>>,
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
        self.add_symbol(name)
    }

    pub fn add_symbol(&mut self, name: &Loc<Identifier>) {
        self.symbols
            .last_mut()
            .expect("At least one scope must be present to add a symbol")
            .insert(name.inner.clone(), name.loc());
    }

    pub fn has_symbol(&self, name: &Identifier) -> bool {
        self.symbols.iter().any(|i| i.contains_key(name))
    }
}
