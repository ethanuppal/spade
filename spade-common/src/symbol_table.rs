use crate::id_tracker::IdTracker;
use crate::name::{NameID, Path};
use std::collections::HashMap;

/// A table of the symbols known to the program in the current scope. Names
/// are mapped to IDs which are then mapped to the actual things
pub struct SymbolTable<T> {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    pub symbols: Vec<HashMap<Path, NameID>>,
    id_tracker: IdTracker,
    pub items: HashMap<NameID, T>,
}

impl<T> SymbolTable<T> {
    pub fn new() -> Self {
        Self {
            symbols: vec![HashMap::new()],
            id_tracker: IdTracker::new(),
            items: HashMap::new(),
        }
    }
    pub fn new_scope(&mut self) {
        self.symbols.push(HashMap::new())
    }

    pub fn close_scope(&mut self) {
        self.symbols.pop();
    }


    /// Adds a thing to the scope at `current_scope - offset`. Panics if there is no such scope
    pub fn add_thing_with_id_at_offset(
        &mut self,
        offset: usize,
        id: u64,
        name: Path,
        item: T,
    ) -> NameID {
        let name_id = NameID(id, name.clone());
        if self.items.contains_key(&name_id) {
            panic!("Duplicate nameID inserted, {}", id);
        }
        self.items.insert(name_id.clone(), item);

        if offset > self.symbols.len() {
            panic!("Not enough scopes to add symbol at offset {}", offset);
        }

        let index = self.symbols.len() - 1 - offset;
        self.symbols[index].insert(name, name_id.clone());

        name_id
    }

    pub fn add_thing_with_id(&mut self, id: u64, name: Path, item: T) -> NameID {
        self.add_thing_with_id_at_offset(0, id, name, item)
    }

    pub fn add_thing(&mut self, name: Path, item: T) -> NameID {
        let id = self.id_tracker.next();
        self.add_thing_with_id(id, name, item)
    }

    pub fn add_thing_at_offset(&mut self, offset: usize, name: Path, item: T) -> NameID {
        let id = self.id_tracker.next();
        self.add_thing_with_id_at_offset(offset, id, name, item)
    }
}
