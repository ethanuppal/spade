use crate::{EntityHead, FunctionHead, PipelineHead};
use spade_common::{
    id_tracker::IdTracker,
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID, Path},
};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("No such symbol")]
    NoSuchSymbol(Loc<Path>),
    #[error("Not a type symbol")]
    NotATypeSymbol(Loc<Path>, Thing),
    #[error("Not a variable")]
    NotAVariable(Loc<Path>, Thing),
    #[error("Not an entity")]
    NotAnEntity(Loc<Path>, Thing),
    #[error("Not a pipeline")]
    NotAPipeline(Loc<Path>, Thing),
    #[error("Not a function")]
    NotAFunction(Loc<Path>, Thing),
}

/// Any named thing in the language
#[derive(PartialEq, Debug, Clone)]
pub enum Thing {
    /// Defintion of a named type
    Type(Loc<TypeSymbol>),
    Function(Loc<FunctionHead>),
    Entity(Loc<EntityHead>),
    Pipeline(Loc<PipelineHead>),
    Variable(Loc<Identifier>),
}

impl Thing {
    pub fn kind_string(&self) -> &'static str {
        match self {
            Thing::Type(_) => "type",
            Thing::Entity(_) => "entity",
            Thing::Variable(_) => "variable",
            Thing::Pipeline(_) => "pipeline",
            Thing::Function(_) => "function",
        }
    }

    pub fn loc(&self) -> Loc<()> {
        match self {
            Thing::Type(i) => i.loc(),
            Thing::Entity(i) => i.loc(),
            Thing::Pipeline(i) => i.loc(),
            Thing::Variable(i) => i.loc(),
            Thing::Function(i) => i.loc(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum GenericArg {
    TypeName(Identifier),
    Number(Identifier),
}
impl WithLocation for GenericArg {}

/// A previously declared type symbol
#[derive(Clone, Debug, PartialEq)]
pub enum TypeSymbol {
    /// A fixed type that has been declared, like a typedef, enum or struct with the
    /// specified generic arguments
    Declared(Vec<Loc<GenericArg>>),
    /// A generic type present in the current scope
    GenericArg,
    GenericInt,
}
impl WithLocation for TypeSymbol {}

/// A table of the symbols known to the program in the current scope. Names
/// are mapped to IDs which are then mapped to the actual things
pub struct SymbolTable {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    pub symbols: Vec<HashMap<Path, NameID>>,
    id_tracker: IdTracker,
    pub items: HashMap<NameID, Thing>,
}

impl SymbolTable {
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
        item: Thing,
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

    pub fn add_thing_with_id(&mut self, id: u64, name: Path, item: Thing) -> NameID {
        self.add_thing_with_id_at_offset(0, id, name, item)
    }

    pub fn add_thing(&mut self, name: Path, item: Thing) -> NameID {
        let id = self.id_tracker.next();
        self.add_thing_with_id(id, name, item)
    }

    /// Adds a thing to the scope at `current_scope - offset`. Panics if there is no such scope
    pub fn add_thing_at_offset(&mut self, offset: usize, name: Path, item: Thing) -> NameID {
        let id = self.id_tracker.next();
        self.add_thing_with_id_at_offset(offset, id, name, item)
    }

    pub fn freeze(self) -> FrozenSymtab {
        let id_tracker = self.id_tracker.clone();
        FrozenSymtab {
            inner: self,
            id_tracker,
        }
    }

    pub fn add_local_variable(&mut self, name: Loc<Identifier>) -> NameID {
        self.add_thing(
            crate::util::path_from_ident(name.clone()).inner,
            Thing::Variable(name),
        )
    }
    pub fn add_local_variable_at_offset(&mut self, offset: usize, name: Loc<Identifier>) -> NameID {
        self.add_thing_at_offset(
            offset,
            crate::util::path_from_ident(name.clone()).inner,
            Thing::Variable(name),
        )
    }

    /// Get the entity with the specified ID. Panics if no such entity is in the symtab
    pub fn entity_by_id(&self, id: &NameID) -> &Loc<EntityHead> {
        match self.items.get(&id) {
            Some(Thing::Entity(head)) => head,
            Some(other) => panic!("attempted to look up entity {} but it was {:?}", id, other),
            None => panic!("No thing entry for {:?}", id),
        }
    }
    pub fn pipeline_by_id(&self, id: &NameID) -> &Loc<PipelineHead> {
        match self.items.get(&id) {
            Some(Thing::Pipeline(head)) => head,
            Some(other) => panic!(
                "attempted to look up pipeline {} but it was {:?}",
                id, other
            ),
            None => panic!("No thing entry for {:?}", id),
        }
    }
    /// Get the function with the specified ID. Panics if no such entity is in the symtab
    pub fn function_by_id(&self, id: &NameID) -> &Loc<FunctionHead> {
        match self.items.get(&id) {
            Some(Thing::Function(head)) => head,
            Some(other) => panic!(
                "attempted to look up function {} but it was {:?}",
                id, other
            ),
            None => panic!("No thing entry for {:?}", id),
        }
    }
    /// Get the type with the specified ID. Panics if no such entity is in the symtab
    pub fn type_symbol_by_id(&self, id: &NameID) -> &Loc<TypeSymbol> {
        match self.items.get(&id) {
            Some(Thing::Type(t)) => t,
            Some(other) => panic!("attempted to look up type {} but it was {:?}", id, other),
            None => panic!("No thing entry for {:?}", id),
        }
    }

    pub fn has_symbol(&self, name: Path) -> bool {
        match self.lookup_id(&name.nowhere()) {
            Ok(_) => true,
            Err(Error::NoSuchSymbol(_)) => false,
            Err(Error::NotATypeSymbol(_, _)) => unreachable!(),
            Err(Error::NotAVariable(_, _)) => unreachable!(),
            Err(Error::NotAnEntity(_, _)) => unreachable!(),
            Err(Error::NotAPipeline(_, _)) => unreachable!(),
            Err(Error::NotAFunction(_, _)) => unreachable!(),
        }
    }

    pub fn lookup_type_symbol(
        &self,
        name: &Loc<Path>,
    ) -> Result<(NameID, &Loc<TypeSymbol>), Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Type(t) => Ok((id, t)),
            other => Err(Error::NotATypeSymbol(name.clone(), other.clone())),
        }
    }

    pub fn lookup_variable(&self, name: &Loc<Path>) -> Result<NameID, Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Variable(_) => Ok(id),
            other => Err(Error::NotAVariable(name.clone(), other.clone())),
        }
    }

    pub fn lookup_entity(&self, name: &Loc<Path>) -> Result<(NameID, &Loc<EntityHead>), Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Entity(head) => Ok((id, head)),
            other => Err(Error::NotAnEntity(name.clone(), other.clone())),
        }
    }

    pub fn lookup_id(&self, name: &Loc<Path>) -> Result<NameID, Error> {
        for tab in self.symbols.iter().rev() {
            if let Some(id) = tab.get(&name) {
                return Ok(id.clone());
            }
        }
        Err(Error::NoSuchSymbol(name.clone()))
    }
    pub fn lookup_pipeline(&self, name: &Loc<Path>) -> Result<(NameID, &Loc<PipelineHead>), Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Pipeline(head) => Ok((id, head)),
            other => Err(Error::NotAPipeline(name.clone(), other.clone())),
        }
    }
    pub fn lookup_function(&self, name: &Loc<Path>) -> Result<(NameID, &Loc<FunctionHead>), Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Function(decl) => Ok((id, decl)),
            other => Err(Error::NotAFunction(name.clone(), other.clone())),
        }
    }
}

/// A symbol table that can not have any new symbols added to it. The ID tracker can be used to
/// generate new names for for intermediate variables during codegen.
///
/// Mutable references to `SymbolTable` are never given out, ensuring that nothing can be added to
/// the symtab, thus avoiding collisions with things added using the Id tracker.
pub struct FrozenSymtab {
    inner: SymbolTable,
    pub id_tracker: IdTracker,
}

impl FrozenSymtab {
    pub fn symtab(&self) -> &SymbolTable {
        &self.inner
    }

    pub fn new_name(&mut self, description: Path) -> NameID {
        NameID(self.id_tracker.next(), description)
    }
}
