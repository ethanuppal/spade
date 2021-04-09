use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID, Path},
    symbol_table::SymbolTable as BaseSymbolTable,
};
use spade_hir::{EntityHead, PipelineHead, TypeParam};
use spade_types::BaseType;
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
}

/// Any named thing in the language
#[derive(PartialEq, Debug, Clone)]
pub enum Thing {
    /// Defintion of a named type
    Type(TypeSymbol),
    TraitDef(Loc<TraitDef>),
    Entity(Loc<EntityHead>),
    Pipeline(Loc<PipelineHead>),
    Variable(Loc<Identifier>),
}

impl Thing {
    pub fn kind_string(&self) -> &'static str {
        match self {
            Thing::Type(_) => "type",
            Thing::TraitDef(_) => "trait definition",
            Thing::Entity(_) => "entity",
            Thing::Variable(_) => "variable",
            Thing::Pipeline(_) => "pipeline",
        }
    }

    pub fn loc(&self) -> Loc<()> {
        match self {
            Thing::Type(TypeSymbol::Alias(i)) => i.loc(),
            Thing::Type(TypeSymbol::Param(i)) => i.loc(),
            Thing::TraitDef(i) => i.loc(),
            Thing::Entity(i) => i.loc(),
            Thing::Pipeline(i) => i.loc(),
            Thing::Variable(i) => i.loc(),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct FunctionDecl {
    pub name: Loc<Identifier>,
    pub self_arg: Option<Loc<()>>,
    pub inputs: Vec<(Loc<Identifier>, Loc<BaseType>)>,
    pub output_type: Loc<BaseType>,
}
impl WithLocation for FunctionDecl {}

#[derive(PartialEq, Debug, Clone)]
pub struct TraitDef {
    pub functions: Vec<Loc<FunctionDecl>>,
}
impl WithLocation for TraitDef {}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeSymbol {
    Alias(Loc<BaseType>),
    Param(Loc<TypeParam>),
}
impl WithLocation for TypeSymbol {}

pub type SymbolTable = BaseSymbolTable<Thing>;

pub trait SymbolTableExt {
    fn add_local_variable(&mut self, name: Loc<Identifier>) -> NameID;
    fn entity_by_id(&self, id: &NameID) -> &Loc<EntityHead>;
    fn has_symbol(&self, name: Path) -> bool;
    fn lookyp_type_symbol(&self, name: &Loc<Path>) -> Result<(NameID, &TypeSymbol), Error>;
    fn lookup_variable(&self, name: &Loc<Path>) -> Result<NameID, Error>;
    fn lookup_entity(&self, name: &Loc<Path>) -> Result<(NameID, &Loc<EntityHead>), Error>;
    fn lookup_id(&self, name: &Loc<Path>) -> Result<NameID, Error>;
    fn add_local_variable_at_offset(&mut self, offset: usize, name: Loc<Identifier>) -> NameID;
    fn lookup_pipeline(&self, name: &Loc<Path>) -> Result<(NameID, &Loc<PipelineHead>), Error>;
    fn pipeline_by_id(&self, id: &NameID) -> &Loc<PipelineHead>;
}

impl SymbolTableExt for SymbolTable {
    fn add_local_variable(&mut self, name: Loc<Identifier>) -> NameID {
        self.add_thing(
            crate::path_from_ident(name.clone()).inner,
            Thing::Variable(name),
        )
    }
    fn add_local_variable_at_offset(&mut self, offset: usize, name: Loc<Identifier>) -> NameID {
        self.add_thing_at_offset(
            offset,
            crate::path_from_ident(name.clone()).inner,
            Thing::Variable(name),
        )
    }

    /// Get the entity with the specified ID. Panics if no such entity is in the symtab
    fn entity_by_id(&self, id: &NameID) -> &Loc<EntityHead> {
        match self.items.get(&id) {
            Some(Thing::Entity(head)) => head,
            Some(other) => panic!("attempted to look up entity {} but it was {:?}", id, other),
            None => panic!("No thing entry for {:?}", id),
        }
    }
    fn pipeline_by_id(&self, id: &NameID) -> &Loc<PipelineHead> {
        match self.items.get(&id) {
            Some(Thing::Pipeline(head)) => head,
            Some(other) => panic!(
                "attempted to look up pipeline {} but it was {:?}",
                id, other
            ),
            None => panic!("No thing entry for {:?}", id),
        }
    }

    fn has_symbol(&self, name: Path) -> bool {
        match self.lookup_id(&name.nowhere()) {
            Ok(_) => true,
            Err(Error::NoSuchSymbol(_)) => false,
            Err(Error::NotATypeSymbol(_, _)) => unreachable!(),
            Err(Error::NotAVariable(_, _)) => unreachable!(),
            Err(Error::NotAnEntity(_, _)) => unreachable!(),
            Err(Error::NotAPipeline(_, _)) => unreachable!(),
        }
    }

    fn lookyp_type_symbol(&self, name: &Loc<Path>) -> Result<(NameID, &TypeSymbol), Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Type(t) => Ok((id, t)),
            other => Err(Error::NotATypeSymbol(name.clone(), other.clone())),
        }
    }

    fn lookup_variable(&self, name: &Loc<Path>) -> Result<NameID, Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Variable(_) => Ok(id),
            other => Err(Error::NotAVariable(name.clone(), other.clone())),
        }
    }

    fn lookup_entity(&self, name: &Loc<Path>) -> Result<(NameID, &Loc<EntityHead>), Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Entity(head) => Ok((id, head)),
            other => Err(Error::NotAnEntity(name.clone(), other.clone())),
        }
    }

    fn lookup_id(&self, name: &Loc<Path>) -> Result<NameID, Error> {
        for tab in self.symbols.iter().rev() {
            if let Some(id) = tab.get(&name) {
                return Ok(id.clone());
            }
        }
        Err(Error::NoSuchSymbol(name.clone()))
    }
    fn lookup_pipeline(&self, name: &Loc<Path>) -> Result<(NameID, &Loc<PipelineHead>), Error> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Pipeline(head) => Ok((id, head)),
            other => Err(Error::NotAPipeline(name.clone(), other.clone())),
        }
    }
}
