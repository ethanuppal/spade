use crate::{EntityHead, FunctionHead, ParameterList, PipelineHead, TypeParam, TypeSpec};
use spade_common::{
    id_tracker::NameIdTracker,
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID, Path},
};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum LookupError {
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
    #[error("Not an enum variant")]
    NotAnEnumVariant(Loc<Path>, Thing),
    #[error("Not a value")]
    NotAValue(Loc<Path>, Thing),
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum DeclarationError {
    #[error("Duplicate declaration")]
    DuplicateDeclaration {
        new: Loc<Identifier>,
        old: Loc<Identifier>,
    },
}

#[derive(PartialEq, Debug, Clone)]
pub struct EnumVariant {
    pub output_type: Loc<TypeSpec>,
    pub option: usize,
    pub params: ParameterList,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for EnumVariant {}

impl EnumVariant {
    pub fn as_function_head(&self) -> FunctionHead {
        FunctionHead {
            inputs: self.params.clone(),
            output_type: Some(self.output_type.clone()),
            type_params: self.type_params.clone(),
        }
    }
}

/// Any named thing in the language
#[derive(PartialEq, Debug, Clone)]
pub enum Thing {
    /// Defintion of a named type
    Type(Loc<TypeSymbol>),
    EnumVariant(Loc<EnumVariant>),
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
            Thing::EnumVariant(_) => "enum variant",
        }
    }

    pub fn loc(&self) -> Loc<()> {
        match self {
            Thing::Type(i) => i.loc(),
            Thing::Entity(i) => i.loc(),
            Thing::Pipeline(i) => i.loc(),
            Thing::Variable(i) => i.loc(),
            Thing::Function(i) => i.loc(),
            Thing::EnumVariant(i) => i.loc(),
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

#[derive(Clone, PartialEq)]
pub enum DeclarationState {
    Undefined(NameID),
    Defined(Loc<()>),
}
impl WithLocation for DeclarationState {}

/// A table of the symbols known to the program in the current scope. Names
/// are mapped to IDs which are then mapped to the actual things
pub struct SymbolTable {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    pub symbols: Vec<HashMap<Path, NameID>>,
    pub declarations: Vec<HashMap<Loc<Identifier>, DeclarationState>>,
    id_tracker: NameIdTracker,
    pub items: HashMap<NameID, Thing>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            symbols: vec![HashMap::new()],
            declarations: vec![HashMap::new()],
            id_tracker: NameIdTracker::new(),
            items: HashMap::new(),
        }
    }
    pub fn new_scope(&mut self) {
        self.symbols.push(HashMap::new());
        self.declarations.push(HashMap::new());
    }

    pub fn close_scope(&mut self) {
        self.symbols.pop();
        self.declarations.pop();
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
        let id_tracker = self.id_tracker.make_clone();
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

    pub fn add_declaration(&mut self, ident: Loc<Identifier>) -> Result<NameID, DeclarationError> {
        if let Some((old, _)) = self.declarations.last().unwrap().get_key_value(&ident) {
            Err(DeclarationError::DuplicateDeclaration {
                new: ident.clone(),
                old: old.clone(),
            })
        } else {
            let name_id = self.add_local_variable(ident.clone());
            self.declarations
                .last_mut()
                .unwrap()
                .insert(ident, DeclarationState::Undefined(name_id.clone()));
            Ok(name_id)
        }
    }

    pub fn get_declaration(&mut self, ident: &Loc<Identifier>) -> Option<Loc<DeclarationState>> {
        self.declarations
            .last()
            .unwrap()
            .get_key_value(ident)
            .map(|(k, v)| v.clone().at_loc(k))
    }

    pub fn mark_declaration_defined(&mut self, ident: Loc<Identifier>, definition_point: Loc<()>) {
        *self
            .declarations
            .last_mut()
            .unwrap()
            .get_mut(&ident)
            .unwrap() = DeclarationState::Defined(definition_point)
    }
}
macro_rules! item_accessors {
    (
        $(
            $by_id_name:ident,
            $lookup_name:ident,
            $result:path,
            $err:ident $(,)?
            {$($thing:pat => $conversion:expr),*$(,)?}
        ),*
    ) => {
        $(
            /// Look up an item and panic if the item is not in the symtab or if it is the wrong
            /// type
            pub fn $by_id_name(&self, id: &NameID) -> Loc<$result> {
                match self.items.get(&id) {
                    $(Some($thing) => {$conversion})*
                    Some(other) => panic!("attempted to look up {} but it was {:?}", stringify!($result), other),
                    None => panic!("No thing entry found for {:?}", id)
                }
            }

            /// Look up an item, with errors if the item is not currently in scope, or is not
            /// convertible to the return type.
            pub fn $lookup_name(&self, name: &Loc<Path>) -> Result<(NameID, Loc<$result>), LookupError> {
                let id = self.lookup_id(name)?;

                match self.items.get(&id).unwrap() {
                    $($thing => {Ok((id, $conversion))})*
                    other => Err(LookupError::$err(name.clone(), other.clone())),
                }
            }
        )*
    }
}

impl SymbolTable {
    // Define accessors for accessing items. *_by_id looks up things under the
    // assumption that the name is in the symtab, and that it is the specified type.
    // If this is not true, it panics.
    //
    // lookup_* looks up items by path, and returns the NameID and item if successful.
    // If the path is not in scope, or the item is not the right kind, returns an error.
    item_accessors! {
        entity_by_id, lookup_entity, EntityHead, NotAnEntity {
            Thing::Entity(head) => head.clone()
        },
        pipeline_by_id, lookup_pipeline, PipelineHead, NotAPipeline {
            Thing::Pipeline(head) => head.clone()
        },
        function_by_id, lookup_function, FunctionHead, NotAFunction {
            Thing::Function(head) => head.clone(),
            Thing::EnumVariant(variant) => variant.as_function_head().at_loc(&variant),
        },
        type_symbol_by_id, lookup_type_symbol, TypeSymbol, NotATypeSymbol {
            Thing::Type(t) => t.clone(),
        },
        enum_variant_by_id, lookup_enum_variant, EnumVariant, NotAnEnumVariant {
            Thing::EnumVariant(variant) => variant.clone()
        }
    }
    pub fn has_symbol(&self, name: Path) -> bool {
        match self.lookup_id(&name.nowhere()) {
            Ok(_) => true,
            Err(LookupError::NoSuchSymbol(_)) => false,
            Err(LookupError::NotATypeSymbol(_, _)) => unreachable!(),
            Err(LookupError::NotAVariable(_, _)) => unreachable!(),
            Err(LookupError::NotAnEntity(_, _)) => unreachable!(),
            Err(LookupError::NotAPipeline(_, _)) => unreachable!(),
            Err(LookupError::NotAFunction(_, _)) => unreachable!(),
            Err(LookupError::NotAnEnumVariant(_, _)) => unreachable!(),
            Err(LookupError::NotAValue(_, _)) => unreachable!(),
        }
    }

    pub fn lookup_variable(&self, name: &Loc<Path>) -> Result<NameID, LookupError> {
        let id = self.lookup_id(name)?;

        match self.items.get(&id).unwrap() {
            Thing::Variable(_) => Ok(id),
            other => Err(LookupError::NotAVariable(name.clone(), other.clone())),
        }
    }

    pub fn lookup_id(&self, name: &Loc<Path>) -> Result<NameID, LookupError> {
        for tab in self.symbols.iter().rev() {
            if let Some(id) = tab.get(&name) {
                return Ok(id.clone());
            }
        }
        Err(LookupError::NoSuchSymbol(name.clone()))
    }
}

/// A symbol table that can not have any new symbols added to it. The ID tracker can be used to
/// generate new names for for intermediate variables during codegen.
///
/// Mutable references to `SymbolTable` are never given out, ensuring that nothing can be added to
/// the symtab, thus avoiding collisions with things added using the Id tracker.
pub struct FrozenSymtab {
    inner: SymbolTable,
    pub id_tracker: NameIdTracker,
}

impl FrozenSymtab {
    pub fn symtab(&self) -> &SymbolTable {
        &self.inner
    }

    pub fn new_name(&mut self, description: Path) -> NameID {
        NameID(self.id_tracker.next(), description)
    }
}
