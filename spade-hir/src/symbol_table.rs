use crate::{EntityHead, FunctionHead, ParameterList, PipelineHead, TypeParam, TypeSpec};
use colored::Colorize;
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
    #[error("Not a patternable type")]
    NotAPatternableType(Loc<Path>, Thing),
    #[error("Not a struct")]
    NotAStruct(Loc<Path>, Thing),
    #[error("Not a value")]
    NotAValue(Loc<Path>, Thing),
    #[error("Looked up target which is a type")]
    IsAType(Loc<Path>),
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

#[derive(PartialEq, Debug, Clone)]
pub struct StructCallable {
    pub self_type: Loc<TypeSpec>,
    pub params: ParameterList,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for StructCallable {}
impl StructCallable {
    pub fn as_function_head(&self) -> FunctionHead {
        FunctionHead {
            inputs: self.params.clone(),
            output_type: Some(self.self_type.clone()),
            type_params: self.type_params.clone(),
        }
    }
}

impl EntityHead {
    pub fn as_function_head(&self) -> FunctionHead {
        let EntityHead {
            inputs,
            type_params,
            output_type,
        } = self;
        FunctionHead {
            inputs: inputs.clone(),
            type_params: type_params.clone(),
            output_type: output_type.clone(),
        }
    }
}

impl FunctionHead {
    pub fn as_entity_head(&self) -> EntityHead {
        let FunctionHead {
            inputs,
            type_params,
            output_type,
        } = self;
        EntityHead {
            inputs: inputs.clone(),
            type_params: type_params.clone(),
            output_type: output_type.clone(),
        }
    }
}

/// Any named thing in the language which is not a type. Structs are here for instanciation
/// under the same NameID as the type
#[derive(PartialEq, Debug, Clone)]
pub enum Thing {
    /// Defintion of a named type
    Struct(Loc<StructCallable>),
    EnumVariant(Loc<EnumVariant>),
    Function(Loc<EntityHead>),
    Entity(Loc<EntityHead>),
    Pipeline(Loc<PipelineHead>),
    Variable(Loc<Identifier>),
    Alias(Loc<Path>),
}

impl Thing {
    pub fn kind_string(&self) -> &'static str {
        match self {
            Thing::Struct(_) => "struct",
            Thing::Entity(_) => "entity",
            Thing::Variable(_) => "variable",
            Thing::Pipeline(_) => "pipeline",
            Thing::Function(_) => "function",
            Thing::EnumVariant(_) => "enum variant",
            Thing::Alias(_) => "alias",
        }
    }

    pub fn loc(&self) -> Loc<()> {
        match self {
            Thing::Struct(i) => i.loc(),
            Thing::Entity(i) => i.loc(),
            Thing::Pipeline(i) => i.loc(),
            Thing::Variable(i) => i.loc(),
            Thing::Function(i) => i.loc(),
            Thing::EnumVariant(i) => i.loc(),
            Thing::Alias(i) => i.loc(),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum PatternableKind {
    Struct,
    Enum,
}
#[derive(PartialEq, Debug, Clone)]
pub struct Patternable {
    pub kind: PatternableKind,
    pub params: ParameterList,
}
impl WithLocation for Patternable {}

#[derive(Clone, Debug, PartialEq)]
pub enum GenericArg {
    TypeName(Identifier),
    Number(Identifier),
}
impl WithLocation for GenericArg {}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeDeclKind {
    Struct,
    Enum,
    Primitive,
}

/// A previously declared type symbol
#[derive(Clone, Debug, PartialEq)]
pub enum TypeSymbol {
    /// A fixed type that has been declared, like a typedef, enum or struct with the
    /// specified generic arguments
    Declared(Vec<Loc<GenericArg>>, TypeDeclKind),
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
///
/// Modules are managed by a special variable in the symtab. All names in the
/// symtab are absolute paths, that is `X` in `mod A{mod B {fn X}}` will only be
/// stored as `A::B::X`. All variables inside X will also have the full path
/// appended to them. This should however be invisilbe to the user.
pub struct SymbolTable {
    /// Each outer vec is a scope, inner vecs are symbols in that scope
    pub symbols: Vec<HashMap<Path, NameID>>,
    pub declarations: Vec<HashMap<Loc<Identifier>, DeclarationState>>,
    id_tracker: NameIdTracker,
    pub types: HashMap<NameID, Loc<TypeSymbol>>,
    pub things: HashMap<NameID, Thing>,
    /// The namespace which we are currently in. When looking up and adding symbols, this namespace
    /// is added to the start of the path, thus ensuring all paths are absolute. If a path is not
    /// found that path is also looked up in the global namespace
    namespace: Path,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            symbols: vec![HashMap::new()],
            declarations: vec![HashMap::new()],
            id_tracker: NameIdTracker::new(),
            types: HashMap::new(),
            things: HashMap::new(),
            namespace: Path(vec![]),
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

    /// Push an identifier onto the current namespace
    pub fn push_namespace(&mut self, new_ident: Loc<Identifier>) {
        self.namespace = self.namespace.push_ident(new_ident);
    }

    pub fn pop_namespace(&mut self) {
        self.namespace = self.namespace.pop();
    }

    pub fn current_namespace(&self) -> &Path {
        &self.namespace
    }

    /// Adds a thing to the scope at `current_scope - offset`. Panics if there is no such scope
    pub fn add_thing_with_id_at_offset(
        &mut self,
        offset: usize,
        id: u64,
        name: Path,
        item: Thing,
    ) -> NameID {
        let full_name = self.namespace.join(name);

        let name_id = NameID(id, full_name.clone());
        if self.things.contains_key(&name_id) {
            panic!("Duplicate nameID inserted, {}", id);
        }
        self.things.insert(name_id.clone(), item);

        if offset > self.symbols.len() {
            panic!("Not enough scopes to add symbol at offset {}", offset);
        }

        let index = self.symbols.len() - 1 - offset;
        self.symbols[index].insert(full_name, name_id.clone());

        name_id
    }

    /// Add a thing to the symtab with the specified NameID. The NameID must already be in
    /// the symtab when calling this function
    pub fn add_thing_with_name_id(&mut self, name_id: NameID, item: Thing) {
        self.things.insert(name_id, item);
    }

    pub fn add_thing_with_id(&mut self, id: u64, name: Path, item: Thing) -> NameID {
        self.add_thing_with_id_at_offset(0, id, name, item)
    }

    pub fn add_thing(&mut self, name: Path, item: Thing) -> NameID {
        let id = self.id_tracker.next();
        self.add_thing_with_id(id, name, item)
    }

    pub fn add_type_with_id(&mut self, id: u64, name: Path, t: Loc<TypeSymbol>) -> NameID {
        let full_name = self.namespace.join(name);
        let name_id = NameID(id, full_name.clone());
        if self.types.contains_key(&name_id) {
            panic!("Duplicate nameID for types, {}", id)
        }
        self.types.insert(name_id.clone(), t);
        self.symbols
            .last_mut()
            .unwrap()
            .insert(full_name, name_id.clone());
        name_id
    }

    pub fn add_type(&mut self, name: Path, t: Loc<TypeSymbol>) -> NameID {
        let id = self.id_tracker.next();
        self.add_type_with_id(id, name, t)
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
        let path = Path(vec![name.clone()]);
        self.add_thing(path, Thing::Variable(name))
    }
    pub fn add_local_variable_at_offset(&mut self, offset: usize, name: Loc<Identifier>) -> NameID {
        let path = Path(vec![name.clone()]);
        self.add_thing_at_offset(offset, path, Thing::Variable(name))
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
macro_rules! thing_accessors {
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
                match self.things.get(&id) {
                    $(Some($thing) => {$conversion})*,
                    Some(other) => panic!("attempted to look up {} but it was {:?}", stringify!($result), other),
                    None => panic!("No thing entry found for {:?}", id)
                }
            }

            /// Look up an item, with errors if the item is not currently in scope, or is not
            /// convertible to the return type.
            pub fn $lookup_name(&self, name: &Loc<Path>) -> Result<(NameID, Loc<$result>), LookupError> {
                let id = self.lookup_id(name)?;

                match self.things.get(&id) {
                    $(Some($thing) => {Ok((id, $conversion))})*,
                    Some(Thing::Alias(alias)) => self.$lookup_name(alias),
                    Some(other) => Err(LookupError::$err(name.clone(), other.clone())),
                    None => {
                        match self.types.get(&id) {
                            Some(_) => Err(LookupError::IsAType(name.clone())),
                            None => panic!("{:?} is in symtab but not a thign or type", id)
                        }
                    }
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
    thing_accessors! {
        entity_by_id, lookup_entity, EntityHead, NotAnEntity {
            Thing::Entity(head) => head.clone()
        },
        pipeline_by_id, lookup_pipeline, PipelineHead, NotAPipeline {
            Thing::Pipeline(head) => head.clone()
        },
        function_by_id, lookup_function, FunctionHead, NotAFunction {
            Thing::Function(head) => head.as_function_head().at_loc(&head),
            Thing::EnumVariant(variant) => variant.as_function_head().at_loc(&variant),
            Thing::Struct(s) => s.as_function_head().at_loc(&s),
        },
        enum_variant_by_id, lookup_enum_variant, EnumVariant, NotAnEnumVariant {
            Thing::EnumVariant(variant) => variant.clone()
        },
        patternable_type_by_id, lookup_patternable_type, Patternable, NotAPatternableType {
            Thing::EnumVariant(variant) => Patternable{
                kind: PatternableKind::Enum,
                params: variant.params.clone()
            }.at_loc(&variant),
            Thing::Struct(variant) => Patternable {
                kind: PatternableKind::Struct,
                params: variant.params.clone()
            }.at_loc(&variant),
        },
        struct_by_id, lookup_struct, StructCallable, NotAStruct {
            Thing::Struct(s) => s.clone()
        }
    }

    pub fn type_symbol_by_id(&self, id: &NameID) -> Loc<TypeSymbol> {
        match self.types.get(id) {
            Some(inner) => inner.clone(),
            None => panic!("No thing entry found for {:?}", id),
        }
    }

    pub fn lookup_type_symbol(
        &self,
        name: &Loc<Path>,
    ) -> Result<(NameID, Loc<TypeSymbol>), LookupError> {
        let id = self.lookup_id(name)?;

        match self.types.get(&id) {
            Some(tsym) => Ok((id, tsym.clone())),
            None => match self.things.get(&id) {
                Some(Thing::Alias(alias)) => self.lookup_type_symbol(alias),
                Some(thing) => Err(LookupError::NotATypeSymbol(name.clone(), thing.clone())),
                None => panic!("{:?} was in symtab but is neither a type nor a thing", id),
            },
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
            Err(LookupError::NotAPatternableType(_, _)) => unreachable!(),
            Err(LookupError::NotAnEnumVariant(_, _)) => unreachable!(),
            Err(LookupError::NotAStruct(_, _)) => unreachable!(),
            Err(LookupError::NotAValue(_, _)) => unreachable!(),
            Err(LookupError::IsAType(_)) => unreachable!(),
        }
    }

    pub fn lookup_variable(&self, name: &Loc<Path>) -> Result<NameID, LookupError> {
        let id = self.lookup_id(name)?;

        match self.things.get(&id) {
            Some(Thing::Variable(_)) => Ok(id),
            Some(other) => Err(LookupError::NotAVariable(name.clone(), other.clone())),
            None => match self.types.get(&id) {
                Some(_) => Err(LookupError::IsAType(name.clone())),
                None => panic!("{:?} is in symtab but not a thign or type", id),
            },
        }
    }

    pub fn lookup_id(&self, name: &Loc<Path>) -> Result<NameID, LookupError> {
        self.try_lookup_id(name)
            .ok_or_else(|| LookupError::NoSuchSymbol(name.clone()))
    }

    /// Returns the name ID of the provided path if that path exists and resolving
    /// all aliases along the way.
    pub fn try_lookup_final_id(&self, name: &Loc<Path>) -> Option<NameID> {
        let id = self.try_lookup_id(name);
        if let Some(id) = id {
            match self.things.get(&id) {
                Some(Thing::Alias(alias)) => self.try_lookup_final_id(alias),
                _ => Some(id),
            }
        } else {
            None
        }
    }

    pub fn try_lookup_id(&self, name: &Loc<Path>) -> Option<NameID> {
        // Look up things in the current namespace first
        let local_path = self.namespace.join(name.inner.clone());
        for tab in self.symbols.iter().rev() {
            if let Some(id) = tab.get(&local_path) {
                return Some(id.clone());
            }
        }

        // Then look up things in the absolute namespace. This is only needed at the
        // top scope as that's where all top level will be defined
        if let Some(id) = self.symbols.first().unwrap().get(name) {
            return Some(id.clone());
        }
        None
    }

    pub fn print_symbols(&self) {
        println!("=============================================================");
        println!("                      Symtab dump");
        println!("=============================================================");
        for (level, scope) in self.symbols.iter().enumerate() {
            let indent = (1..level + 1).map(|_| "\t").collect::<Vec<_>>().join("");
            println!(">>> new_scope",);

            for (path, name) in scope {
                println!(
                    "{indent}{path} => {name}",
                    path = format!("{path}").cyan(),
                    name = format!("{name:?}").yellow()
                );
            }
        }

        println!("Things:");
        for (name, thing) in &self.things {
            print!("{}: ", format!("{name:?}").purple());
            match thing {
                Thing::Struct(_) => println!("struct"),
                Thing::EnumVariant(_) => println!("enum variant"),
                Thing::Function(_) => println!("function"),
                Thing::Entity(_) => println!("entity"),
                Thing::Pipeline(_) => println!("pipeline"),
                Thing::Variable(_) => println!("variable"),
                Thing::Alias(to) => println!("{}", format!("alias => {to}").green()),
            }
        }

        println!("Types:");
        for (name, _) in &self.types {
            print!("{}: ", format!("{name:?}").purple());
            println!("type");
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
