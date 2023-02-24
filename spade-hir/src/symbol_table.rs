use std::collections::HashMap;

use colored::Colorize;
use num::BigInt;
use serde::{Deserialize, Serialize};
use tap::prelude::*;
use thiserror::Error;
use tracing::trace;

use spade_common::id_tracker::NameIdTracker;
use spade_common::location_info::{Loc, WithLocation};
use spade_common::name::{Identifier, NameID, Path};
use spade_diagnostics::diagnostic::Diagnostic;

use crate::{FunctionKind, ParameterList, TypeParam, TypeSpec, UnitHead, UnitKind};

#[derive(Debug, Clone, PartialEq)]
pub enum LookupError {
    NoSuchSymbol(Loc<Path>),
    NotATypeSymbol(Loc<Path>, Thing),
    NotAVariable(Loc<Path>, Thing),
    NotAUnit(Loc<Path>, Thing),
    NotAnEnumVariant(Loc<Path>, Thing),
    NotAPatternableType(Loc<Path>, Thing),
    NotAStruct(Loc<Path>, Thing),
    NotAValue(Loc<Path>, Thing),
    NotAComptimeValue(Loc<Path>, Thing),
    IsAType(Loc<Path>),
}

impl From<LookupError> for Diagnostic {
    fn from(lookup_error: LookupError) -> Diagnostic {
        match &lookup_error {
            LookupError::NoSuchSymbol(path) => {
                Diagnostic::error(path, format!("Use of undeclared name {path}"))
                    .primary_label("Undeclared name")
            }
            LookupError::IsAType(path) => {
                Diagnostic::error(path, format!("Unexpected type {path}"))
                    .primary_label("Unexpected type")
            }
            LookupError::NotATypeSymbol(path, got)
            | LookupError::NotAVariable(path, got)
            | LookupError::NotAUnit(path, got)
            | LookupError::NotAnEnumVariant(path, got)
            | LookupError::NotAPatternableType(path, got)
            | LookupError::NotAStruct(path, got)
            | LookupError::NotAValue(path, got)
            | LookupError::NotAComptimeValue(path, got) => {
                let expected = match lookup_error {
                    LookupError::NotATypeSymbol(_, _) => "a type symbol",
                    LookupError::NotAVariable(_, _) => "a variable",
                    LookupError::NotAUnit(_, _) => "a unit",
                    LookupError::NotAnEnumVariant(_, _) => "an enum variant",
                    LookupError::NotAPatternableType(_, _) => "a patternable type",
                    LookupError::NotAStruct(_, _) => "a struct",
                    LookupError::NotAValue(_, _) => "a value",
                    LookupError::NotAComptimeValue(_, _) => "a compile time value",
                    LookupError::NoSuchSymbol(_) | LookupError::IsAType(_) => unreachable!(),
                };
                // FIXME: We can sometimes do suggestions depending on `got`. For example, a struct/enum variant can be initialized,
                // an entity can be instantiated, ...
                let hint = match lookup_error {
                    LookupError::NotAComptimeValue(_, _) => {
                        Some("compile time values can be defined with $config <name> = value")
                    }
                    _ => None,
                };
                let mut diagnostic =
                    Diagnostic::error(path, format!("Expected {path} to be {expected}"))
                        .primary_label(format!("Expected {expected}"))
                        .secondary_label(got.loc(), format!("{path} is a {}", got.kind_string()));
                if let Some(hint) = hint {
                    diagnostic.add_help(hint);
                }
                diagnostic
            }
        }
    }
}

impl LookupError {
    fn with_path(self, path: Loc<Path>) -> Self {
        macro_rules! match_replace_path {
            ( $( $variant:ident $old_items:tt => $new_items:tt ),* $(,)? ) => {
                match self {
                    $(
                        LookupError::$variant $old_items => LookupError::$variant $new_items,
                    )*
                }
            };
        }

        match_replace_path! {
            NoSuchSymbol(_) => (path),
            NotATypeSymbol(_, thing) => (path, thing),
            NotAVariable(_, thing) => (path, thing),
            NotAUnit(_, thing) => (path, thing),
            NotAnEnumVariant(_, thing) => (path, thing),
            NotAPatternableType(_, thing) => (path, thing),
            NotAStruct(_, thing) => (path, thing),
            NotAValue(_, thing) => (path, thing),
            NotAComptimeValue(_, thing) => (path, thing),
            IsAType(_) => (path),
        }
    }
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum UniqueNameError {
    #[error("Multiple definitions of {new}")]
    MultipleDefinitions { new: Loc<Path>, prev: Loc<()> },
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct EnumVariant {
    pub name: Loc<Identifier>,
    pub output_type: Loc<TypeSpec>,
    pub option: usize,
    pub params: ParameterList,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for EnumVariant {}

impl EnumVariant {
    pub fn as_unit_head(&self) -> UnitHead {
        UnitHead {
            name: self.name.clone(),
            inputs: self.params.clone(),
            output_type: Some(self.output_type.clone()),
            type_params: self.type_params.clone(),
            unit_kind: UnitKind::Function(FunctionKind::Enum).at_loc(&self.name),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct StructCallable {
    pub name: Loc<Identifier>,
    pub self_type: Loc<TypeSpec>,
    pub params: ParameterList,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for StructCallable {}
impl StructCallable {
    pub fn as_unit_head(&self) -> UnitHead {
        UnitHead {
            name: self.name.clone(),
            inputs: self.params.clone(),
            output_type: Some(self.self_type.clone()),
            type_params: self.type_params.clone(),
            unit_kind: UnitKind::Function(FunctionKind::Struct).at_loc(&self.name),
        }
    }
}

/// Any named thing in the language which is not a type. Structs are here for instantiation
/// under the same NameID as the type
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum Thing {
    /// Definition of a named type
    Struct(Loc<StructCallable>),
    EnumVariant(Loc<EnumVariant>),
    Unit(Loc<UnitHead>),
    Variable(Loc<Identifier>),
    Alias {
        path: Loc<Path>,
        in_namespace: Path,
    },
    PipelineStage(Loc<Identifier>),
    ComptimeConfig(Loc<BigInt>),
}

impl Thing {
    pub fn kind_string(&self) -> &'static str {
        match self {
            Thing::Struct(_) => "struct",
            Thing::Unit(_) => "unit",
            Thing::Variable(_) => "variable",
            Thing::EnumVariant(_) => "enum variant",
            Thing::Alias { .. } => "alias",
            Thing::PipelineStage(_) => "pipeline stage",
            Thing::ComptimeConfig(_) => "$config",
        }
    }

    /// The Loc of the entire Thing.
    pub fn loc(&self) -> Loc<()> {
        match self {
            Thing::Struct(i) => i.loc(),
            Thing::Variable(i) => i.loc(),
            Thing::Unit(i) => i.loc(),
            Thing::EnumVariant(i) => i.loc(),
            Thing::Alias {
                path,
                in_namespace: _,
            } => path.loc(),
            Thing::PipelineStage(i) => i.loc(),
            Thing::ComptimeConfig(val) => val.loc(),
        }
    }

    /// The Loc where the name of the thing is defined.
    pub fn name_loc(&self) -> Loc<()> {
        match self {
            Thing::Struct(s) => s.name.loc(),
            Thing::EnumVariant(v) => v.name.loc(),
            Thing::Unit(f) => f.name.loc(),
            Thing::Variable(v) => v.loc(),
            Thing::Alias {
                path,
                in_namespace: _,
            } => path.loc(),
            Thing::PipelineStage(_) => todo!(),
            Thing::ComptimeConfig(_) => todo!(),
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

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum GenericArg {
    TypeName(Identifier),
    Number(Identifier),
}
impl WithLocation for GenericArg {}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum TypeDeclKind {
    Struct { is_port: bool },
    Enum,
    Primitive { is_port: bool },
}

impl TypeDeclKind {
    pub fn normal_struct() -> Self {
        TypeDeclKind::Struct { is_port: false }
    }
    pub fn struct_port() -> Self {
        TypeDeclKind::Struct { is_port: true }
    }
}

/// A previously declared type symbol
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum TypeSymbol {
    /// A fixed type that has been declared, like a typedef, enum or struct with the
    /// specified generic arguments
    Declared(Vec<Loc<GenericArg>>, TypeDeclKind),
    /// A generic type present in the current scope
    GenericArg,
    GenericInt,
}
impl WithLocation for TypeSymbol {}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
#[derive(Debug, Serialize, Deserialize)]
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
    /// The namespace which `lib` refers to currently.
    base_namespace: Path,
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
            base_namespace: Path(vec![]),
        }
    }
    #[tracing::instrument(skip_all)]
    pub fn new_scope(&mut self) {
        self.symbols.push(HashMap::new());
        self.declarations.push(HashMap::new());
    }

    #[tracing::instrument(skip_all)]
    pub fn close_scope(&mut self) {
        self.symbols.pop();
        self.declarations.pop();
    }

    /// Push an identifier onto the current namespace
    #[tracing::instrument(skip_all, fields(%new_ident))]
    pub fn push_namespace(&mut self, new_ident: Loc<Identifier>) {
        self.namespace = self.namespace.push_ident(new_ident);
    }

    #[tracing::instrument(skip_all)]
    pub fn pop_namespace(&mut self) {
        self.namespace = self.namespace.pop();
    }

    pub fn current_namespace(&self) -> &Path {
        &self.namespace
    }

    pub fn set_base_namespace(&mut self, base_namespace: Path) {
        self.base_namespace = base_namespace
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

    #[tracing::instrument(skip_all, fields(?name))]
    pub fn add_unique_thing(&mut self, name: Loc<Path>, item: Thing) -> Result<NameID, Diagnostic> {
        self.ensure_is_unique(&name)?;
        Ok(self.add_thing(name.inner, item))
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

    pub fn add_unique_type(
        &mut self,
        name: Loc<Path>,
        t: Loc<TypeSymbol>,
    ) -> Result<NameID, Diagnostic> {
        self.ensure_is_unique(&name)?;

        Ok(self.add_type(name.inner, t))
    }

    #[tracing::instrument(skip_all, fields(?name, ?target))]
    pub fn add_alias(&mut self, name: Loc<Path>, target: Loc<Path>) -> Result<NameID, Diagnostic> {
        self.ensure_is_unique(&name)?;
        let absolute_path = if let Some(lib_relative) = target.inner.lib_relative() {
            self.base_namespace.join(lib_relative)
        } else {
            target.inner.clone()
        };
        let path = absolute_path.between(name.file_id, &name, &target);
        Ok(self.add_thing(
            name.inner,
            Thing::Alias {
                path,
                in_namespace: self.current_namespace().clone(),
            },
        ))
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

    pub fn add_declaration(&mut self, ident: Loc<Identifier>) -> Result<NameID, Diagnostic> {
        let declared_more_than_once = |new, old| {
            Diagnostic::error(new, "Variable declared more than once")
                .primary_label("This variable has been declared more than once")
                .secondary_label(old, "Previously declared here")
        };
        // Check if a variable with this name already exists
        if let Some(id) = self.try_lookup_id(&Path(vec![ident.clone()]).at_loc(&ident)) {
            if let Some(Thing::Variable(prev)) = self.things.get(&id) {
                return Err(declared_more_than_once(ident, prev).into());
            }
        }

        if let Some((old, _)) = self.declarations.last().unwrap().get_key_value(&ident) {
            Err(declared_more_than_once(ident, old).into())
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

    pub fn get_undefined_declarations(&self) -> Vec<Loc<Identifier>> {
        self.declarations
            .last()
            .unwrap()
            .iter()
            .filter_map(|(ident, state)| match state {
                DeclarationState::Undefined(_) => Some(ident.clone()),
                DeclarationState::Defined(_) => None,
            })
            .collect()
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
                    $(
                        Some($thing) => {$conversion}
                    )*,
                    Some(other) => panic!("attempted to look up {} but it was {:?}", stringify!($result), other),
                    None => panic!("No thing entry found for {:?}", id)
                }
            }

            /// Look up an item, with errors if the item is not currently in scope, or is not
            /// convertible to the return type.
            #[tracing::instrument(level = "trace", skip_all, fields(%name.inner, %name.span, %name.file_id))]
            pub fn $lookup_name(&self, name: &Loc<Path>) -> Result<(NameID, Loc<$result>), LookupError> {
                let id = self.lookup_id(name).tap(|id| trace!(?id))?;

                match self.things.get(&id).tap(|thing| trace!(?thing)) {
                    $(
                        Some($thing) => {Ok((id, $conversion))}
                    )*,
                    // Item is aliased. Same lookup but on the path.
                    Some(Thing::Alias{path, in_namespace}) => self.$lookup_name(path)
                        .or_else(|_| {
                            // If the alias returns an error (wrong type / does not exist), try
                            // the same lookup but starting from the namespace the use is
                            // located in.
                            self.$lookup_name(&in_namespace.join(path.inner.clone()).at_loc(path))
                        })
                        .map_err(|e| {
                            // If the lookup on the alias also errors, replace the path in the
                            // error with the original lookup.
                            e.with_path(name.clone())
                        }),
                    Some(other) => Err(LookupError::$err(name.clone(), other.clone())),
                    None => {
                        match self.types.get(&id) {
                            Some(_) => Err(LookupError::IsAType(name.clone())),
                            None => panic!("{:?} is in symtab but not a thing or type", id)
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
        unit_by_id, lookup_unit, UnitHead, NotAUnit {
            Thing::Unit(head) => head.clone(),
            Thing::EnumVariant(variant) => variant.as_unit_head().at_loc(variant),
            Thing::Struct(s) => s.as_unit_head().at_loc(s),
        },
        enum_variant_by_id, lookup_enum_variant, EnumVariant, NotAnEnumVariant {
            Thing::EnumVariant(variant) => variant.clone()
        },
        patternable_type_by_id, lookup_patternable_type, Patternable, NotAPatternableType {
            Thing::EnumVariant(variant) => Patternable{
                kind: PatternableKind::Enum,
                params: variant.params.clone()
            }.at_loc(variant),
            Thing::Struct(variant) => Patternable {
                kind: PatternableKind::Struct,
                params: variant.params.clone()
            }.at_loc(variant),
        },
        struct_by_id, lookup_struct, StructCallable, NotAStruct {
            Thing::Struct(s) => s.clone()
        },
        comptime_config_by_id, lookup_comptime_config, BigInt, NotAComptimeValue {
            Thing::ComptimeConfig(val) => val.clone()
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
                Some(Thing::Alias {
                    path: alias,
                    in_namespace,
                }) => self.lookup_type_symbol(alias).or_else(|_| {
                    self.lookup_type_symbol(&in_namespace.join(alias.inner.clone()).at_loc(alias))
                }),
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
            Err(LookupError::NotAUnit(_, _)) => unreachable!(),
            Err(LookupError::NotAPatternableType(_, _)) => unreachable!(),
            Err(LookupError::NotAnEnumVariant(_, _)) => unreachable!(),
            Err(LookupError::NotAStruct(_, _)) => unreachable!(),
            Err(LookupError::NotAValue(_, _)) => unreachable!(),
            Err(LookupError::NotAComptimeValue(_, _)) => unreachable!(),
            Err(LookupError::IsAType(_)) => unreachable!(),
        }
    }

    /// Look up the previous definition of `name` returning None if no
    /// such definition exists. Only an absolute path in the root name space is checked
    /// as this is intended to be used for item definitions
    pub fn ensure_is_unique(&self, name: &Loc<Path>) -> Result<(), Diagnostic> {
        let full_path = self.current_namespace().join(name.inner.clone());

        let prev = self
            .symbols
            .first()
            .unwrap()
            .get(&full_path)
            .and_then(|id| {
                self.things
                    .get(id)
                    .map(|thing| thing.name_loc())
                    .or_else(|| self.types.get(id).map(|t| t.loc()))
            });

        match prev {
            Some(prev) => Err(Diagnostic::error(name, "Multiple items with the same name")
                .primary_label(format!("{} is defined multiple times", name))
                .secondary_label(prev, "Previous definition here")),
            None => Ok(()),
        }
    }

    pub fn lookup_variable(&self, name: &Loc<Path>) -> Result<NameID, LookupError> {
        let id = self.lookup_id(name)?;

        match self.things.get(&id) {
            Some(Thing::Variable(_)) => Ok(id),
            Some(other) => Err(LookupError::NotAVariable(name.clone(), other.clone())),
            None => match self.types.get(&id) {
                Some(_) => Err(LookupError::IsAType(name.clone())),
                None => panic!("{:?} is in symtab but not a thing or type", id),
            },
        }
    }

    /// Look up `name`. If it is defined and a variable, return that name. If it is defined
    /// but not a variable, return an error. If it is undefined, return None
    ///
    /// Intended for use if undefined variables should be declared
    pub fn try_lookup_variable(&self, name: &Loc<Path>) -> Result<Option<NameID>, LookupError> {
        let id = self.try_lookup_id(name);
        match id {
            Some(id) => match self.things.get(&id) {
                Some(Thing::Variable(_)) => Ok(Some(id)),
                Some(other) => Err(LookupError::NotAVariable(name.clone(), other.clone())),
                None => match self.types.get(&id) {
                    Some(_) => Err(LookupError::IsAType(name.clone())),
                    None => Ok(None),
                },
            },
            None => Ok(None),
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
                Some(Thing::Alias {
                    path: alias,
                    in_namespace,
                }) => self.try_lookup_final_id(alias).or_else(|| {
                    self.try_lookup_final_id(&in_namespace.join(alias.inner.clone()).at_loc(alias))
                }),
                _ => Some(id),
            }
        } else {
            None
        }
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn try_lookup_id(&self, name: &Loc<Path>) -> Option<NameID> {
        // The behaviour depends on whether or not the path is a library relative path (starting
        // with `lib`) or not. If it is, an absolute lookup of the path obtained by
        // substituting `lib` for the current `base_path` should be performed.
        //
        // If not, three lookups should be performed
        //  - The path in the root namespace
        //  - The path in the current namespace
        //  - The path in other use statements. For example, with
        //      ```
        //      use a::b;
        //
        //      b::c();
        //      ```
        //      A lookup for `b` is performed which returns an alias (a::b). From that, another
        //      lookup for a::b::c is performed.

        let absolute_path = if let Some(lib_relative) = name.lib_relative() {
            self.base_namespace.join(lib_relative).at_loc(name)
        } else {
            let local_path = self.namespace.join(name.inner.clone());
            for tab in self.symbols.iter().rev() {
                if let Some(id) = tab.get(&local_path) {
                    return Some(id.clone());
                }
            }

            if name.inner.0.len() > 1 {
                let base_name = name.inner.0.first().unwrap();

                if let Some(alias_id) =
                    self.try_lookup_id(&Path(vec![base_name.clone()]).at_loc(base_name))
                {
                    match self.things.get(&alias_id) {
                        Some(Thing::Alias {
                            path: alias_path,
                            in_namespace,
                        }) => {
                            // Pop the aliased bit of the path
                            let rest_path = Path(name.inner.0[1..].into());

                            // Compute the path of the use in the global namespace
                            // i.e. `mod a {use x;}` looks up `x`
                            let full_path = alias_path.join(rest_path);

                            // Compute the path of the use in the local namespace of the use
                            // i.e. `mod a {use x;}` looks up `a::x`
                            let path_in_namespace = in_namespace.join(full_path.clone());

                            return self
                                .try_lookup_id(&path_in_namespace.at_loc(name))
                                .or_else(|| self.try_lookup_id(&full_path.at_loc(name)));
                        }
                        _ => {}
                    }
                }
            }

            name.clone()
        };

        // Then look up things in the absolute namespace. This is only needed at the
        // top scope as that's where all top level will be defined
        if let Some(id) = self.symbols.first().unwrap().get(&absolute_path) {
            return Some(id.clone());
        }
        None
    }

    pub fn print_symbols(&self) {
        println!("=============================================================");
        println!("                      Symtab dump");
        println!("=============================================================");
        println!("Current namespace is `{}`", self.namespace);
        println!("Current base_namespace is `{}`", self.base_namespace);
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
                Thing::Unit(_) => println!("unit"),
                Thing::Variable(_) => println!("variable"),
                Thing::Alias { path, in_namespace } => {
                    println!("{}", format!("alias => {path} in {in_namespace}").green())
                }
                Thing::PipelineStage(stage) => println!("'{stage}"),
                Thing::ComptimeConfig(val) => println!("$config {}", val),
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
#[derive(Serialize, Deserialize)]
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

    /// Unfreeze the symtab, removing access to the underlying id_tracker and
    /// giving ownership of the symtab again
    pub fn unfreeze(self) -> SymbolTable {
        // Ensure that we will not generate any conflicting IDs by re combining
        // this with the new ID trakcer by ensuring that the new ID tracker is further
        // along than the symtabs
        SymbolTable {
            id_tracker: self.id_tracker,
            ..self.inner
        }
    }
}
