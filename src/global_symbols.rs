use std::collections::HashMap;

use thiserror::Error;

use crate::hir::Path;
use crate::location_info::Loc;
use crate::types::{self, Type};
use crate::{
    ast::Item,
    ast::ModuleBody,
    hir::{EntityHead, Identifier},
    location_info::WithLocation,
    semantic_analysis::{entity_head, visit_identifier},
};

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("Duplicate name {name}. Previously defined at {prev:?}")]
    DuplicateName {
        name: Path,
        prev: Loc<()>,
        now: Loc<()>,
    },
    #[error("Type error")]
    TypeError(#[from] types::Error),
    #[error("Semantic error")]
    HirError(#[from] crate::semantic_analysis::Error),
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(PartialEq, Debug, Clone)]
pub struct FunctionDecl {
    pub name: Loc<Identifier>,
    pub self_arg: Option<Loc<()>>,
    pub inputs: Vec<(Loc<Identifier>, Loc<Type>)>,
    pub output_type: Loc<Type>,
}
impl WithLocation for FunctionDecl {}

#[derive(PartialEq, Debug, Clone)]
pub struct TraitDef {
    pub functions: Vec<Loc<FunctionDecl>>,
}
impl WithLocation for TraitDef {}

#[derive(PartialEq, Debug, Clone)]
pub struct Module {
    items: Vec<GlobalItem>,
}

#[derive(PartialEq, Debug, Clone)]
pub enum GlobalItem {
    /// Defintion of a named type
    Type(Loc<Type>),
    TraitDef(Loc<TraitDef>),
    Entity(Loc<EntityHead>),
    Module(Loc<Module>),
}

pub struct Symbols {
    pub symbols: HashMap<Path, GlobalItem>,
}

impl Symbols {
    pub fn new() -> Self {
        Self {
            symbols: HashMap::new(),
        }
    }

    pub fn lookup(&self, needle: Path) -> Option<&GlobalItem> {
        self.symbols.get(&needle)
    }

    pub fn visit_module(&mut self, path: Path, body: &Loc<ModuleBody>) -> Result<()> {
        for item in &body.inner.members {
            self.visit_item(&path, item)?;
        }
        Ok(())
    }

    pub fn visit_item(&mut self, mod_path: &Path, item: &Item) -> Result<()> {
        match item {
            Item::Entity(entity) => {
                let name = visit_identifier(&entity.name);

                let head = entity.map_ref(|t| entity_head(t)).map_err(|e, _| e)?;

                self.symbols
                    .insert(mod_path.with_ident(name), GlobalItem::Entity(head));

                Ok(())
            }
            Item::TraitDef(_) => unimplemented![],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        ast::{self, Entity, Item},
        testutil::{ast_ident, ast_path, hir_ident},
    };

    #[test]
    fn entity_defintions_are_found() {
        let module = ModuleBody {
            members: vec![Item::Entity(
                Entity {
                    name: ast_ident("test"),
                    inputs: vec![
                        (ast_ident("a"), ast::Type::UnitType.nowhere()),
                        (ast_ident("b"), ast::Type::UnitType.nowhere()),
                    ],
                    output_type: ast::Type::UnitType.nowhere(),
                    body: ast::Expression::Identifier(ast_path("ignored")).nowhere(),
                }
                .nowhere(),
            )],
        }
        .nowhere();

        let mut symbols = Symbols::new();

        symbols
            .visit_module(Path::from_strs(&[]), &module)
            .expect("Failed to visit module");

        let expected = GlobalItem::Entity(
            EntityHead {
                inputs: vec![
                    (hir_ident("a"), types::Type::Unit.nowhere()),
                    (hir_ident("b"), types::Type::Unit.nowhere()),
                ],
                output_type: types::Type::Unit.nowhere(),
            }
            .nowhere(),
        );

        assert_eq!(symbols.lookup(Path::from_strs(&["test"])), Some(&expected));
    }
}
