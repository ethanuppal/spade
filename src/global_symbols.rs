use std::collections::HashMap;

use thiserror::Error;

use crate::location_info::Loc;
use crate::types::{self, Type};
use crate::{ast, hir::Path};
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
        let (name, item) = match item {
            Item::Entity(entity) => {
                let name = visit_identifier(&entity.name);

                let head = entity.try_map_ref(entity_head)?;

                (name, GlobalItem::Entity(head))
            }
            Item::TraitDef(def) => {
                let trait_name = visit_identifier(&def.name);
                (
                    trait_name,
                    GlobalItem::TraitDef(def.try_map_ref(Self::visit_trait_def)?),
                )
            }
        };

        let new_path = mod_path.with_ident(name);
        self.symbols.insert(new_path, item);

        Ok(())
    }

    pub fn visit_trait_def(def: &ast::TraitDef) -> Result<TraitDef> {
        let functions = def
            .functions
            .iter()
            .map(|func_loc| {
                func_loc.try_map_ref(|func| {
                    let inputs = func
                        .inputs
                        .iter()
                        .map(|(n, t)| {
                            Ok((
                                n.map_ref(visit_identifier),
                                t.try_map_ref(Type::convert_from_ast)?,
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    Ok(FunctionDecl {
                        name: func.name.map_ref(visit_identifier),
                        self_arg: func.self_arg,
                        inputs,
                        output_type: func.return_type.try_map_ref(Type::convert_from_ast)?,
                    })
                })
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(TraitDef { functions })
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
                    type_params: vec![],
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

    #[test]
    fn trait_defintions_are_found() {
        let module = ModuleBody {
            members: vec![Item::TraitDef(
                ast::TraitDef {
                    name: ast_ident("TestTrait"),
                    functions: vec![ast::FunctionDecl {
                        name: ast_ident("fn1"),
                        self_arg: Some(Loc::nowhere(())),
                        inputs: vec![
                            (ast_ident("a"), ast::Type::UnitType.nowhere()),
                            (ast_ident("b"), ast::Type::UnitType.nowhere()),
                        ],
                        return_type: ast::Type::UnitType.nowhere(),
                        type_params: vec![],
                    }
                    .nowhere()],
                }
                .nowhere(),
            )],
        }
        .nowhere();

        let mut symbols = Symbols::new();

        symbols
            .visit_module(Path::from_strs(&[]), &module)
            .expect("failed to visit module");

        let expected = GlobalItem::TraitDef(
            TraitDef {
                functions: vec![FunctionDecl {
                    name: hir_ident("fn1"),
                    self_arg: Some(Loc::nowhere(())),
                    inputs: vec![
                        (hir_ident("a"), types::Type::Unit.nowhere()),
                        (hir_ident("b"), types::Type::Unit.nowhere()),
                    ],
                    output_type: types::Type::Unit.nowhere(),
                }
                .nowhere()],
            }
            .nowhere(),
        );

        assert_eq!(
            symbols.lookup(Path::from_strs(&["TestTrait"])),
            Some(&expected)
        );
    }
}
