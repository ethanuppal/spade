use spade_common::location_info::{Loc, WithLocation};
use spade_parser::ast;

use crate::{
    symbol_table::{SymbolTable, Thing},
    Error,
};

/// Collect global symbols as a first pass before generating HIR
pub fn gather_symbols(
    module: &ast::ModuleBody,
    namespace: &ast::Path,
    symtab: &mut SymbolTable,
) -> Result<(), Error> {
    for item in &module.members {
        visit_item(item, namespace, symtab)?;
    }

    Ok(())
}

pub fn visit_item(
    item: &ast::Item,
    namespace: &ast::Path,
    symtab: &mut SymbolTable,
) -> Result<(), Error> {
    match item {
        ast::Item::Entity(e) => {
            visit_entity(&e, namespace, symtab)?;
        }
        ast::Item::TraitDef(_) => {
            todo!("Trait definitions are unsupported")
        }
    }
    Ok(())
}

pub fn visit_entity(
    e: &Loc<ast::Entity>,
    namespace: &ast::Path,
    symtab: &mut SymbolTable,
) -> Result<(), Error> {
    let head = crate::entity_head(&e, symtab)?;

    let path = namespace.push_ident(e.name.clone());

    symtab.add_thing(path, Thing::Entity(head.at_loc(e)));

    Ok(())
}
