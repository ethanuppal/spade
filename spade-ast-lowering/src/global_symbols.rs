use spade_ast as ast;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::Path,
};

use crate::{Error, symbol_table::{GenericArg, SymbolTable, Thing, TypeSymbol}};

/// Collect global symbols as a first pass before generating HIR
pub fn gather_symbols(
    module: &ast::ModuleBody,
    namespace: &Path,
    symtab: &mut SymbolTable,
) -> Result<(), Error> {
    for item in &module.members {
        visit_item(item, namespace, symtab)?;
    }

    Ok(())
}

pub fn visit_item(
    item: &ast::Item,
    namespace: &Path,
    symtab: &mut SymbolTable,
) -> Result<(), Error> {
    match item {
        ast::Item::Entity(e) => {
            visit_entity(&e, namespace, symtab)?;
        }
        ast::Item::Pipeline(p) => {
            visit_pipeline(&p, namespace, symtab)?;
        }
        ast::Item::TraitDef(_) => {
            todo!("Trait definitions are unsupported")
        }
        ast::Item::Type(t) => {
            visit_type_declaration(t, namespace, symtab)?;
        }
    }
    Ok(())
}

pub fn visit_entity(
    e: &Loc<ast::Entity>,
    namespace: &Path,
    symtab: &mut SymbolTable,
) -> Result<(), Error> {
    let head = crate::entity_head(&e, symtab)?;

    let path = namespace.push_ident(e.name.clone());

    symtab.add_thing(path, Thing::Entity(head.at_loc(e)));

    Ok(())
}

pub fn visit_pipeline(
    p: &Loc<ast::Pipeline>,
    namespace: &Path,
    symtab: &mut SymbolTable,
) -> Result<(), Error> {
    let head = crate::pipelines::pipeline_head(&p, symtab)?;

    let path = namespace.push_ident(p.name.clone());

    symtab.add_thing(path, Thing::Pipeline(head.at_loc(p)));

    Ok(())
}

pub fn visit_type_declaration(
    t: &Loc<ast::TypeDeclaration>,
    namespace: &Path,
    symtab: &mut SymbolTable
) -> Result<(), Error> {
    let path = namespace.push_ident(t.name.clone());

    let args = t.generic_args
        .iter()
        .map(|arg| match &arg.inner {
            ast::TypeParam::TypeName(n) => GenericArg::TypeName(n.clone()),
            ast::TypeParam::Integer(n) => GenericArg::Number(n.inner.clone())
        }.at_loc(&arg.loc()))
        .collect();

    symtab.add_thing(path, Thing::Type(TypeSymbol::Declared(args).at_loc(&t)));

    Ok(())
}
