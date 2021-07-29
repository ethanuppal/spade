use hir::ItemList;
use spade_ast as ast;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::Path,
};
use spade_hir as hir;
use spade_hir::FunctionHead;

use crate::Error;
use spade_hir::symbol_table::{GenericArg, SymbolTable, Thing, TypeSymbol};

/// Collect global symbols as a first pass before generating HIR
pub fn gather_symbols(
    module: &ast::ModuleBody,
    namespace: &Path,
    symtab: &mut SymbolTable,
    item_list: &mut ItemList,
) -> Result<(), Error> {
    // Start by visiting each item and adding types to the symtab. These are needed
    // for signatures of other things which is why this has to be done first
    for item in &module.members {
        if let ast::Item::Type(t) = item {
            visit_type_declaration(t, namespace, symtab)?;
        }
    }

    // Then visit all the items adding their heads to the symtab
    for item in &module.members {
        visit_item(item, namespace, symtab, item_list)?;
    }

    Ok(())
}

pub fn visit_item(
    item: &ast::Item,
    namespace: &Path,
    symtab: &mut SymbolTable,
    item_list: &mut ItemList,
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
            re_visit_type_declaration(t, namespace, symtab, item_list)?;
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
    symtab: &mut SymbolTable,
) -> Result<(), Error> {
    let path = namespace.push_ident(t.name.clone());

    let args = t
        .generic_args
        .iter()
        .map(|arg| {
            match &arg.inner {
                ast::TypeParam::TypeName(n) => GenericArg::TypeName(n.inner.clone()),
                ast::TypeParam::Integer(n) => GenericArg::Number(n.inner.clone()),
            }
            .at_loc(&arg.loc())
        })
        .collect();

    symtab.add_thing(
        path.clone(),
        Thing::Type(TypeSymbol::Declared(args).at_loc(&t)),
    );

    Ok(())
}

/// Visit type declarations a second time, primarily to add enum variants to the symtab.
/// This can not be done in the same pass as normal type declaration visiting as other types
/// may be present in the declaration
pub fn re_visit_type_declaration(
    t: &Loc<ast::TypeDeclaration>,
    namespace: &Path,
    symtab: &mut SymbolTable,
    items: &mut ItemList,
) -> Result<(), Error> {
    // Add the generic types declared here to the symtab
    for param in &t.generic_args {
        match &param.inner {
            ast::TypeParam::TypeName(name) => {
                symtab.add_thing(
                    Path(vec![name.clone()]),
                    Thing::Type(TypeSymbol::GenericArg.at_loc(&param)),
                );
            }
            ast::TypeParam::Integer(name) => {
                symtab.add_thing(
                    Path(vec![name.clone()]),
                    Thing::Type(TypeSymbol::GenericInt.at_loc(&param)),
                );
            }
        }
    }

    // Add things like enum variants to the symtab
    match &t.inner.kind {
        ast::TypeDeclKind::Enum(e) => {
            let path = namespace.push_ident(t.name.clone()).nowhere();
            let (id, _) = symtab.lookup_type_symbol(&path).expect(&format!(
                "Failed to look up type {}. It was probably not added to the symtab",
                path
            ));
            for (i, option) in e.options.iter().enumerate() {
                let path = path.clone().push_ident(option.0.clone());

                let parameter_list = option
                    .1
                    .clone()
                    .map(|l| crate::visit_parameter_list(&l, symtab))
                    .unwrap_or_else(|| Ok(hir::ParameterList(vec![])))?;

                let head = FunctionHead {
                    inputs: parameter_list,
                    output_type: Some(
                        hir::TypeSpec::Declared(
                            id.clone().at_loc(&t.name),
                            vec![], // TODO: Handle generics
                        )
                        .at_loc(&t.name),
                    ),
                    type_params: vec![], // TODO: Handle generics
                }
                .at_loc(&option.0);

                let function_name = symtab.add_thing(path.clone(), Thing::Function(head));

                items.executables.insert(
                    function_name,
                    hir::ExecutableItem::EnumInstance {
                        base_enum: id.clone(),
                        variant: i,
                    },
                );
            }
        }
    }

    Ok(())
}
