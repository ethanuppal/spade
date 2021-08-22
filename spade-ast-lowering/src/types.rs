use hir::symbol_table::{SymbolTable, Thing, TypeSymbol};
use spade_ast as ast;
use spade_common::{location_info::WithLocation, name::Path};
use spade_hir as hir;

use crate::{visit_type_param, Result};

pub fn lower_type_declaration(
    decl: &ast::TypeDeclaration,
    namespace: &Path,
    symtab: &mut SymbolTable,
) -> Result<hir::TypeDeclaration> {
    symtab.new_scope();
    // Add the generic types declared here to the symtab
    for param in &decl.generic_args {
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

    let ast::TypeDeclaration {
        name,
        kind,
        generic_args,
    } = decl;

    let this_path = namespace.push_ident(name.clone());

    let (id, _) = symtab.lookup_type_symbol(&this_path.clone().at_loc(&name))
        .expect("Found no entry for typedecl in symtab. Was it not visited during global symbol collection?");

    let generic_args = generic_args
        .iter()
        .map(|param| param.try_map_ref(|p| visit_type_param(p, symtab)))
        .collect::<Result<Vec<_>>>()?;

    let kind = match kind {
        ast::TypeDeclKind::Enum(e) => {
            hir::TypeDeclKind::Enum(e.try_map_ref::<_, crate::Error, _>(|e| {
                let ast::Enum { name: _, options } = e;

                let options = options
                    .iter()
                    .map(|(name, params)| {
                        let params = crate::visit_parameter_list(
                            params.as_ref().unwrap_or(&ast::ParameterList(vec![])),
                            symtab,
                        )?;

                        let option_path = this_path.clone().push_ident(name.clone());

                        let (id, _) = symtab
                            .lookup_function(&option_path.nowhere())
                            .expect("Expected enum variant to be in symtab as a function");

                        Ok((id.at_loc(name), params.clone()))
                    })
                    .collect::<Result<Vec<_>>>()?;

                Ok(hir::Enum { options })
            })?)
        }
    };

    symtab.close_scope();

    let declaration = hir::TypeDeclaration {
        name: id.at_loc(&name),
        kind,
        generic_args,
    };

    Ok(declaration)
}
