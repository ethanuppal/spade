use hir::symbol_table::SymbolTable;
use spade_ast as ast;
use spade_common::{location_info::WithLocation, name::Path};
use spade_hir as hir;

use crate::{visit_type_param, Result};

pub fn visit_typedecl(
    decl: &ast::TypeDeclaration,
    namespace: &Path,
    symtab: &mut SymbolTable,
) -> Result<hir::TypeDeclaration> {
    let ast::TypeDeclaration {
        name,
        kind,
        generic_args,
    } = decl;

    let this_path = namespace.push_ident(name.clone());

    // TODO: Should this use expect or return an error?
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

    Ok(hir::TypeDeclaration {
        name: id.at_loc(name),
        kind,
        generic_args,
    })
}

#[cfg(test)]
mod tests {
    use ast::{
        aparams,
        testutil::{ast_ident, ast_path},
        TypeParam,
    };
    use hir::{dtype, hparams, testutil::t_num};
    use spade_common::name::testutil::{name_id, name_id_p};

    use super::*;

    #[test]
    fn type_declaration_visiting_works() {
        let input = ast::TypeDeclaration {
            name: ast_ident("test"),
            kind: ast::TypeDeclKind::Enum(
                ast::Enum {
                    name: ast_ident("test"),
                    options: vec![
                        // No arguments
                        (ast_ident("A"), None),
                        // Builtin type with no args
                        (
                            ast_ident("B"),
                            Some(ast::ParameterList(vec![(
                                ast_ident("x"),
                                ast::TypeSpec::Named(ast_path("bool"), vec![]).nowhere(),
                            )])),
                        ),
                        // Builtin type with no args
                        (
                            ast_ident("C"),
                            Some(ast::ParameterList(vec![(
                                ast_ident("x"),
                                ast::TypeSpec::Named(
                                    ast_path("int"),
                                    vec![ast::TypeExpression::Integer(10).nowhere()],
                                )
                                .nowhere(),
                            )])),
                        ),
                    ],
                }
                .nowhere(),
            ),
            generic_args: vec![],
        }
        .nowhere();

        // Populate the symtab with builtins
        let mut symtab = SymbolTable::new();

        let namespace = Path(vec![]);

        crate::builtins::populate_symtab(&mut symtab);
        crate::global_symbols::visit_type_declaration(&input, &namespace, &mut symtab)
            .expect("Failed to visit global symbol");
        crate::global_symbols::re_visit_type_declaration(&input, &namespace, &mut symtab)
            .expect("Failed to re-visit global symbol");

        let expected = hir::TypeDeclaration {
            name: name_id(0, "test"),
            kind: hir::TypeDeclKind::Enum(
                hir::Enum {
                    options: vec![
                        (name_id_p(1, &["test", "A"]), hir::ParameterList(vec![])),
                        (
                            name_id_p(2, &["test", "B"]),
                            hparams![("x", dtype!(symtab => "bool"))],
                        ),
                        (
                            name_id_p(3, &["test", "C"]),
                            hparams![("x", dtype!(symtab => "int"; (t_num(10))))],
                        ),
                    ],
                }
                .nowhere(),
            ),
            generic_args: vec![],
        };

        assert_eq!(
            visit_typedecl(&input, &namespace, &mut symtab),
            Ok(expected)
        );
    }

    #[test]
    fn type_declarations_with_generics_work() {
        let input = ast::TypeDeclaration {
            name: ast_ident("test"),
            kind: ast::TypeDeclKind::Enum(
                ast::Enum {
                    name: ast_ident("test"),
                    options: vec![
                        // Builtin type with no args
                        (ast_ident("B"), Some(aparams!(("a", ast::tspec!("T"))))),
                    ],
                }
                .nowhere(),
            ),
            generic_args: vec![TypeParam::TypeName(ast_ident("T")).nowhere()],
        }
        .nowhere();

        // Populate the symtab with builtins
        let mut symtab = SymbolTable::new();

        let namespace = Path(vec![]);

        crate::builtins::populate_symtab(&mut symtab);
        crate::global_symbols::visit_type_declaration(&input, &namespace, &mut symtab)
            .expect("Failed to visit global symbol");
        crate::global_symbols::re_visit_type_declaration(&input, &namespace, &mut symtab)
            .expect("Failed to visit global symbol");

        let expected = hir::TypeDeclaration {
            name: name_id(0, "test"),
            kind: hir::TypeDeclKind::Enum(
                hir::Enum {
                    options: vec![(
                        name_id_p(2, &["test", "B"]),
                        hparams![("a", hir::TypeSpec::Generic(name_id(3, "T")).nowhere())],
                    )],
                }
                .nowhere(),
            ),
            generic_args: vec![hir::TypeParam::TypeName(
                ast_ident("T").inner,
                name_id(3, "T").inner,
            )
            .nowhere()],
        };

        assert_eq!(
            visit_typedecl(&input, &namespace, &mut symtab),
            Ok(expected)
        );
    }
}
