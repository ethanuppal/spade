use spade_common::{id_tracker::IdTracker, location_info::Loc, name::Path, location_info::WithLocation};
use spade_ast as ast;
use spade_hir as hir;

use crate::symbol_table::SymbolTable;
use crate::Result;

// Functions for lowering type declarations


pub fn visit_typedecl(
    pipeline: &Loc<ast::Pipeline>,
    namespace: &Path,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<Loc<hir::TypeDeclaration>> {
    unimplemented!()
}

#[cfg(test)]
mod tests {
    use ast::testutil::{ast_ident, ast_path};
    use spade_common::name::testutil::name_id;

    use super::*;

    #[test]
    fn type_declaration_visiting_works() {
        let input = ast::TypeDeclaration {
            name: ast_ident("test"),
            kind: ast::TypeDeclKind::Enum(ast::Enum {
                name: ast_ident("test"),
                options: vec![
                    // No arguments
                    (ast_ident("A"), None),
                    // Builtin type with no args
                    (ast_ident("B"), Some(vec![
                        ast::TypeSpec::Named(ast_path("bool"), vec![]).nowhere()
                    ])),
                    // Builtin type with no args
                    (ast_ident("C"), Some(vec![
                        ast::TypeSpec::Named(ast_path("int"), vec![
                            ast::TypeExpression::Integer(10).nowhere()
                        ]).nowhere()
                    ]))
                ],
            }.nowhere()),
            generic_args: vec![],
        };

        // Populate the symtab with builtins
        let mut symtab = SymbolTable::new();
        let mut id_tracker = IdTracker::new();

        let expected = hir::TypeDeclaration {
            name: name_id(0, "test"),
            kind: hir::TypeDeclKind::Enum(hir::Enum {
                options: vec![
                    (name_id(1, "A"), vec![]),
                    (
                        name_id(2, "B"),
                        hir::TypeSpec::Declared(name_id())
                    ),
                ]
            }.nowhere()),
            generic_args: (),
        };

        unimplemented!()
    }

    #[test]
    fn type_declarations_with_generics_work() {
        unimplemented!()
    }
}
