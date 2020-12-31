use crate::ast;
use crate::hir;
use crate::location_info::{Loc, WithLocation};

pub fn ast_ident(name: &str) -> Loc<ast::Identifier> {
    ast::Identifier(name.to_string()).nowhere()
}

pub fn hir_ident(name: &str) -> Loc<hir::Identifier> {
    hir::Identifier::Named(name.to_string()).nowhere()
}

pub fn ast_path(name: &str) -> Loc<ast::Path> {
    ast::Path(vec![ast_ident(name)]).nowhere()
}
pub fn hir_path(name: &str) -> Loc<hir::Path> {
    hir::Path(vec![hir_ident(name)]).nowhere()
}

#[macro_export]
macro_rules! assert_matches {
    ($lhs:expr, $pattern:pat) => {
        if let $pattern = $lhs {
        } else {
            panic!("{:?} does not match the specified pattern", $lhs)
        }
    };
}
