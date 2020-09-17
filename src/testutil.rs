use crate::ast;
use crate::hir;
use crate::location_info::{Loc, WithLocation};

pub fn ast_ident(name: &str) -> Loc<ast::Identifier> {
    ast::Identifier(name.to_string()).nowhere()
}

pub fn hir_ident(name: &str) -> Loc<hir::Identifier> {
    hir::Identifier::Named(name.to_string()).nowhere()
}
