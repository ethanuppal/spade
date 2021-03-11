use spade_common::location_info::{Loc, WithLocation};

use crate::ast;

pub fn ast_ident(name: &str) -> Loc<ast::Identifier> {
    ast::Identifier(name.to_string()).nowhere()
}

pub fn ast_path(name: &str) -> Loc<ast::Path> {
    ast::Path(vec![ast_ident(name)]).nowhere()
}
