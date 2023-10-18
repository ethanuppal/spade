use hir::symbol_table::{SymbolTable, TypeDeclKind, TypeSymbol};
use local_impl::local_impl;
use spade_ast as ast;
use spade_hir as hir;

use crate::Result;

#[local_impl]
impl IsPort for ast::TypeSpec {
    #[tracing::instrument(skip(symtab))]
    fn is_port(&self, symtab: &SymbolTable) -> Result<bool> {
        match self {
            ast::TypeSpec::Tuple(inner) => {
                for t in inner {
                    if t.is_port(symtab)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            ast::TypeSpec::Array { inner, size: _ } => inner.is_port(symtab),
            ast::TypeSpec::Named(name, _) => {
                let (_, symbol) = symtab.lookup_type_symbol(name)?;

                match &symbol.inner {
                    TypeSymbol::Declared(_, kind) => match kind {
                        TypeDeclKind::Struct { is_port } => Ok(*is_port),
                        TypeDeclKind::Enum => Ok(false),
                        TypeDeclKind::Primitive { is_port } => Ok(*is_port),
                    },
                    TypeSymbol::GenericArg { traits: _ } => Ok(false),
                    TypeSymbol::GenericInt => Ok(false),
                }
            }
            ast::TypeSpec::Unit(_) => Ok(false),
            ast::TypeSpec::Backward(_) => Ok(true),
            ast::TypeSpec::Inverted(_) => Ok(true),
            ast::TypeSpec::Wire(_) => Ok(true),
        }
    }
}
