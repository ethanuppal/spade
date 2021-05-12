use spade_common::location_info::{Loc, WithLocation};

/// A declared type.
/// The type name is the name as declared in the symtab which must be in scope with
/// the name `symtab`
#[macro_export]
macro_rules! dtype {
    ($symtab:expr => $base:expr$(; ($($arg:expr),*) )?) => {
        hir::TypeSpec::Declared(
            $symtab.lookup_id(&ast_path($base)).unwrap().nowhere(),
            vec![ $( $( $arg ),* )? ]
        ).nowhere()
    }
}

// TODO: Rename to t_num
/// A type level integer
pub fn t_num(size: u128) -> Loc<crate::TypeExpression> {
    crate::TypeExpression::Integer(size).nowhere()
}

#[macro_export]
macro_rules! hparams {
    ($(($name:expr, $type:expr)),*) => {
        hir::ParameterList(vec![$((ast_ident($name), $type)),*])
    }
}
