use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};

pub fn ast_ident(name: &str) -> Loc<Identifier> {
    Identifier(name.to_string()).nowhere()
}

pub fn ast_path(name: &str) -> Loc<Path> {
    Path(vec![ast_ident(name)]).nowhere()
}

#[macro_export]
/// A type specification with a specified path and optional generic arguments
macro_rules! tspec {
    ( $( $base:expr ),*$(; $( $arg:expr ),* )? ) => {
        ast::TypeSpec::Named(
            Path(vec![ $( ast_ident($base) ),* ]).nowhere(),
            vec![ $( $( $arg ),* )?]
        ).nowhere()
    }
}

#[macro_export]
macro_rules! aparams {
    ( $( ( $name:expr, $type:expr ) ),* $(,)? ) => {
        ast::ParameterList(
            vec![ $(( ast_ident($name), $type )),* ]
        )
    }
}
