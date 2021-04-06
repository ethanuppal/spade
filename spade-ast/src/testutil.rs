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
