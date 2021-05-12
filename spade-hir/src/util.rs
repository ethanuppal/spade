use spade_common::{
    location_info::{Loc, WithLocation},
    name::Path,
};

use crate::Identifier;

pub fn path_from_ident(ident: Loc<Identifier>) -> Loc<Path> {
    Path(vec![ident.clone()]).at_loc(&ident)
}
