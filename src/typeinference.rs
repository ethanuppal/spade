use std::collections::HashMap;

use crate::hir::Path;
use crate::types::Type;

pub enum TypeKind {
    Known(Type),
    Unknown(u64),
}

enum Thing {
    Id(u64),
    Name(Path),
}

pub struct TypeMap {
    inner: HashMap<u64, TypeKind>,
}
