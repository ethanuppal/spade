use std::collections::HashMap;

use crate::hir::Path;
use crate::types::Type;

pub enum TypeKind {
    Known(Type),
    Unknown(u64),
}

enum TypedExpression {
    Id(u64),
    Name(Path),
}

pub struct TypeMap {
    // Map between a subexpression or identifier and a type variable
    inner: HashMap<TypedExpression, u64>,
}

// https://eli.thegreenplace.net/2018/type-inference/
