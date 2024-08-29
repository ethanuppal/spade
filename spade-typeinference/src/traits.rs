use crate::equation::TypeVar;
use spade_common::name::NameID;
use spade_hir::{ImplBlock, TraitName};
use std::collections::HashMap;

#[derive(Clone)]
pub struct TraitImpl {
    pub name: TraitName,
    pub type_params: Vec<TypeVar>,
    pub impl_block: ImplBlock,
}

#[derive(Clone)]
pub struct TraitImplList {
    pub inner: HashMap<NameID, Vec<TraitImpl>>,
}

impl TraitImplList {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }
}
