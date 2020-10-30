use std::collections::HashMap;

use crate::global_symbols::GlobalSymbols;
use crate::hir::Block;
use crate::hir::Path;
use crate::hir::{Entity, Item};
use crate::location_info::Loc;
use crate::types::Type;

pub enum TypeVar {
    Known(Loc<Type>),
    Unknown(u64),
}

enum TypedExpression {
    Id(u64),
    Name(Path),
}

pub struct TypeEquation {
    lhs: TypedExpression,
    rhs: TypeVar,
}

impl TypeEquation {
    fn new(lhs: TypedExpression, rhs: TypeVar) -> Self {
        Self { lhs, rhs }
    }
}

pub struct TypeState<'a> {
    next_type_id: u64,
    equations: Vec<TypeEquation>,
    global_symbols: &'a GlobalSymbols,
}

impl<'a> TypeState<'a> {
    pub fn new(global_symbols: &'a GlobalSymbols) -> Self {
        Self {
            next_type_id: 0,
            equations: vec![],
            global_symbols,
        }
    }

    /// Visit an item to assign type variables and equations to every subexpression
    /// in the item
    pub fn visit_item(&mut self, item: &Item) {
        match item {
            Item::Entity(e) => self.visit_entity(&e.inner),
        }
    }

    pub fn visit_entity(&mut self, entity: &Entity) {
        // Create equations for all inputs
        for (name, t) in &entity.inputs {
            self.equations.push(TypeEquation::new(
                TypedExpression::Name(name.clone().to_path()),
                TypeVar::Known(t.clone()),
            ))
        }

        // Equate the type of the block with the return type of the entity
    }

    pub fn visit_block(&mut self, block: &Block) {
        unimplemented!()
    }
}

// https://eli.thegreenplace.net/2018/type-inference/
