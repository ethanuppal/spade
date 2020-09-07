use std::collections::HashMap;

use crate::expression::Expression;
use crate::identifier::Identifier;

pub enum BindTarget {
    Signal(Expression),
}

/// A map between names and named things.
pub struct Bindings {
    inner: HashMap<Identifier, BindTarget>,
    // Stuff for keeping track of annonymous bindings
    // next_id: usize,
    // TODO: Later, we'll need some way to not create duplicate constants.
}

impl Bindings {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
            // next_id: 0,
        }
    }

    pub fn add_named(&mut self, name: Identifier, target: BindTarget) {
        self.inner.insert(name, target);
    }
}
