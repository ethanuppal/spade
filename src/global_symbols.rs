use std::collections::HashMap;

use thiserror::Error;

use crate::ast::Entity;
use crate::hir::Path;
use crate::location_info::Loc;
use crate::types::{self, Type};

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("Duplicate name {name}. Previously defined at {prev:?}")]
    DuplicateName {
        name: Path,
        prev: Loc<()>,
        now: Loc<()>,
    },
    #[error("Type error")]
    TypeError(#[from] types::Error),
}

pub struct GlobalSymbols {
    inner: HashMap<Path, (Loc<()>, Type)>,
}

impl GlobalSymbols {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn add_entity(&mut self, path: Path, e: Loc<Entity>) -> Result<(), Error> {
        let loc = e.loc();
        // Figure out the type of the entity
        let params = e
            .inner
            .inputs
            .iter()
            .map(|i| i.1.inner.clone())
            .map(Type::convert_from_ast)
            .collect::<Result<Vec<_>, _>>()?;

        let return_type = Type::convert_from_ast(e.inner.output_type.inner)?;

        let prev = self.inner.insert(
            path.clone(),
            (loc, Type::Entity(params, Box::new(return_type))),
        );

        match prev {
            Some(prev) => Err(Error::DuplicateName {
                name: path,
                prev: prev.0,
                now: loc,
            }),
            None => Ok(()),
        }
    }
}
