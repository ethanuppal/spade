use thiserror::Error;

use crate::identifier::Identifier;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Attempting to bind twice to the name {0}")]
    DuplicateBinding(Identifier),
}
