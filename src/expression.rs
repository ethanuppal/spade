use crate::identifier::Identifier;

pub enum Expression {
    Add(Identifier, Identifier),
}
