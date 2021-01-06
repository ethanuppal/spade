pub mod expression;
pub mod identifier;
pub mod path;

pub use expression::{ExprKind, Expression};
pub use identifier::Identifier;
pub use path::Path;

use crate::location_info::{Loc, WithLocation};
use crate::types::Type;

/**
  Representation of the language with most language constructs still present, with
  more correctness guaranatees than the AST, such as types actually existing.
*/

#[derive(PartialEq, Debug, Clone)]
pub struct Block {
    pub statements: Vec<Loc<Statement>>,
    pub result: Loc<Expression>,
}
impl WithLocation for Block {}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Binding(Loc<Identifier>, Option<Loc<Type>>, Loc<Expression>),
    Register(Loc<Register>),
}
impl WithLocation for Statement {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub name: Loc<Identifier>,
    pub clock: Loc<Path>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<Type>>,
}
impl WithLocation for Register {}

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub name: Loc<Identifier>,
    pub head: EntityHead,
    pub body: Loc<Expression>,
}
impl WithLocation for Entity {}

#[derive(PartialEq, Debug, Clone)]
pub struct EntityHead {
    pub inputs: Vec<(Loc<Identifier>, Loc<Type>)>,
    pub output_type: Loc<Type>,
}
impl WithLocation for EntityHead {}

/// Items are things typically present at the top level of a module such as
/// entities, pipelines, submodules etc.
#[derive(PartialEq, Debug, Clone)]
pub enum Item {
    Entity(Loc<Entity>),
}
impl WithLocation for Item {}

#[derive(PartialEq, Debug, Clone)]
pub struct ModuleBody {
    pub members: Vec<Item>,
}
