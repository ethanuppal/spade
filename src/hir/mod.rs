pub mod expression;
pub mod identifier;
pub mod path;

pub use expression::{ExprKind, Expression};
pub use identifier::Identifier;
pub use path::Path;

use crate::location_info::{Loc, WithLocation};

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
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<Type>>,
}
impl WithLocation for Register {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeParam {
    TypeName(Identifier),
    Integer(Loc<Identifier>),
}
impl TypeParam {
    pub fn name(&self) -> &Identifier {
        match self {
            TypeParam::TypeName(name) => name,
            TypeParam::Integer(name_loc) => &name_loc.inner,
        }
    }
}
impl WithLocation for TypeParam {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    Integer(u128),
    Ident(Path),
}
impl WithLocation for TypeExpression {}

#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Concrete(Path),
    Generic(Loc<Path>, Vec<Loc<TypeExpression>>),
    Unit,
}
impl WithLocation for Type {}

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
    pub type_params: Vec<Loc<TypeParam>>,
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
