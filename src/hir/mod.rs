pub mod expression;

pub use expression::{ExprKind, Expression};

use crate::{
    ast,
    location_info::{Loc, WithLocation},
};

/// Anything named will get assigned a unique name ID in order to avoid caring
/// about scopes HIR has been generated. This is the type of those IDs
///
/// The associated string is only used for formating when printing. The hash and eq
/// methods do not use it
#[derive(Clone)]
pub struct NameID(pub u64, pub ast::Path);

impl WithLocation for NameID {}

impl std::cmp::PartialEq for NameID {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl std::cmp::Eq for NameID {}

impl std::hash::Hash for NameID {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl std::fmt::Debug for NameID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}#{}", self.1, self.0)
    }
}
impl std::fmt::Display for NameID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.1)
    }
}

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
    Binding(Loc<NameID>, Option<Loc<Type>>, Loc<Expression>),
    Register(Loc<Register>),
}
impl WithLocation for Statement {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub name: Loc<NameID>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<Type>>,
}
impl WithLocation for Register {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeParam {
    TypeName,
    Integer,
}
impl WithLocation for TypeParam {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    Integer(u128),
    Ident(NameID),
}
impl WithLocation for TypeExpression {}

#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Concrete(NameID),
    Generic(Loc<NameID>, Vec<Loc<TypeExpression>>),
    Unit,
}
impl WithLocation for Type {}

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub name: Loc<NameID>,
    pub head: EntityHead,
    pub body: Loc<Expression>,
}
impl WithLocation for Entity {}

#[derive(PartialEq, Debug, Clone)]
pub struct EntityHead {
    pub inputs: Vec<(NameID, Loc<Type>)>,
    pub output_type: Loc<Type>,
    pub type_params: Vec<ast::Identifier>,
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
