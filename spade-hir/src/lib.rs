pub mod expression;
pub mod symbol_table;
pub mod testutil;
pub mod util;

pub use expression::{Argument, ArgumentKind, ExprKind, Expression};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, NameID},
};

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
    Binding(Loc<NameID>, Option<Loc<TypeSpec>>, Loc<Expression>),
    Register(Loc<Register>),
}
impl WithLocation for Statement {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub name: Loc<NameID>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<TypeSpec>>,
}
impl WithLocation for Register {}

/// Type params have both an identifier and a NameID since they go through the
/// ast lowering process in a few separate steps, and the identifier needs to be
/// re-added to the symtab multiple times
#[derive(PartialEq, Debug, Clone)]
pub enum TypeParam {
    TypeName(Identifier, NameID),
    Integer(Identifier, NameID),
}
impl WithLocation for TypeParam {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    /// An integer value
    Integer(u128),
    /// Another type
    TypeSpec(TypeSpec),
}
impl WithLocation for TypeExpression {}

/// A specification of a type to be used. For example, the types of input/output arguments the type
/// of fields in a struct etc.
#[derive(PartialEq, Debug, Clone)]
pub enum TypeSpec {
    /// The type is a declared type (struct, enum, typedef etc.) with n arguments
    Declared(Loc<NameID>, Vec<Loc<TypeExpression>>),
    /// Tye type is a generic argument visible in the current scope
    Generic(Loc<NameID>),
    /// The type is a tuple of other variables
    Tuple(Vec<Loc<TypeSpec>>),
    Unit(Loc<()>),
}
impl WithLocation for TypeSpec {}

// Quick functions for creating types wihtout typing so much
impl TypeSpec {
    pub fn unit() -> Self {
        TypeSpec::Unit(().nowhere())
    }
}

/// Declaration of an enum
#[derive(PartialEq, Debug, Clone)]
pub struct Enum {
    pub options: Vec<(Loc<NameID>, ParameterList)>,
}
impl WithLocation for Enum {}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeDeclKind {
    Enum(Loc<Enum>),
}

/// A declaration of a new type
#[derive(PartialEq, Debug, Clone)]
pub struct TypeDeclaration {
    pub name: Loc<NameID>,
    pub kind: TypeDeclKind,
    pub generic_args: Vec<Loc<TypeParam>>,
}
impl WithLocation for TypeDeclaration {}

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub name: Loc<NameID>,
    pub head: EntityHead,
    // This is needed here because the head does not have NameIDs
    pub inputs: Vec<(NameID, Loc<TypeSpec>)>,
    pub body: Loc<Expression>,
}
impl WithLocation for Entity {}

#[derive(PartialEq, Debug, Clone)]
pub struct ParameterList(pub Vec<(Loc<Identifier>, Loc<TypeSpec>)>);

impl ParameterList {
    // Look up the type of an argument. Panics if no such argument exists
    pub fn arg_type(&self, name: &Identifier) -> TypeSpec {
        for (arg, ty) in &self.0 {
            if &arg.inner == name {
                return ty.inner.clone();
            }
        }
        panic!(
            "Tried to get type of an argument which is not part of the entity. {}",
            name
        )
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct FunctionHead {
    pub inputs: ParameterList,
    pub output_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Identifier>,
}
impl WithLocation for FunctionHead {}

#[derive(PartialEq, Debug, Clone)]
pub struct EntityHead {
    pub inputs: ParameterList,
    pub output_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Identifier>,
}
impl WithLocation for EntityHead {}

#[derive(PartialEq, Debug, Clone)]
pub struct PipelineHead {
    pub depth: Loc<usize>,
    pub inputs: ParameterList,
    pub output_type: Option<Loc<TypeSpec>>,
}
impl WithLocation for PipelineHead {}

#[derive(PartialEq, Debug, Clone)]
pub struct PipelineBinding {
    pub name: Loc<NameID>,
    pub type_spec: Option<Loc<TypeSpec>>,
    pub value: Loc<Expression>,
}
impl WithLocation for PipelineBinding {}

#[derive(PartialEq, Debug, Clone)]
pub struct PipelineStage {
    pub bindings: Vec<Loc<PipelineBinding>>,
}
impl WithLocation for PipelineStage {}

#[derive(PartialEq, Debug, Clone)]
pub struct Pipeline {
    pub name: Loc<NameID>,
    // The inputs to the pipeline as visible locally, rather than the inputs
    // as visible externally in the PipelineHead
    pub inputs: Vec<(NameID, Loc<TypeSpec>)>,
    pub body: Vec<Loc<PipelineStage>>,
    pub result: Loc<Expression>,
    pub depth: Loc<u128>,
    pub output_type: Loc<TypeSpec>,
}
impl WithLocation for Pipeline {}

/// Items are things typically present at the top level of a module such as
/// entities, pipelines, submodules etc.
#[derive(PartialEq, Debug, Clone)]
pub enum Item {
    Entity(Loc<Entity>),
    Pipeline(Loc<Pipeline>),
}
impl WithLocation for Item {}

#[derive(PartialEq, Debug, Clone)]
pub struct ModuleBody {
    pub members: Vec<Item>,
}
