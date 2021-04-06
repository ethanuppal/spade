use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};

pub mod testutil;

#[derive(PartialEq, Debug, Clone)]
pub enum TypeExpression {
    TypeSpec(Box<Loc<TypeSpec>>),
    Integer(u128),
}
impl WithLocation for TypeExpression {}
#[derive(PartialEq, Debug, Clone)]
pub enum TypeSpec {
    Tuple(Vec<Loc<TypeSpec>>),
    Named(Loc<Path>, Vec<Loc<TypeExpression>>),
    Unit(Loc<()>),
}
impl WithLocation for TypeSpec {}

#[derive(PartialEq, Debug, Clone)]
pub enum NamedArgument {
    Full(Loc<Identifier>, Loc<Expression>),
    /// Binds a local variable to an argument with the same name
    Short(Loc<Identifier>),
}
impl WithLocation for NamedArgument {}

#[derive(PartialEq, Debug, Clone)]
pub enum ArgumentList {
    Positional(Vec<Loc<Expression>>),
    Named(Vec<NamedArgument>),
}
impl WithLocation for ArgumentList {}

#[derive(PartialEq, Debug, Clone)]
pub enum BinaryOperator {
    Add,
    Sub,
    Equals,
    Lt,
    Gt,
    LogicalAnd,
    LogicalOr,
    LeftShift,
    RightShift,
}

#[derive(PartialEq, Debug, Clone)]
pub enum Expression {
    Identifier(Loc<Path>),
    IntLiteral(u128),
    BoolLiteral(bool),
    TupleLiteral(Vec<Loc<Expression>>),
    TupleIndex(Box<Loc<Expression>>, Loc<u128>),
    If(
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
    BinaryOperator(Box<Loc<Expression>>, BinaryOperator, Box<Loc<Expression>>),
    Block(Box<Block>),
    EntityInstance(Loc<Path>, Loc<ArgumentList>),
}
impl WithLocation for Expression {}

#[derive(PartialEq, Debug, Clone)]
pub struct Block {
    pub statements: Vec<Loc<Statement>>,
    pub result: Loc<Expression>,
}
impl WithLocation for Block {}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Binding(Loc<Identifier>, Option<Loc<TypeSpec>>, Loc<Expression>),
    Register(Loc<Register>),
}
impl WithLocation for Statement {}

/// A generic type parameter
#[derive(PartialEq, Debug, Clone)]
pub enum TypeParam {
    TypeName(Identifier),
    Integer(Loc<Identifier>),
}
impl WithLocation for TypeParam {}

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub name: Loc<Identifier>,
    pub inputs: Vec<(Loc<Identifier>, Loc<TypeSpec>)>,
    pub output_type: Option<Loc<TypeSpec>>,
    /// The body is an expression for ID assignment purposes, but semantic analysis
    /// ensures that it is always a block.
    pub body: Loc<Expression>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for Entity {}

/// Modifiers on pipeline bindings which change the visibility of the binding
#[derive(PartialEq, Debug, Clone)]
pub enum PipelineBindModifier {
    Reg,
}
impl WithLocation for PipelineBindModifier {}
/// A variable binding inside a pipeline. These behave a bit differently
/// to standard bindings
#[derive(PartialEq, Debug, Clone)]
pub struct PipelineBinding {
    pub name: Loc<Identifier>,
    pub modifier: Option<Loc<PipelineBindModifier>>,
    pub type_spec: Option<Loc<TypeSpec>>,
    pub value: Loc<Expression>,
}
impl WithLocation for PipelineBinding {}

/// A single stage in a pipeline.
#[derive(PartialEq, Debug, Clone)]
pub struct PipelineStage {
    pub bindings: Vec<Loc<PipelineBinding>>,
    pub result: Option<Loc<Expression>>,
}
impl WithLocation for PipelineStage {}

#[derive(PartialEq, Debug, Clone)]
pub struct Pipeline {
    pub depth: Loc<u128>,
    /// Name of the local clock signal
    pub clock: Loc<Identifier>,
    pub name: Loc<Identifier>,
    pub inputs: Vec<(Loc<Identifier>, Loc<TypeSpec>)>,
    pub output_type: Option<Loc<TypeSpec>>,
    /// The body is a list of expression for ID assignment purposes, but semantic analysis
    /// ensures that it is always a block.
    pub stages: Vec<Loc<PipelineStage>>,
}
impl WithLocation for Pipeline {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub name: Loc<Identifier>,
    pub clock: Loc<Expression>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<TypeSpec>>,
}
impl WithLocation for Register {}

/// A definition of a function without a body.
#[derive(PartialEq, Debug, Clone)]
pub struct FunctionDecl {
    pub name: Loc<Identifier>,
    pub self_arg: Option<Loc<()>>,
    pub inputs: Vec<(Loc<Identifier>, Loc<TypeSpec>)>,
    pub return_type: Option<Loc<TypeSpec>>,
    pub type_params: Vec<Loc<TypeParam>>,
}
impl WithLocation for FunctionDecl {}

/// A definition of a trait
#[derive(PartialEq, Debug, Clone)]
pub struct TraitDef {
    pub name: Loc<Identifier>,
    pub functions: Vec<Loc<FunctionDecl>>,
}
impl WithLocation for TraitDef {}

/// Items are things typically present at the top level of a module such as
/// entities, pipelines, submodules etc.
#[derive(PartialEq, Debug, Clone)]
pub enum Item {
    Entity(Loc<Entity>),
    Pipeline(Loc<Pipeline>),
    TraitDef(Loc<TraitDef>),
}
impl WithLocation for Item {}

#[derive(PartialEq, Debug, Clone)]
pub struct ModuleBody {
    pub members: Vec<Item>,
}
impl WithLocation for ModuleBody {}
