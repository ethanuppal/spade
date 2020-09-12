/**
  Representation of the language with most language constructs still present, with
  more correctness guaranatees than the AST, such as types actually existing.
*/
use crate::location_info::{Loc, WithLocation};
use crate::types::Type;

#[derive(PartialEq, Debug, Clone)]
pub enum Identifier {
    Named(String),
    Anonymous(u64),
}

impl WithLocation for Identifier {}

#[derive(PartialEq, Debug, Clone)]
pub enum Expression {
    Identifier(Loc<Identifier>),
    IntLiteral(u128),
    Add(Box<Loc<Expression>>, Box<Loc<Expression>>),
    Sub(Box<Loc<Expression>>, Box<Loc<Expression>>),
    Mul(Box<Loc<Expression>>, Box<Loc<Expression>>),
    Div(Box<Loc<Expression>>, Box<Loc<Expression>>),
    Parenthisised(Box<Loc<Expression>>),
}
impl WithLocation for Expression {}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Binding(Loc<Identifier>, Loc<Type>, Loc<Expression>),
    Register(Loc<Register>),
}
impl WithLocation for Statement {}

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub name: Loc<Identifier>,
    pub inputs: Vec<(Loc<Identifier>, Loc<Type>)>,
    pub statements: Vec<Loc<Statement>>,
    pub output_type: Loc<Type>,
    pub output_value: Loc<Expression>,
}
impl WithLocation for Entity {}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub name: Loc<Identifier>,
    pub clock: Loc<Identifier>,
    pub reset: Option<(Loc<Expression>, Loc<Expression>)>,
    pub value: Loc<Expression>,
    pub value_type: Option<Loc<Type>>,
}
