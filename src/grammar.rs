use crate::identifier::Identifier;
use crate::lexer::TokenKind;

#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Named(Identifier),
    UnitType,
}

#[derive(PartialEq, Debug, Clone)]
pub enum Expression {
    Identifier(Identifier),
    IntLiteral(u128),
    BinaryOperator(Box<Expression>, TokenKind, Box<Expression>),
    Parenthisised(Box<Expression>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Binding(Identifier, Option<Type>, Expression),
    Register(Register),
}

#[derive(PartialEq, Debug, Clone)]
pub struct Entity {
    pub name: String,
    pub inputs: Vec<(Identifier, Type)>,
    pub statements: Vec<Statement>,
    pub output_type: Type,
    pub output_value: Expression,
}

#[derive(PartialEq, Debug, Clone)]
pub struct Register {
    pub name: Identifier,
    pub clock: Identifier,
    pub reset: Option<(Expression, Expression)>,
    pub value: Expression,
}
