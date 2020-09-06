use crate::identifier::Identifier;
use crate::lexer::TokenKind;

#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Named(Identifier),
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
}
