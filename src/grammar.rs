use crate::identifier::Identifier;
use crate::lexer::TokenKind;

#[derive(PartialEq, Debug, Clone)]
pub enum Expression {
    Identifier(Identifier),
    IntLiteral(u128),
    BinaryOperator(Box<Expression>, TokenKind, Box<Expression>),
    Parenthisised(Box<Expression>),
}
