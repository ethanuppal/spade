use crate::lexer::TokenKind;
use crate::location_info::Loc;
use codespan::Span;

pub trait WithLocation {
    fn at(self, span: Span) -> Loc<Self>
    where
        Self: Sized,
    {
        Loc::new(self, span)
    }

    fn nowhere(self) -> Loc<Self>
    where
        Self: Sized,
    {
        self.at(Span::new(0, 0))
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Identifier(pub String);

impl WithLocation for Identifier {}

#[derive(PartialEq, Debug, Clone)]
pub enum Type {
    Named(Loc<Identifier>),
    WithSize(Box<Loc<Type>>, Loc<Expression>),
    UnitType,
}
impl WithLocation for Type {}

#[derive(PartialEq, Debug, Clone)]
pub enum Expression {
    Identifier(Loc<Identifier>),
    IntLiteral(u128),
    BinaryOperator(Box<Loc<Expression>>, TokenKind, Box<Loc<Expression>>),
    Parenthisised(Box<Loc<Expression>>),
}
impl WithLocation for Expression {}

#[derive(PartialEq, Debug, Clone)]
pub enum Statement {
    Binding(Loc<Identifier>, Option<Loc<Type>>, Loc<Expression>),
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
impl WithLocation for Register {}
