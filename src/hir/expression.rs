use super::{Block, NameID};
use crate::location_info::{Loc, WithLocation};

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Eq,
    Gt,
    Lt,
    LeftShift,
    RightShift,
    LogicalAnd,
    LogicalOr,
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    Identifier(NameID),
    IntLiteral(u128),
    BoolLiteral(bool),
    FnCall(Loc<NameID>, Vec<Loc<Expression>>),
    BinaryOperator(Box<Loc<Expression>>, BinaryOperator, Box<Loc<Expression>>),
    Block(Box<Block>),
    If(
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
}
impl WithLocation for ExprKind {}

impl ExprKind {
    pub fn with_id(self, id: u64) -> Expression {
        Expression { kind: self, id }
    }

    #[cfg(test)]
    pub fn idless(self) -> Expression {
        Expression { kind: self, id: 0 }
    }
}

#[derive(Debug, Clone)]
pub struct Expression {
    pub kind: ExprKind,
    // This ID is used to associate types with the expression
    pub id: u64,
}
impl WithLocation for Expression {}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

// Helper constructors used in tests
#[cfg(test)]
impl Expression {
    pub fn ident(id: u64, name: &str) -> Expression {
        ExprKind::Identifier(Path::from_strs(&[name]).nowhere()).with_id(id)
    }
}
