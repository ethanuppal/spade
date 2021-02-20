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
    TupleLiteral(Vec<Loc<Expression>>),
    TupleIndex(Box<Loc<Expression>>, Loc<u128>),
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

impl Expression {
    /// Create a new expression referencing an identifier with the specified
    /// id and name
    #[cfg(test)]
    pub fn ident(expr_id: u64, name_id: u64, name: &str) -> Expression {
        ExprKind::Identifier(NameID(name_id, crate::ast::Path::from_strs(&[name]))).with_id(expr_id)
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
