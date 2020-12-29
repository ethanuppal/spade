use super::{Block, Path};
use crate::location_info::{Loc, WithLocation};

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    Identifier(Loc<Path>),
    IntLiteral(u128),
    FnCall(Loc<Path>, Vec<Loc<Expression>>),
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
