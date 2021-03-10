use super::{Block, NameID};
use spade_common::location_info::{Loc, WithLocation};
use spade_parser::ast::Identifier;

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
pub enum NamedArgument {
    /// Binds the arguent named LHS in the outer scope to the expression
    Full(Loc<Identifier>, Loc<Expression>),
    /// Binds a local variable to an argument with the same name
    Short(Loc<NameID>),
}
impl WithLocation for NamedArgument {}

#[derive(PartialEq, Debug, Clone)]
pub enum ArgumentList {
    Positional(Vec<Loc<Expression>>),
    Named(Vec<NamedArgument>),
}
impl WithLocation for ArgumentList {}

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
    EntityInstance(Loc<NameID>, ArgumentList),
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
    pub fn ident(expr_id: u64, name_id: u64, name: &str) -> Expression {
        ExprKind::Identifier(NameID(name_id, crate::ast::Path::from_strs(&[name]))).with_id(expr_id)
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
