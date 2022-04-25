use crate::Pattern;

use super::{Block, NameID};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Eq,
    Gt,
    Lt,
    Ge,
    Le,
    LeftShift,
    RightShift,
    LogicalAnd,
    LogicalOr,
    BitwiseOr,
    BitwiseAnd,
    Xor,
}
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum UnaryOperator {
    Sub,
    Not,
    BitwiseNot,
}

#[derive(PartialEq, Debug, Clone)]
pub enum NamedArgument {
    /// Binds the arguent named LHS in the outer scope to the expression
    Full(Loc<Identifier>, Loc<Expression>),
    /// Binds a local variable to an argument with the same name
    Short(Loc<Identifier>, Expression),
}
impl WithLocation for NamedArgument {}

/// Specifies how an argument is bound. Mainly used for error reporting without
/// code duplication
#[derive(PartialEq, Debug, Clone)]
pub enum ArgumentKind {
    Positional,
    Named,
    ShortNamed,
}

#[derive(PartialEq, Debug, Clone)]
pub struct Argument {
    pub target: Loc<Identifier>,
    pub value: Loc<Expression>,
    pub kind: ArgumentKind,
}
impl WithLocation for Argument {}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    Identifier(NameID),
    IntLiteral(u128),
    BoolLiteral(bool),
    TupleLiteral(Vec<Loc<Expression>>),
    ArrayLiteral(Vec<Loc<Expression>>),
    Index(Box<Loc<Expression>>, Box<Loc<Expression>>),
    TupleIndex(Box<Loc<Expression>>, Loc<u128>),
    FieldAccess(Box<Loc<Expression>>, Loc<Identifier>),
    FnCall(Loc<NameID>, Vec<Argument>),
    BinaryOperator(Box<Loc<Expression>>, BinaryOperator, Box<Loc<Expression>>),
    UnaryOperator(UnaryOperator, Box<Loc<Expression>>),
    Match(Box<Loc<Expression>>, Vec<(Loc<Pattern>, Loc<Expression>)>),
    Block(Box<Block>),
    /// Instantiation of an entity. While the argument contains information about
    /// argument names, for codegen purposes, the arguments must be ordered in
    /// the target order. I.e. they should all act as positioanl arguments
    EntityInstance(Loc<NameID>, Vec<Argument>),
    PipelineInstance {
        depth: Loc<u128>,
        name: Loc<NameID>,
        args: Vec<Argument>,
    },
    If(
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
    PipelineRef {
        stage: Loc<usize>,
        name: Loc<NameID>,
    },
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
        ExprKind::Identifier(NameID(name_id, Path::from_strs(&[name]))).with_id(expr_id)
    }

    /// Returns the block that is this expression. Panics if the expression is not a block
    pub fn assume_block(&self) -> &Block {
        if let ExprKind::Block(ref block) = self.kind {
            block
        } else {
            panic!("Expression is not a block")
        }
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
