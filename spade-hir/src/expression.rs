use crate::Pattern;

use super::{Block, NameID};
use local_impl::local_impl;
use serde::{Deserialize, Serialize};
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};

#[derive(Clone, Copy, PartialEq, Debug, Serialize, Deserialize)]
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
    ArithmeticRightShift,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    BitwiseOr,
    BitwiseAnd,
    BitwiseXor,
}
#[derive(Clone, Copy, PartialEq, Debug, Serialize, Deserialize)]
pub enum UnaryOperator {
    Sub,
    Not,
    BitwiseNot,
    Dereference,
    Reference,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum NamedArgument {
    /// Binds the arguent named LHS in the outer scope to the expression
    Full(Loc<Identifier>, Loc<Expression>),
    /// Binds a local variable to an argument with the same name
    Short(Loc<Identifier>, Loc<Expression>),
}
impl WithLocation for NamedArgument {}

/// Specifies how an argument is bound. Mainly used for error reporting without
/// code duplication
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum ArgumentKind {
    Positional,
    Named,
    ShortNamed,
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum ArgumentList {
    Named(Vec<NamedArgument>),
    Positional(Vec<Loc<Expression>>),
}

impl ArgumentList {
    pub fn expressions(&self) -> Vec<&Loc<Expression>> {
        match self {
            ArgumentList::Named(n) => n
                .iter()
                .map(|arg| match arg {
                    NamedArgument::Full(_, expr) => expr,
                    NamedArgument::Short(_, expr) => expr,
                })
                .collect(),
            ArgumentList::Positional(arg) => arg.iter().collect(),
        }
    }
    pub fn expressions_mut(&mut self) -> Vec<&mut Loc<Expression>> {
        match self {
            ArgumentList::Named(n) => n
                .iter_mut()
                .map(|arg| match arg {
                    NamedArgument::Full(_, expr) => expr,
                    NamedArgument::Short(_, expr) => expr,
                })
                .collect(),
            ArgumentList::Positional(arg) => arg.iter_mut().collect(),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct Argument {
    pub target: Loc<Identifier>,
    pub value: Loc<Expression>,
    pub kind: ArgumentKind,
}
impl WithLocation for ArgumentList {}

// FIXME: Migrate entity, pipeline and fn instantiation to this
#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum CallKind {
    Function,
    Entity(Loc<()>),
    Pipeline(Loc<()>, Loc<u128>),
}
impl WithLocation for CallKind {}

#[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
pub enum ExprKind {
    Identifier(NameID),
    IntLiteral(u128),
    BoolLiteral(bool),
    TupleLiteral(Vec<Loc<Expression>>),
    ArrayLiteral(Vec<Loc<Expression>>),
    Index(Box<Loc<Expression>>, Box<Loc<Expression>>),
    TupleIndex(Box<Loc<Expression>>, Loc<u128>),
    FieldAccess(Box<Loc<Expression>>, Loc<Identifier>),
    MethodCall {
        target: Box<Loc<Expression>>,
        name: Loc<Identifier>,
        args: Loc<ArgumentList>,
        call_kind: CallKind,
    },
    Call {
        kind: CallKind,
        callee: Loc<NameID>,
        args: Loc<ArgumentList>,
    },
    BinaryOperator(Box<Loc<Expression>>, BinaryOperator, Box<Loc<Expression>>),
    UnaryOperator(UnaryOperator, Box<Loc<Expression>>),
    Match(Box<Loc<Expression>>, Vec<(Loc<Pattern>, Loc<Expression>)>),
    Block(Box<Block>),
    If(
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
        Box<Loc<Expression>>,
    ),
    PipelineRef {
        stage: Loc<usize>,
        name: Loc<NameID>,
        declares_name: bool,
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

#[derive(Debug, Clone, Serialize, Deserialize)]
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

#[local_impl]
impl LocExprExt for Loc<Expression> {
    /// Checks if the expression is evaluatable at compile time, returning a Loc of
    /// a (sub)-expression which requires runtime, and None if it is comptime valuatable.
    ///
    /// If this method returns None, `.eval()` on the resulting list of mir statements is
    /// guaranteed to work
    fn runtime_requirement_witness(&self) -> Option<Loc<Expression>> {
        match &self.kind {
            ExprKind::Identifier(_) => Some(self.clone()),
            ExprKind::IntLiteral(_) => None,
            ExprKind::BoolLiteral(_) => None,
            ExprKind::TupleLiteral(inner) => inner
                .iter()
                .filter_map(Self::runtime_requirement_witness)
                .next(),
            ExprKind::ArrayLiteral(inner) => inner
                .iter()
                .filter_map(Self::runtime_requirement_witness)
                .next(),
            ExprKind::Index(l, r) => l
                .runtime_requirement_witness()
                .or_else(|| r.runtime_requirement_witness()),
            ExprKind::TupleIndex(l, _) => l.runtime_requirement_witness(),
            ExprKind::FieldAccess(l, _) => l.runtime_requirement_witness(),
            // NOTE: We probably shouldn't see this here since we'll have lowered
            // methods at this point, but this function doesn't throw
            ExprKind::MethodCall(_, _, _)
            | ExprKind::PipelineInstance { .. }
            | ExprKind::EntityInstance(_, _)
            | ExprKind::FnCall(_, _) => Some(self.clone()),
            ExprKind::BinaryOperator(l, operator, r) => {
                if let Some(witness) = l
                    .runtime_requirement_witness()
                    .or_else(|| r.runtime_requirement_witness())
                {
                    Some(witness)
                } else {
                    match &operator {
                        BinaryOperator::Add => None,
                        BinaryOperator::Sub => None,
                        BinaryOperator::Mul
                        | BinaryOperator::Eq
                        | BinaryOperator::Gt
                        | BinaryOperator::Lt
                        | BinaryOperator::Ge
                        | BinaryOperator::Le
                        | BinaryOperator::LeftShift
                        | BinaryOperator::RightShift
                        | BinaryOperator::ArithmeticRightShift
                        | BinaryOperator::LogicalAnd
                        | BinaryOperator::LogicalOr
                        | BinaryOperator::LogicalXor
                        | BinaryOperator::BitwiseOr
                        | BinaryOperator::BitwiseAnd
                        | BinaryOperator::BitwiseXor => Some(self.clone()),
                    }
                }
            }
            ExprKind::UnaryOperator(op, operand) => {
                if let Some(witness) = operand.runtime_requirement_witness() {
                    Some(witness)
                } else {
                    match op {
                        UnaryOperator::Sub => None,
                        UnaryOperator::Not
                        | UnaryOperator::BitwiseNot
                        | UnaryOperator::Dereference
                        | UnaryOperator::Reference => Some(self.clone()),
                    }
                }
            }
            ExprKind::Match(_, _) => Some(self.clone()),
            ExprKind::Block(_) => Some(self.clone()),
            ExprKind::If(_, _, _) => Some(self.clone()),
            ExprKind::PipelineRef { .. } => Some(self.clone()),
        }
    }
}
