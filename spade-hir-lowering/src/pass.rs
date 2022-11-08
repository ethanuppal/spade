use spade_common::location_info::Loc;
use spade_hir::{Entity, ExprKind, Expression, Pipeline, Register, Statement};

use crate::Result;

pub trait Pass {
    fn visit_expression(&mut self, expression: &mut Loc<Expression>) -> Result<()>;

    fn visit_statement(&mut self, statement: &mut Loc<Statement>) -> Result<()>;
}

pub trait Passable {
    /// Applies the pass to this HIR node. Children are visited before
    /// parents. Statements are visited in the order that they are defined
    fn apply(&mut self, pass: &mut impl Pass) -> Result<()>;
}

impl Passable for Loc<Expression> {
    fn apply(&mut self, pass: &mut impl Pass) -> Result<()> {
        macro_rules! subnodes {
            ($($node:expr),*) => {
                {$($node.apply(pass)?;)*}
            };
        }
        match &mut self.inner.kind {
            ExprKind::Identifier(_) => {}
            ExprKind::IntLiteral(_) => {}
            ExprKind::BoolLiteral(_) => {}
            ExprKind::TupleLiteral(_) => {}
            ExprKind::ArrayLiteral(_) => {}
            ExprKind::Index(lhs, rhs) => {
                subnodes!(lhs, rhs)
            }
            ExprKind::TupleIndex(lhs, _) => subnodes!(lhs),
            ExprKind::FieldAccess(lhs, _) => subnodes!(lhs),
            ExprKind::MethodCall(self_, _, args) => {
                subnodes!(self_);
                for arg in args.expressions_mut() {
                    arg.apply(pass)?;
                }
            }
            ExprKind::FnCall(_, args)
            | ExprKind::EntityInstance(_, args)
            | ExprKind::PipelineInstance {
                depth: _,
                name: _,
                args,
            } => {
                for arg in args.expressions_mut() {
                    arg.apply(pass)?;
                }
            }
            ExprKind::BinaryOperator(lhs, _, rhs) => subnodes!(lhs, rhs),
            ExprKind::UnaryOperator(_, operand) => subnodes!(operand),
            ExprKind::Match(cond, branches) => {
                cond.apply(pass)?;
                for (_, branch) in branches {
                    branch.apply(pass)?;
                }
            }
            ExprKind::Block(block) => {
                for statement in &mut block.statements {
                    match &mut statement.inner {
                        Statement::Binding(_, _, expr) => expr.apply(pass)?,
                        Statement::Register(reg) => {
                            let Register {
                                pattern: _,
                                clock,
                                reset,
                                value,
                                value_type: _,
                            } = &mut reg.inner;

                            match reset {
                                Some((trig, val)) => subnodes!(trig, val),
                                None => {}
                            }

                            subnodes!(clock, value);
                        }
                        Statement::Declaration(_) => {}
                        Statement::PipelineRegMarker => {}
                        Statement::Label(_) => {}
                        Statement::Assert(expr) => expr.apply(pass)?,
                        Statement::Set { target, value } => subnodes!(target, value),
                    }

                    pass.visit_statement(statement)?;
                }

                block.result.apply(pass)?;
            }
            ExprKind::If(cond, on_true, on_false) => subnodes!(cond, on_true, on_false),
            ExprKind::PipelineRef {
                stage: _,
                name: _,
                declares_name: _,
            } => {}
        }

        pass.visit_expression(self)
    }
}

impl Passable for Entity {
    fn apply(&mut self, pass: &mut impl Pass) -> Result<()> {
        self.body.apply(pass)
    }
}

impl Passable for Pipeline {
    fn apply(&mut self, pass: &mut impl Pass) -> Result<()> {
        self.body.apply(pass)
    }
}
