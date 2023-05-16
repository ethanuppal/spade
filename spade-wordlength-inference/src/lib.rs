use std::collections::HashMap;

use num::ToPrimitive;
use spade_common::location_info::Loc;
use spade_hir::{
    expression::{BinaryOperator, UnaryOperator},
    ArgumentList, Block, ExprKind, Expression, ItemList, Pattern, PatternArgument, Register,
    Statement, TypeParam, Unit,
};
use spade_typeinference::{equation::TypeVar, Context, TypeState};

mod error;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Var(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
enum Equation {
    Var(Var),
    Constant { lo: i128, hi: i128 }, // Change this to IA and then to AA
    Add(Box<Equation>, Box<Equation>),
}

type Res = error::Result<Option<Equation>>;

struct Inferer<'a> {
    mappings: HashMap<TypeVar, Var>,
    // These are <= equations
    equations: Vec<(Var, Equation)>,
    var_counter: usize,
    symtab: &'a Context<'a>,
}
impl<'a> Inferer<'a> {
    fn new(symtab: &'a Context<'a>) -> Self {
        Self {
            mappings: HashMap::new(),
            equations: Vec::new(),
            var_counter: 0,
            symtab,
        }
    }

    fn new_var(&mut self) -> Var {
        let v = self.var_counter;
        self.var_counter += 1;
        Var(v)
    }

    fn expression(&mut self, type_state: &mut TypeState, expr: &Loc<Expression>) -> Res {
        Ok(match &expr.inner.kind {
            ExprKind::Identifier(var) => {
                panic!()
            }
            ExprKind::IntLiteral(literal) => {
                let x = match literal {
                    spade_hir::expression::IntLiteral::Signed(x) => x.to_i128(),
                    spade_hir::expression::IntLiteral::Unsigned(x) => x.to_i128(),
                }
                .unwrap();
                Some(Equation::Constant { lo: x, hi: x })
            }

            ExprKind::Call { kind, callee, args } => todo!(),
            ExprKind::BinaryOperator(lhs, op, rhs) => {
                self.binary_operator(type_state, lhs, *op, rhs)?
            }
            ExprKind::UnaryOperator(op, v) => self.unary_operator(type_state, *op, v)?,
            ExprKind::Match(value, patterns) => self.match_(type_state, value, patterns)?,
            ExprKind::Block(block) => self.block(type_state, block)?,
            ExprKind::If(value, true_, false_) => self.if_(type_state, value, true_, false_)?,

            // There's a case to be made for these being valuable to implement, but I'm not gonna
            // do that right now since I can test this without implementing these
            ExprKind::BoolLiteral(_)
            | ExprKind::PipelineRef { .. }
            | ExprKind::CreatePorts
            | ExprKind::TupleLiteral(_)
            | ExprKind::ArrayLiteral(_)
            | ExprKind::Index(_, _)
            | ExprKind::TupleIndex(_, _)
            | ExprKind::FieldAccess(_, _)
            | ExprKind::MethodCall { .. } => todo!(),
        })
    }

    fn block(&self, type_state: &mut TypeState, block: &Block) -> Res {
        todo!()
    }

    fn match_(
        &self,
        type_state: &mut TypeState,
        value: &Loc<Expression>,
        patterns: &[(Loc<Pattern>, Loc<Expression>)],
    ) -> Res {
        todo!()
    }

    fn if_(
        &self,
        type_state: &mut TypeState,
        value: &Loc<Expression>,
        r#true: &Loc<Expression>,
        r#false: &Loc<Expression>,
    ) -> Res {
        todo!()
    }

    fn binary_operator(
        &self,
        type_state: &mut TypeState,
        lhs: &Loc<Expression>,
        op: BinaryOperator,
        rhs: &Loc<Expression>,
    ) -> Res {
        todo!()
    }

    fn unary_operator(
        &self,
        type_state: &mut TypeState,
        op: UnaryOperator,
        v: &Loc<Expression>,
    ) -> Res {
        todo!()
    }
}

pub fn infer_and_check(
    type_state: &mut TypeState,
    context: &Context,
    unit: &Unit,
) -> error::Result<()> {
    let mut inferer = Inferer::new(context);
    inferer.expression(type_state, &unit.body)?;

    panic!()
}
