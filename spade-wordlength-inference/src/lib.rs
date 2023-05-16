use std::collections::HashMap;

use num::ToPrimitive;
use spade_common::location_info::Loc;
use spade_hir::{
    expression::{BinaryOperator, UnaryOperator},
    ArgumentList, Block, ExprKind, Expression, ItemList, Pattern, PatternArgument, Register,
    Statement, TypeParam, Unit,
};
use spade_typeinference::{equation::TypeVar, fixed_types::t_int, Context, HasType, TypeState};
use spade_types::KnownType;

mod error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Var(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
enum Equation {
    Var(Var),
    Constant { lo: i128, hi: i128 }, // Change this to IA and then to AA
    Add(Box<Equation>, Box<Equation>),
    Sub(Box<Equation>, Box<Equation>),
}

type Res = error::Result<Option<Equation>>;

struct Inferer<'a> {
    mappings: HashMap<TypeVar, Var>,
    // These are >= equations
    equations: Vec<(Var, Equation)>,
    var_counter: usize,
    context: &'a Context<'a>,
    type_state: &'a mut TypeState,
}
impl<'a> Inferer<'a> {
    fn new(type_state: &'a mut TypeState, context: &'a Context<'a>) -> Self {
        Self {
            mappings: HashMap::new(),
            equations: Vec::new(),
            var_counter: 0,
            context,
            type_state,
        }
    }

    fn new_var(&mut self) -> Var {
        let v = self.var_counter;
        self.var_counter += 1;
        Var(v)
    }

    fn find_or_create(&mut self, thing: &dyn HasType) -> Option<Var> {
        if let Ok(TypeVar::Known(t, v)) = thing.get_type(self.type_state) {
            match v.as_slice() {
                [size] if t == t_int(self.context.symtab) => {
                    let p = if let Some(q) = self.mappings.get(size) {
                        *q
                    } else {
                        let q = self.new_var();
                        self.mappings.insert(size.clone(), q);
                        q
                    };
                    Some(p)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    fn maybe_add_equation(&mut self, thing: &dyn HasType, maybe_eq: Option<Equation>) {
        match (self.find_or_create(thing), maybe_eq) {
            (Some(var), Some(eq)) => self.equations.push((var, eq)),
            _ => {}
        }
    }

    fn expression(&mut self, expr: &Loc<Expression>) -> Res {
        let maybe_eq = match &expr.inner.kind {
            ExprKind::Identifier(_) => self.find_or_create(&expr.inner).map(|v| Equation::Var(v)),
            ExprKind::IntLiteral(literal) => {
                let x = match literal {
                    spade_hir::expression::IntLiteral::Signed(x) => x.to_i128(),
                    spade_hir::expression::IntLiteral::Unsigned(x) => x.to_i128(),
                }
                .unwrap();
                Some(Equation::Constant { lo: x, hi: x })
            }

            ExprKind::Call { kind, callee, args } => self.call(kind, callee, args)?,
            ExprKind::BinaryOperator(lhs, op, rhs) => self.binary_operator(lhs, *op, rhs)?,
            ExprKind::UnaryOperator(op, v) => self.unary_operator(*op, v)?,
            ExprKind::Match(value, patterns) => self.match_(value, patterns)?,
            ExprKind::Block(block) => self.block(block)?,
            ExprKind::If(value, true_, false_) => self.if_(value, true_, false_)?,

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
            | ExprKind::MethodCall { .. } => None,
        };

        self.maybe_add_equation(&expr.inner, maybe_eq.clone());
        Ok(maybe_eq)
    }

    fn block(&mut self, block: &Block) -> Res {
        // TODO: Check the statements as well!
        self.expression(&block.result)
    }

    fn match_(&self, value: &Loc<Expression>, patterns: &[(Loc<Pattern>, Loc<Expression>)]) -> Res {
        todo!()
    }

    fn if_(
        &self,
        value: &Loc<Expression>,
        r#true: &Loc<Expression>,
        r#false: &Loc<Expression>,
    ) -> Res {
        Ok(None)
    }

    fn binary_operator(
        &mut self,
        lhs: &Loc<Expression>,
        op: BinaryOperator,
        rhs: &Loc<Expression>,
    ) -> Res {
        // These unwraps are safe, right?
        let lhs_t = self.expression(lhs)?;
        let rhs_t = self.expression(rhs)?;
        Ok(match (op, lhs_t, rhs_t) {
            (BinaryOperator::Add, Some(lhs_t), Some(rhs_t)) => {
                Some(Equation::Add(Box::new(lhs_t), Box::new(rhs_t)))
            }
            (BinaryOperator::Add, _, _) => None,
            (BinaryOperator::Sub, Some(lhs_t), Some(rhs_t)) => {
                Some(Equation::Sub(Box::new(lhs_t), Box::new(rhs_t)))
            }
            (BinaryOperator::Sub, _, _) => None,

            (BinaryOperator::Mul, _, _) => todo!(),
            (BinaryOperator::LeftShift, _, _) => todo!(),
            (BinaryOperator::RightShift, _, _) => todo!(),
            (BinaryOperator::ArithmeticRightShift, _, _) => todo!(),
            (BinaryOperator::LogicalAnd, _, _) => todo!(),
            (BinaryOperator::LogicalOr, _, _) => todo!(),
            (BinaryOperator::LogicalXor, _, _) => todo!(),
            (BinaryOperator::BitwiseOr, _, _) => todo!(),
            (BinaryOperator::BitwiseAnd, _, _) => todo!(),
            (BinaryOperator::BitwiseXor, _, _) => todo!(),

            (
                BinaryOperator::Eq
                | BinaryOperator::NotEq
                | BinaryOperator::Gt
                | BinaryOperator::Lt
                | BinaryOperator::Ge
                | BinaryOperator::Le,
                _,
                _,
            ) => None,
        })
    }

    fn unary_operator(&mut self, op: UnaryOperator, v: &Loc<Expression>) -> Res {
        let v_t = self.expression(v)?;
        Ok(match (op, v_t) {
            (UnaryOperator::Sub, Some(_)) => todo!(),
            (UnaryOperator::Sub, _) => None,
            (UnaryOperator::BitwiseNot, Some(_)) => todo!(),
            (UnaryOperator::BitwiseNot, _) => None,

            (
                UnaryOperator::Not
                | UnaryOperator::Dereference
                | UnaryOperator::Reference
                | UnaryOperator::FlipPort,
                _,
            ) => None,
        })
    }

    fn call(
        &self,
        kind: &spade_hir::expression::CallKind,
        callee: &Loc<spade_common::name::NameID>,
        args: &Loc<ArgumentList>,
    ) -> Res {
        todo!()
    }
}

pub fn infer_and_check(
    type_state: &mut TypeState,
    context: &Context,
    unit: &Unit,
) -> error::Result<()> {
    let mut inferer = Inferer::new(type_state, context);
    inferer.expression(&unit.body)?;
    println!("Infered: {:?}", inferer.equations);

    panic!()
}
