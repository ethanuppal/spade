use std::collections::BTreeMap;

use num::ToPrimitive;
use spade_common::location_info::Loc;
use spade_hir::Expression;
use spade_hir::{
    expression::{BinaryOperator, UnaryOperator},
    ArgumentList, Block, ExprKind, Pattern, Statement,
};
use spade_typeinference::{equation::TypeVar, fixed_types::t_int, Context, HasType, TypeState};

use crate::{error, Res};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Equation {
    Var(Var),
    Constant(Range),
    Add(Box<Equation>, Box<Equation>),
    Sub(Box<Equation>, Box<Equation>),
    Mul(Box<Equation>, Box<Equation>),
    BitManpi(Box<Equation>),
    Neg(Box<Equation>),
    BitManipMax(Box<Equation>, Box<Equation>),
    Union(Box<Equation>, Box<Equation>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    pub lo: i128,
    pub hi: i128,
}
impl Range {
    pub fn add(&self, b: &Self) -> Self {
        let a = self;
        Range {
            lo: a.lo + b.lo,
            hi: a.hi + b.hi,
        }
    }

    pub fn sub(&self, b: &Self) -> Self {
        let a = self;
        Range {
            lo: (a.lo - b.hi).min(a.lo - b.lo),
            hi: (a.hi - b.hi).max(a.hi - b.lo),
        }
    }

    pub fn neg(&self) -> Self {
        Range {
            lo: -self.hi,
            hi: -self.lo,
        }
    }

    pub fn mul(&self, b: &Self) -> Self {
        let a = self;
        Range {
            lo: (a.lo * b.hi)
                .min(a.lo * b.lo)
                .min(a.hi * b.hi)
                .min(a.hi * b.lo),
            hi: (a.lo * b.hi)
                .max(a.lo * b.lo)
                .max(a.hi * b.hi)
                .max(a.hi * b.lo),
        }
    }

    pub fn union(&self, b: &Self) -> Self {
        let a = self;
        Range {
            lo: a.lo.min(b.lo),
            hi: a.hi.max(b.hi),
        }
    }

    pub fn bit_manip(&self) -> Option<Self> {
        // This assumes positive integers
        self.to_wordlength().map(|wl| Range {
            lo: -2_i128.pow(wl),
            hi: 2_i128.pow(wl),
        })
    }

    pub fn to_wordlength(&self) -> Option<u32> {
        // NOTE: This can be considerably more fancy, taking into account the range and working
        // from there - but I'm keeping things simple for now.

        // We take the discrete logarithm here - no sneeky floats in my program!
        // Just guessed at a large number like 128...
        for i in 1..128 {
            let ii = 2_i128.pow(i - 1);
            if self.hi < ii && self.lo.abs() < ii + 1 {
                return Some(i);
            }
        }
        None
    }

    pub fn zero() -> Range {
        Range { lo: 0, hi: 0 }
    }
}

fn evaluate(out: &Var, body: &Equation, known: &BTreeMap<Var, Range>) -> Option<Range> {
    match &body {
        Equation::Var(var) => known.get(var).copied(),
        Equation::Constant(range) => Some(*range),
        Equation::Add(a, b) => match (evaluate(out, a, known), evaluate(out, b, known)) {
            (Some(a), Some(b)) => Some(a.add(&b)),
            _ => None,
        },
        Equation::Sub(a, b) => match (evaluate(out, a, known), evaluate(out, b, known)) {
            (Some(a), Some(b)) => Some(a.sub(&b)),
            _ => None,
        },
        Equation::Mul(a, b) => match (evaluate(out, a, known), evaluate(out, b, known)) {
            (Some(a), Some(b)) => Some(a.mul(&b)),
            _ => None,
        },
        Equation::BitManpi(a) => evaluate(out, a, known).and_then(|x| x.bit_manip()),
        Equation::Neg(a) => evaluate(out, a, known).map(|x| x.neg()),
        Equation::BitManipMax(a, b) => match (
            evaluate(out, a, known).and_then(|x| x.bit_manip()),
            evaluate(out, b, known).and_then(|x| x.bit_manip()),
        ) {
            (Some(a), Some(b)) => Some(a.union(&b)),
            _ => None,
        },
        Equation::Union(a, b) => match (evaluate(out, a, known), evaluate(out, b, known)) {
            (Some(a), Some(b)) => Some(a.union(&b)),
            _ => None,
        },
    }
}

pub struct Inferer<'a> {
    pub(crate) source: BTreeMap<TypeVar, Expression>,
    pub(crate) mappings: BTreeMap<TypeVar, Var>,
    // These are >= equations
    pub(crate) equations: Vec<(Var, Equation)>,
    pub(crate) var_counter: usize,
    pub(crate) context: &'a Context<'a>,
    pub(crate) type_state: &'a mut TypeState,
}
impl<'a> Inferer<'a> {
    pub fn new(type_state: &'a mut TypeState, context: &'a Context<'a>) -> Self {
        Self {
            source: BTreeMap::new(),
            mappings: BTreeMap::new(),
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
                    // TODO[et]: Inject where the variable came from so we can put it back in
                    let p = if let Some(q) = self.mappings.get(size) {
                        *q
                    } else {
                        let q = self.new_var();
                        // self.source.insert(q, );
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

    pub fn expression(&mut self, expr: &Loc<Expression>) -> Res {
        let maybe_eq = match &expr.inner.kind {
            ExprKind::Identifier(_) => self.find_or_create(&expr.inner).map(|v| Equation::Var(v)),
            ExprKind::IntLiteral(literal) => {
                let x = match literal {
                    spade_hir::expression::IntLiteral::Signed(x) => x.to_i128(),
                    spade_hir::expression::IntLiteral::Unsigned(x) => x.to_i128(),
                }
                .unwrap();
                Some(Equation::Constant(Range { lo: x, hi: x }))
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
        for stmt in block.statements.iter() {
            match &stmt.inner {
                // TODO: Is there a currectness bug here since I discard the pattern?
                Statement::Binding(_pattern, _, expr) => {
                    self.expression(&expr)?;
                }

                // Nothing to be done for these
                Statement::Register(_)
                | Statement::Declaration(_)
                | Statement::PipelineRegMarker
                | Statement::Label(_)
                | Statement::Assert(_)
                | Statement::Set { .. } => {}
            }
        }
        self.expression(&block.result)
    }

    fn match_(
        &mut self,
        _value: &Loc<Expression>,
        patterns: &[(Loc<Pattern>, Loc<Expression>)],
    ) -> Res {
        // TODO: Is there a currectness bug here since I discard the pattern?
        // NOTE: This unification works if the range contains zero - which it kinda always does
        // here, but it can cause overestimations!
        let mut eq = Equation::Constant(Range::zero());
        for (_, body) in patterns {
            if let Some(b) = self.expression(body)? {
                eq = Equation::Union(Box::new(eq), Box::new(b));
            }
        }
        Ok(Some(eq))
    }

    fn if_(
        &mut self,
        _value: &Loc<Expression>,
        true_: &Loc<Expression>,
        false_: &Loc<Expression>,
    ) -> Res {
        Ok(match (self.expression(true_)?, self.expression(false_)?) {
            (Some(true_), Some(false_)) => Some(Equation::Union(Box::new(true_), Box::new(false_))),
            _ => None,
        })
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

            (BinaryOperator::Mul, Some(lhs_t), Some(rhs_t)) => {
                Some(Equation::Mul(Box::new(lhs_t), Box::new(rhs_t)))
            }
            (BinaryOperator::Mul, _, _) => None,

            (
                BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::ArithmeticRightShift,
                Some(v),
                _,
            ) => {
                // The left value is the one being shifted, right?
                Some(Equation::BitManpi(Box::new(v)))
            }

            (
                BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::ArithmeticRightShift,
                _,
                _,
            ) => None,

            (
                BinaryOperator::BitwiseOr | BinaryOperator::BitwiseAnd | BinaryOperator::BitwiseXor,
                Some(a),
                Some(b),
            ) => Some(Equation::BitManipMax(Box::new(a), Box::new(b))),
            (
                BinaryOperator::BitwiseOr | BinaryOperator::BitwiseAnd | BinaryOperator::BitwiseXor,
                _,
                _,
            ) => None,

            (
                BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::LogicalXor
                | BinaryOperator::Eq
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
            (UnaryOperator::Sub, Some(v)) => Some(Equation::Neg(Box::new(v))),
            (UnaryOperator::Sub, _) => None,
            (UnaryOperator::BitwiseNot, Some(v)) => Some(Equation::BitManpi(Box::new(v))),
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
        _kind: &spade_hir::expression::CallKind,
        _callee: &Loc<spade_common::name::NameID>,
        _args: &Loc<ArgumentList>,
    ) -> Res {
        Ok(None)
    }

    pub fn infer(
        equations: &Vec<(Var, Equation)>,
        known: BTreeMap<Var, Range>,
    ) -> error::Result<BTreeMap<Var, Range>> {
        let mut known = known;
        // worst-case: The equations are all in reverse order and we can solve one new variable per run
        // - after that we're stuck
        // println!("{:?}", inferer.equations);
        for _ in 0..equations.len() {
            let known_at_start = known.clone();
            for (var, body) in equations.iter() {
                // TODO: How do we handle contradictions?
                if let Some(guess) = evaluate(var, body, &known) {
                    match known.entry(*var) {
                        std::collections::btree_map::Entry::Vacant(v) => {
                            v.insert(guess);
                        }
                        std::collections::btree_map::Entry::Occupied(v) => {
                            match (v.get().to_wordlength(), guess.to_wordlength()) {
                                (Some(current_wl), Some(guess_wl)) if current_wl != guess_wl => {
                                    // Wasted resources, potentially quite optimization
                                    return Err(error::Error::WordlengthMismatch(
                                        current_wl, guess_wl,
                                    ));
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }

            // Break when we got new information - I think this is a decent speedup...
            if known_at_start == known {
                break;
            }
        }
        Ok(known)
    }
}
