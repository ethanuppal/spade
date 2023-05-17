use std::collections::BTreeMap;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Var(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
enum Equation {
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
struct Range {
    lo: i128,
    hi: i128,
}
impl Range {
    fn add(&self, b: &Self) -> Self {
        let a = self;
        Range {
            lo: a.lo + b.lo,
            hi: a.hi + b.hi,
        }
    }

    fn sub(&self, b: &Self) -> Self {
        let a = self;
        Range {
            lo: (a.lo - b.hi).min(a.lo - b.lo),
            hi: (a.hi - b.hi).max(a.hi - b.lo),
        }
    }

    fn neg(&self) -> Self {
        Range {
            lo: -self.hi,
            hi: -self.lo,
        }
    }

    fn mul(&self, b: &Self) -> Self {
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

    fn union(&self, b: &Self) -> Self {
        let a = self;
        Range {
            lo: a.lo.min(b.lo),
            hi: a.hi.max(b.hi),
        }
    }

    fn bit_manip(&self) -> Option<Self> {
        // This assumes positive integers
        self.to_wordlength().map(|wl| Range {
            lo: -2_i128.pow(wl),
            hi: 2_i128.pow(wl),
        })
    }

    fn to_wordlength(&self) -> Option<u32> {
        // NOTE: This can be considerably more fancy
        // We take the discrete logarithm here - no sneeky floats in my program!
        // Just guessed at a large number like 128...
        for i in 1..128 {
            let ii = 2_i128.pow(i);
            if self.hi < ii && self.lo.abs() < ii {
                return Some(i);
            }
        }
        None
    }

    fn zero() -> Range {
        Range { lo: 0, hi: 0 }
    }
}

type Res = error::Result<Option<Equation>>;

struct Inferer<'a> {
    source: BTreeMap<TypeVar, Expression>,
    mappings: BTreeMap<TypeVar, Var>,
    // These are >= equations
    equations: Vec<(Var, Equation)>,
    var_counter: usize,
    context: &'a Context<'a>,
    type_state: &'a mut TypeState,
}
impl<'a> Inferer<'a> {
    fn new(type_state: &'a mut TypeState, context: &'a Context<'a>) -> Self {
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

    fn expression(&mut self, expr: &Loc<Expression>) -> Res {
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
        // TODO: Check the statements as well!
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
        kind: &spade_hir::expression::CallKind,
        callee: &Loc<spade_common::name::NameID>,
        args: &Loc<ArgumentList>,
    ) -> Res {
        Ok(None)
    }
}

pub fn infer_and_check(
    type_state: &mut TypeState,
    context: &Context,
    unit: &Unit,
) -> error::Result<()> {
    let mut inferer = Inferer::new(type_state, context);
    inferer.expression(&unit.body)?;

    let mut known = BTreeMap::new();
    // Aren't these strict requirements? These can't change can they? Hmmm... This is where the
    // contradictions come from!
    for (ty, var) in inferer.mappings.iter() {
        match &ty {
            TypeVar::Known(KnownType::Integer(size), _) => {
                let x = size.to_u32().unwrap(); // This is assumed to be small
                known.insert(
                    var,
                    Range {
                        lo: 0,
                        hi: 2_i128.pow(x) - 1,
                    },
                );
            }
            TypeVar::Known(KnownType::Type(n), _) => panic!("How do I handle a type? {:?}", n),
            TypeVar::Unknown(_) => {
                // known.insert(var, Range { lo: 0, hi: 0 });
            }

            TypeVar::Tuple(_)
            | TypeVar::Array { .. }
            | TypeVar::Backward(_)
            | TypeVar::Wire(_)
            | TypeVar::Inverted(_) => panic!("Wat? {:?} {:?}", ty, var),
        }
    }

    // worst-case: The equations are all in reverse order and we can solve one new variable per run
    // - after that we're stuck
    // println!("{:?}", inferer.equations);
    for _ in 0..inferer.equations.len() {
        let known_at_start = known.clone();
        for (var, body) in inferer.equations.iter() {
            // TODO: How do we handle contradictions?
            if let Some(guess) = evaluate(var, body, &known) {
                match known.entry(var) {
                    std::collections::btree_map::Entry::Vacant(v) => {
                        v.insert(guess);
                    }
                    std::collections::btree_map::Entry::Occupied(v) => {
                        match (v.get().to_wordlength(), guess.to_wordlength()) {
                            (Some(current_wl), Some(guess_wl)) if current_wl != guess_wl => {
                                // Wasted resources, potentially quite optimization
                                return Err(error::Error::WordlengthMismatch(current_wl, guess_wl));
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

    // TODO: Location information isn't really a thing... Maybe it can be solved some other way?
    for (ty, var) in inferer.mappings.iter() {
        // println!("{:?} = {:?}", var, known.get(&var));
        // None errors are checked when mir-lowering, this isn't necessarily an error
        if let Some(infered_wl) = known.get(&var).and_then(|guess| guess.to_wordlength()) {
            match &ty {
                TypeVar::Known(KnownType::Integer(size), _) => {
                    let typechecker_wl = size.to_u32().unwrap();
                    if typechecker_wl != infered_wl {
                        return Err(error::Error::WordlengthMismatch(typechecker_wl, infered_wl));
                    }
                }
                _ => {}
            }
            to_wordlength_error(inferer.type_state.unify(
                ty,
                &TypeVar::Known(KnownType::Integer(infered_wl.into()), Vec::new()),
                inferer.context.symtab,
            ))?;
        }
    }

    Ok(())
}

fn to_wordlength_error<A>(
    ty_err: Result<A, spade_typeinference::error::UnificationError>,
) -> error::Result<A> {
    match ty_err {
        Ok(v) => Ok(v),
        Err(e) => Err(error::Error::TypeError(e)),
    }
}

fn evaluate(out: &Var, body: &Equation, known: &BTreeMap<&Var, Range>) -> Option<Range> {
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