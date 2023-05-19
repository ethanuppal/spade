use std::collections::BTreeMap;

use crate::inferer::{Equation, Var};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
            lo: -2_i128.pow(wl - 1),
            hi: 2_i128.pow(wl - 1) - 1,
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

pub fn evaluate_ia(body: &Equation, known: &BTreeMap<Var, Range>) -> Option<Range> {
    match &body {
        Equation::V(var) => known.get(var).copied(),
        Equation::Constant(range) => Some(*range),
        Equation::Add(a, b) => match (evaluate_ia(a, known), evaluate_ia(b, known)) {
            (Some(a), Some(b)) => Some(a.add(&b)),
            _ => None,
        },
        Equation::Sub(a, b) => match (evaluate_ia(a, known), evaluate_ia(b, known)) {
            (Some(a), Some(b)) => Some(a.sub(&b)),
            _ => None,
        },
        Equation::Mul(a, b) => match (evaluate_ia(a, known), evaluate_ia(b, known)) {
            (Some(a), Some(b)) => Some(a.mul(&b)),
            _ => None,
        },
        Equation::BitManpi(a) => evaluate_ia(a, known).and_then(|x| x.bit_manip()),
        Equation::Neg(a) => evaluate_ia(a, known).map(|x| x.neg()),
        Equation::BitManipMax(a, b) => match (
            evaluate_ia(a, known).and_then(|x| x.bit_manip()),
            evaluate_ia(b, known).and_then(|x| x.bit_manip()),
        ) {
            (Some(a), Some(b)) => Some(a.union(&b)),
            _ => None,
        },
        Equation::Union(a, b) => match (evaluate_ia(a, known), evaluate_ia(b, known)) {
            (Some(a), Some(b)) => Some(a.union(&b)),
            _ => None,
        },
    }
}
