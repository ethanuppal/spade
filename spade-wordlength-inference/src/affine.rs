use std::collections::{btree_map::Entry, BTreeMap};

use crate::{
    inferer::{Equation, Var},
    range::Range,
};

#[derive(Eq, PartialEq, Clone, Copy, Debug, Ord, PartialOrd)]
enum AffineVar {
    Var(Var),
    Gen(usize),
    Const,
}

pub struct AAF(BTreeMap<AffineVar, i128>);

impl AAF {
    fn from_range(counter: &mut usize, r: Range) -> AAF {
        // NOTE: Rounding errors?
        let rad = (r.hi - r.lo) / 2;
        let mid = (r.hi + r.lo) / 2;
        let new_var = AAF::new_var(counter);
        AAF([(AffineVar::Const, mid), (new_var, rad)]
            .into_iter()
            .collect())
    }

    fn new_var(counter: &mut usize) -> AffineVar {
        let x = AffineVar::Gen(*counter);
        *counter += 1;
        x
    }

    fn from_var(var: Var, r: Range) -> AAF {
        // NOTE: Rounding errors?
        let rad = (r.hi - r.lo) / 2;
        let mid = (r.hi + r.lo) / 2;
        let new_var = AffineVar::Var(var);
        AAF([(AffineVar::Const, mid), (new_var, rad)]
            .into_iter()
            .collect())
    }

    fn bit_manip(&self, counter: &mut usize) -> AAF {
        let mid = self.mid();
        let rad = self.rad();
        AAF::from_range(
            counter,
            Range {
                lo: mid - rad,
                hi: mid + rad,
            }
            .bit_manip()
            .unwrap(),
        )
    }

    fn rad(&self) -> i128 {
        self.0.values().map(|x| x.abs()).sum()
    }

    fn mid(&self) -> i128 {
        self.0
            .iter()
            .find_map(|(var, value)| {
                if var == &AffineVar::Const {
                    Some(*value)
                } else {
                    None
                }
            })
            .unwrap_or(0)
    }

    fn mul(&self, counter: &mut usize, other: &Self) -> Self {
        let s_rad = self.rad();
        let o_rad = other.rad();
        let aa_mul = AAF::from_range(
            counter,
            Range {
                lo: s_rad,
                hi: s_rad,
            }
            .mul(&Range {
                lo: o_rad,
                hi: o_rad,
            }),
        );

        self.add(other).add(&aa_mul)
    }

    fn add(&self, other: &Self) -> Self {
        let mut out = self.0.clone();
        for (var, value) in other.0.iter() {
            match out.entry(*var) {
                Entry::Vacant(v) => {
                    v.insert(*value);
                }
                Entry::Occupied(mut v) => {
                    *v.get_mut() += value;
                }
            }
        }
        AAF(out)
    }

    fn union(&self, other: &Self) -> Self {
        let mut out = self.0.clone();
        for (var, value) in other.0.iter() {
            match out.entry(*var) {
                Entry::Vacant(v) => {
                    v.insert(*value);
                }
                Entry::Occupied(mut v) => {
                    *v.get_mut() = *v.get().max(value);
                }
            }
        }
        AAF(out)
    }

    fn neg(&self) -> Self {
        AAF(self.0.clone().into_iter().map(|(v, s)| (v, -s)).collect())
    }
}

fn evaluate_aa(counter: &mut usize, body: &Equation, known: &BTreeMap<Var, Range>) -> Option<AAF> {
    match body {
        Equation::Var(var) => known.get(&var).map(|r| AAF::from_var(*var, *r)),
        Equation::Constant(r) => Some(AAF::from_range(counter, *r)),
        Equation::Add(a, b) => match (
            evaluate_aa(counter, a, known),
            evaluate_aa(counter, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.add(&b)),
            _ => None,
        },
        Equation::Sub(a, b) => match (
            evaluate_aa(counter, a, known),
            evaluate_aa(counter, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.add(&b.neg())),
            _ => None,
        },

        Equation::Mul(a, b) => match (
            evaluate_aa(counter, a, known),
            evaluate_aa(counter, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.mul(counter, &b)),
            _ => None,
        },
        Equation::Neg(a) => evaluate_aa(counter, a, known).map(|a| a.neg()),
        Equation::BitManpi(a) => evaluate_aa(counter, a, known).map(|x| x.bit_manip(counter)),
        Equation::BitManipMax(a, b) => match (
            evaluate_aa(counter, a, known),
            evaluate_aa(counter, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.bit_manip(counter).union(&b.bit_manip(counter))),
            _ => None,
        },
        Equation::Union(a, b) => match (
            evaluate_aa(counter, a, known),
            evaluate_aa(counter, b, known),
        ) {
            (Some(a), Some(b)) => Some(a.union(&b)),
            _ => None,
        },
    }
}

pub fn evaluate_aa_and_simplify_to_range(
    body: &Equation,
    known: &BTreeMap<Var, Range>,
) -> Option<Range> {
    if let Some(aa_expr) = evaluate_aa(&mut 0, body, known) {
        let mid = aa_expr.mid();
        let rad = aa_expr.rad();
        Some(Range {
            lo: rad - mid,
            hi: rad + mid,
        })
    } else {
        None
    }
}
