use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    f64::EPSILON,
};

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

// I've made the bold assumption that `x + EPSILON` is the same or equal to `^ x ^` (the larger floating point number).
// Another way of phrasing it is: `b > 0 => a + b > a` when using floating point arithmatic.
#[derive(PartialEq, Clone, Debug, PartialOrd)]
pub struct AAF(BTreeMap<AffineVar, f64>);

#[derive(PartialEq, Clone, Debug, PartialOrd)]
struct H {
    rad: f64,
    mid: f64,
}

fn range_helper(r: Range) -> H {
    let mid = (r.hi + r.lo) as f64 / 2.0;
    let rad = (mid - r.lo as f64).max(r.hi as f64 - mid);
    H { mid, rad }
}

impl AAF {
    fn from_range(counter: &mut usize, r: Range) -> AAF {
        // NOTE: Rounding errors?
        let h = range_helper(r);
        let new_var = AAF::new_var(counter);
        AAF([(AffineVar::Const, h.mid), (new_var, h.rad)]
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
        let h = range_helper(r);
        let new_var = AffineVar::Var(var);
        AAF([(AffineVar::Const, h.mid), (new_var, h.rad)]
            .into_iter()
            .collect())
    }

    fn bit_manip(&self, counter: &mut usize) -> AAF {
        let mid = self.mid();
        let rad = self.rad();
        AAF::from_range(
            counter,
            Range {
                lo: (mid - rad) as i128,
                hi: (mid + rad) as i128,
            }
            .bit_manip()
            .unwrap(),
        )
    }

    fn rad(&self) -> f64 {
        self.0
            .iter()
            .map(|(v, x)| if v == &AffineVar::Const { 0.0 } else { x.abs() })
            .sum()
    }

    fn mid(&self) -> f64 {
        self.0
            .iter()
            .find_map(|(var, value)| {
                if var == &AffineVar::Const {
                    Some(*value)
                } else {
                    None
                }
            })
            .unwrap_or(0.0)
    }

    // Computes alpha * x + beta * y + gamma (where delta is extra noise)
    fn affine(
        counter: &mut usize,
        x: &AAF,
        y: &AAF,
        alpha: f64,
        beta: f64,
        gamma: f64,
        delta: f64,
    ) -> AAF {
        let mut delta = delta;
        let mut z = BTreeMap::new();

        for i in x.vars().union(&y.vars()) {
            let xi = x.0.get(i).unwrap_or(&0.0);
            let yi = y.0.get(i).unwrap_or(&0.0);
            let zi = alpha * xi + beta * yi + if i == &AffineVar::Const { gamma } else { 0.0 };
            z.insert(*i, zi);

            // / Hope the compiler doesn't optimize this away...
            let a = zi + EPSILON;
            let b = zi - EPSILON;
            delta += (a - zi).max(zi - b);
        }
        let d = Self::new_var(counter);
        z.insert(d, delta);
        AAF(z)
    }

    fn vars(&self) -> BTreeSet<AffineVar> {
        self.0.keys().cloned().collect()
    }

    fn mul(&self, counter: &mut usize, other: &Self) -> Self {
        // This code is quite complicated and I got a myriad of bugs here. The idea is to over
        // estimate using: |(a * b)| <= |(|b| * a + |a| * b + mid(a) * mid(b) + rad(a) * rad(b))|
        // It's a pretty correct way of estimating and it works decently well.
        let x0 = self.mid();
        let y0 = other.mid();

        let p = range_helper(
            Range {
                lo: x0 as i128,
                hi: x0 as i128,
            }
            .mul(&Range {
                lo: y0 as i128,
                hi: y0 as i128,
            }),
        );
        let gamma = -p.mid;
        let delta = (self.rad() * other.rad() + EPSILON) + p.rad + EPSILON;

        Self::affine(counter, self, other, y0, x0, gamma, delta)
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
        // Union of AAF doesn't make a lot of sense, it's the biggest weakness of the form
        // since we have to either throw away information, or accumulate a lot of error.
        let mut out = self.0.clone();
        for (var, value) in other.0.iter() {
            if var == &AffineVar::Const {
                out.insert(*var, self.mid() + other.mid());
            } else {
                match out.entry(*var) {
                    Entry::Vacant(v) => {
                        v.insert(*value);
                    }
                    Entry::Occupied(mut v) => {
                        *v.get_mut() = v.get().max(*value);
                    }
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
        Equation::V(var) => known.get(&var).map(|r| AAF::from_var(*var, *r)),
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
            lo: (mid - rad).ceil() as i128,
            hi: (mid + rad).floor() as i128,
        })
    } else {
        None
    }
}
