use std::collections::HashMap;

use spade_common::location_info::{Loc, WithLocation};

use crate::equation::InnerTypeVar;

#[derive(Clone)]
pub enum ConstraintExpr<I> {
    Integer(i128),
    Var(I),
    Sum(Box<ConstraintExpr<I>>, Box<ConstraintExpr<I>>),
    Sub(Box<ConstraintExpr<I>>),
}

impl<I> WithLocation for ConstraintExpr<I> {}

impl ConstraintExpr<InnerTypeVar> {
    /// Evaluates the ConstraintExpr returning a new simplified form
    fn evaluate(&self) -> ConstraintExpr<InnerTypeVar> {
        match self {
            ConstraintExpr::Integer(_) => self.clone(),
            ConstraintExpr::Var(_) => self.clone(),
            ConstraintExpr::Sum(lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                (ConstraintExpr::Integer(l), ConstraintExpr::Integer(r)) => {
                    ConstraintExpr::Integer(l + r)
                }
                _ => self.clone(),
            },
            ConstraintExpr::Sub(inner) => match **inner {
                ConstraintExpr::Integer(val) => ConstraintExpr::Integer(-val),
                _ => self.clone(),
            },
        }
    }
}

impl<I> std::fmt::Display for ConstraintExpr<I>
where
    I: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintExpr::Integer(val) => write!(f, "{val}"),
            ConstraintExpr::Var(var) => write!(f, "{var}"),
            ConstraintExpr::Sum(rhs, lhs) => write!(f, "({rhs} + {lhs})"),
            ConstraintExpr::Sub(val) => write!(f, "(-{val})"),
        }
    }
}

pub struct TypeConstraints {
    pub inner: HashMap<InnerTypeVar, Vec<Loc<ConstraintExpr<InnerTypeVar>>>>,
}

impl TypeConstraints {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn add_constraint(&mut self, lhs: InnerTypeVar, rhs: Loc<ConstraintExpr<InnerTypeVar>>) {
        self.inner.entry(lhs).or_insert(vec![]).push(rhs)
    }

    /// Calls `evaluate` on all constraints. If any constraints are now `T = Integer(val)`,
    /// those updated values are returned. Such constraints are then removed
    pub fn update_constraints(&mut self) -> Vec<Loc<(InnerTypeVar, i128)>> {
        let mut new_known = vec![];
        for (expr, constraints) in &mut self.inner {
            *constraints = constraints
                .into_iter()
                .filter_map(|constraint| {
                    let result = constraint.map_ref(ConstraintExpr::evaluate);

                    match constraint.inner {
                        ConstraintExpr::Integer(val) => {
                            // ().at_loc(..).map is a somewhat ugly way to wrap an arbitrary type
                            // in a known Loc. This is done to avoid having to impl WithLocation for
                            // the the unusual tuple used here
                            new_known.push(().at_loc(&constraint).map(|_| (expr.clone(), val)));
                            None
                        }
                        ConstraintExpr::Var(_) => Some(result),
                        ConstraintExpr::Sum(_, _) => Some(result),
                        ConstraintExpr::Sub(_) => Some(result),
                    }
                })
                .collect()
        }

        new_known
    }
}
