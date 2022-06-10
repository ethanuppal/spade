// Heavily inspired by the rust usefulness implementation documented here
// https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_build/thir/pattern/usefulness/index.html
// https://github.com/rust-lang/rust/blob/master/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs
// See https://github.com/rust-lang/rust/blob/master/COPYRIGHT for the rustc copyright

use itertools::Itertools;
use spade_types::ConcreteType;

use crate::pattern::{Constructor, DeconstructedPattern};

#[derive(Clone, Debug)]
pub(crate) struct PatStack {
    pats: Vec<DeconstructedPattern>,
}

impl PatStack {
    pub(crate) fn new(inner: Vec<DeconstructedPattern>) -> Self {
        Self { pats: inner }
    }

    fn head(&self) -> &DeconstructedPattern {
        &self.pats[0]
    }

    fn pop_head(&self, ctor: &Constructor) -> PatStack {
        let mut new_fields = self.head().specialize(ctor);
        new_fields.extend_from_slice(&self.pats[1..]);
        PatStack::new(new_fields)
    }

    fn is_empty(&self) -> bool {
        self.pats.is_empty()
    }
}

impl std::fmt::Display for PatStack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            self.pats.iter().map(|pat| format!("{}", pat)).join(", ")
        )
    }
}

pub(crate) struct Matrix {
    pub patterns: Vec<PatStack>,
}

impl Matrix {
    pub(crate) fn new(patterns: &[PatStack]) -> Self {
        Self {
            patterns: patterns.into(),
        }
    }

    fn empty() -> Self {
        Matrix { patterns: vec![] }
    }

    fn rows(&self) -> &[PatStack] {
        &self.patterns
    }

    fn push(&mut self, new: PatStack) {
        self.patterns.push(new)
    }

    fn specialize(&self, ctor: Constructor) -> Matrix {
        let mut result = Matrix::empty();

        for row in &self.patterns {
            if ctor.is_covered_by(&row.head().ctor) {
                result.push(row.pop_head(&ctor))
            }
        }

        result
    }
}

impl std::fmt::Debug for Matrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "matrix [{}]",
            self.rows().iter().map(|row| format!("{row}")).join("\n")
        )
    }
}

#[derive(Debug, Clone)]
pub struct Witness(pub Vec<DeconstructedPattern>);

impl Witness {
    fn apply_constructor(mut self, ctor: &Constructor, ty: &ConcreteType) -> Self {
        let pat = {
            let len = self.0.len();
            let arity = ctor.arity(ty);
            let fields = self.0.drain((len - arity)..).rev().collect();
            DeconstructedPattern {
                ctor: ctor.clone(),
                fields,
                ty: ty.clone(),
            }
        };

        self.0.push(pat);

        self
    }
}

impl std::fmt::Display for Witness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            write!(f, "*no witnesses*")
        } else if self.0.len() != 1 {
            write!(f, "[{}]", self.0.iter().map(|p| format!("{p}")).join(", "))
        } else {
            write!(f, "{}", self.0[0])
        }
    }
}

pub(crate) struct Usefulness {
    pub witnesses: Vec<Witness>,
}

impl Usefulness {
    fn new_useful() -> Self {
        Self {
            witnesses: vec![Witness(vec![])],
        }
    }

    fn new_useless() -> Self {
        Self { witnesses: vec![] }
    }

    pub(crate) fn is_useful(&self) -> bool {
        !self.witnesses.is_empty()
    }

    fn apply_constructor(self, ctor: &Constructor, ty: &ConcreteType) -> Self {
        if self.witnesses.is_empty() {
            self
        } else {
            let witnesses = self
                .witnesses
                .into_iter()
                .map(|w| w.apply_constructor(ctor, ty))
                .collect();

            Self { witnesses }
        }
    }

    fn extend(&mut self, other: Self) {
        match (self.witnesses.is_empty(), other.witnesses.is_empty()) {
            (_, true) => {}
            (true, _) => *self = other,
            _ => self.witnesses.extend(other.witnesses),
        }
    }
}

impl std::fmt::Display for Usefulness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "witnesses: [{}]",
            self.witnesses.iter().map(|w| format!("{w}")).join(", ")
        )
    }
}

/// Checks if `pattern` is useful with respect to `prev_patterns`, that is, if the
/// pattern matches some value which is not matched by any pattern in `prev_patterns`
pub(crate) fn is_useful(pattern: &PatStack, prev_patterns: &Matrix) -> Usefulness {
    if pattern.is_empty() {
        if prev_patterns.rows().is_empty() {
            return Usefulness::new_useful();
        } else {
            return Usefulness::new_useless();
        }
    };

    let v_ctor = &pattern.head().ctor;

    let ty = &pattern.head().ty;
    let split_ctors = v_ctor.split(
        ty,
        prev_patterns
            .rows()
            .iter()
            .map(|row| row.head().ctor.clone()),
    );

    let mut ret = Usefulness::new_useless();

    for ctor in split_ctors {
        let pattern = pattern.pop_head(&ctor);
        let specialized = prev_patterns.specialize(ctor.clone());

        let usefullness = is_useful(&pattern, &specialized);

        let usefullness = usefullness.apply_constructor(&ctor, &ty);

        ret.extend(usefullness);
    }

    ret
}

#[cfg(test)]
mod test {
    use spade_types::PrimitiveType;

    use super::*;

    #[test]
    fn single_pattern_is_useful_wrt_nothing() {
        let pattern = PatStack::new(vec![DeconstructedPattern {
            ctor: Constructor::Single,
            fields: vec![],
            ty: ConcreteType::Single {
                base: PrimitiveType::Bool,
                params: vec![],
            },
        }]);

        let matrix = Matrix { patterns: vec![] };

        assert!(is_useful(&pattern, &matrix).is_useful())
    }

    #[test]
    fn single_pattern_is_not_useful_wrt_single_pattern() {
        let pattern = PatStack::new(vec![DeconstructedPattern {
            ctor: Constructor::Single,
            fields: vec![],
            ty: ConcreteType::Single {
                base: PrimitiveType::Bool,
                params: vec![],
            },
        }]);

        let matrix = Matrix {
            patterns: vec![pattern.clone()],
        };

        assert!(!is_useful(&pattern, &matrix).is_useful())
    }
}
