use codespan::Span;

pub fn lspan(s: logos::Span) -> Span {
    Span::new(s.start as u32, s.end as u32)
}

#[cfg(test)]
pub fn dummy() -> Span {
    Span::new(0, 0)
}

#[derive(Clone, Debug, Copy)]
pub struct Loc<T> {
    pub inner: T,
    pub span: Span,
}

impl<T> Loc<T> {
    pub fn new(inner: T, span: Span) -> Self {
        Self { inner, span }
    }

    pub fn separate(self) -> (Self, Span) {
        let span = self.span;
        (self, span)
    }

    pub fn map<Y>(self, op: impl Fn(T) -> Y) -> Loc<Y> {
        Loc {
            inner: op(self.inner),
            span: self.span,
        }
    }
}

impl<T> PartialEq for Loc<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}
