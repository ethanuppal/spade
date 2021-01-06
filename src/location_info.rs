use codespan::Span;

pub trait WithLocation {
    fn at(self, span: Span) -> Loc<Self>
    where
        Self: Sized,
    {
        Loc::new(self, span)
    }

    fn nowhere(self) -> Loc<Self>
    where
        Self: Sized,
    {
        self.at(Span::new(0, 0))
    }
}

impl WithLocation for () {}

pub fn lspan(s: logos::Span) -> Span {
    Span::new(s.start as u32, s.end as u32)
}

#[cfg(test)]
pub fn dummy() -> Span {
    Span::new(0, 0)
}

#[derive(Clone, Copy, Eq)]
pub struct Loc<T> {
    pub inner: T,
    pub span: Span,
}

impl<T> Loc<T> {
    pub fn new(inner: T, span: Span) -> Self {
        Self { inner, span }
    }
    pub fn nowhere(inner: T) -> Self {
        Self::new(inner, Span::new(0, 0))
    }

    pub fn strip(self) -> T {
        self.inner
    }

    pub fn strip_ref(&self) -> &T {
        &self.inner
    }

    pub fn separate(self) -> (Self, Span) {
        let span = self.span;
        (self, span)
    }

    pub fn split(self) -> (T, Span) {
        (self.inner, self.span)
    }
    pub fn split_ref(&self) -> (&T, Span) {
        (&self.inner, self.span)
    }
    pub fn split_loc(self) -> (T, Loc<()>) {
        let loc = self.loc();
        (self.inner, loc)
    }

    pub fn map<Y>(self, mut op: impl FnMut(T) -> Y) -> Loc<Y> {
        Loc {
            inner: op(self.inner),
            span: self.span,
        }
    }
    pub fn map_ref<Y>(&self, mut op: impl FnMut(&T) -> Y) -> Loc<Y> {
        Loc {
            inner: op(&self.inner),
            span: self.span,
        }
    }

    pub fn loc(&self) -> Loc<()> {
        Loc {
            inner: (),
            span: self.span,
        }
    }
}

impl<T, E> Loc<Result<T, E>> {
    pub fn map_err<E2>(self, err_fn: impl Fn(E, Loc<()>) -> E2) -> Result<Loc<T>, E2> {
        match self.inner {
            Ok(inner) => Ok(Loc {
                inner,
                span: self.span,
            }),
            Err(e) => Err(err_fn(e, ().at(self.span))),
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

impl<T> std::hash::Hash for Loc<T>
where
    T: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl<T> std::fmt::Debug for Loc<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "l({:3}..{:3})[{:?}]",
            self.span.start(),
            self.span.end(),
            self.inner
        )
    }
}

impl<T> std::ops::Deref for Loc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
impl<T> std::ops::DerefMut for Loc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
