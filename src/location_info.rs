use codespan::Span;

pub fn lspan(s: logos::Span) -> Span {
    Span::new(s.start as u32, s.end as u32)
}

#[cfg(test)]
pub fn dummy() -> Span {
    Span::new(0, 0)
}
