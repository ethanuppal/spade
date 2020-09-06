use codespan::Span;
use derivative::Derivative;

use crate::lexer::TokenKind;

pub trait KindWithLocation<FullStruct> {
    fn at(self, span: Span) -> FullStruct;
    fn nowhere(self) -> FullStruct
    where
        Self: Sized,
    {
        self.at(Span::new(0, 0))
    }
}

pub trait HasSpan {
    fn span(&self) -> Span;
    fn sep_span(self) -> (Self, Span)
    where
        Self: Sized,
    {
        let span = self.span();
        (self, span)
    }
}

#[derive(Derivative)]
#[derivative(PartialEq)]
#[derive(Debug, Clone)]
pub struct Identifier {
    pub name: String,
    #[derivative(PartialEq = "ignore")]
    pub span: Span,
}
impl Identifier {
    pub fn new(name: String, span: Span) -> Self {
        Self { name, span }
    }
}
impl HasSpan for Identifier {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum TypeKind {
    Named(Identifier),
    UnitType,
}
impl KindWithLocation<Type> for TypeKind {
    fn at(self, span: Span) -> Type {
        Type::new(self, span)
    }
}
#[derive(Derivative)]
#[derivative(PartialEq)]
#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    #[derivative(PartialEq = "ignore")]
    pub span: Span,
}
impl Type {
    pub fn new(kind: TypeKind, span: Span) -> Self {
        Self {
            kind,
            span: span.clone(),
        }
    }
}
impl HasSpan for Type {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprKind {
    Identifier(Identifier),
    IntLiteral(u128),
    BinaryOperator(Box<Expression>, TokenKind, Box<Expression>),
    Parenthisised(Box<Expression>),
}

#[derive(Derivative)]
#[derivative(PartialEq)]
#[derive(Debug, Clone)]
pub struct Expression {
    pub kind: ExprKind,
    #[derivative(PartialEq = "ignore")]
    pub span: Span,
}
impl KindWithLocation<Expression> for ExprKind {
    fn at(self, span: Span) -> Expression {
        Expression::new(self, span)
    }
}
impl Expression {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self {
            kind,
            span: span.clone(),
        }
    }
}
impl HasSpan for Expression {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Derivative)]
#[derivative(PartialEq)]
#[derive(Debug, Clone)]
pub enum StmtKind {
    Binding(Identifier, Option<Type>, Expression),
    Register(Register),
}
impl KindWithLocation<Statement> for StmtKind {
    fn at(self, span: Span) -> Statement {
        Statement::new(self, span)
    }
}
#[derive(Derivative)]
#[derivative(PartialEq)]
#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StmtKind,
    #[derivative(PartialEq = "ignore")]
    pub span: Span,
}
impl Statement {
    pub fn new(kind: StmtKind, span: Span) -> Self {
        Self {
            kind,
            span: span.clone(),
        }
    }
}
impl HasSpan for Statement {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Derivative)]
#[derivative(PartialEq)]
#[derive(Debug, Clone)]
pub struct Entity {
    pub name: String,
    pub inputs: Vec<(Identifier, Type)>,
    pub statements: Vec<Statement>,
    pub output_type: Type,
    pub output_value: Expression,
    #[derivative(PartialEq = "ignore")]
    pub span: Span,
}

#[derive(Derivative)]
#[derivative(PartialEq)]
#[derive(Debug, Clone)]
pub struct Register {
    pub name: Identifier,
    pub clock: Identifier,
    pub reset: Option<(Expression, Expression)>,
    pub value: Expression,
    pub value_type: Option<Type>,
    #[derivative(PartialEq = "ignore")]
    pub span: Span,
}
