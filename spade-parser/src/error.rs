use local_impl::local_impl;
use spade_common::location_info::Loc;
use spade_diagnostics::Diagnostic;
use spade_macros::{IntoDiagnostic, IntoSubdiagnostic};
use thiserror::Error;

use crate::{lexer::TokenKind, Token, TypeSpec};

#[derive(IntoSubdiagnostic)]
#[diagnostic(suggestion, "Use `{` if you want to add items to this enum variant")]
pub(crate) struct SuggestBraceEnumVariant {
    #[diagnostic(replace, "{")]
    pub open_paren: Loc<()>,
    #[diagnostic(replace, "}")]
    pub close_paren: Loc<()>,
}

#[derive(IntoDiagnostic, Clone)]
#[diagnostic(error, "Expected argument list")]
pub(crate) struct ExpectedArgumentList {
    #[diagnostic(primary, "Expected argument list for this instantiation")]
    pub base_expr: Loc<()>,
    pub next_token: Token,
}

impl ExpectedArgumentList {
    pub fn with_suggestions(self) -> Diagnostic {
        let diag: Diagnostic = self.clone().into();
        // If the next token is any kind of opening paren, we'll try to suggest changing that
        if &self.next_token.kind == &TokenKind::OpenBrace
            || &self.next_token.kind == &TokenKind::OpenBracket
        {
            diag.help("Positional argument lists start with`(`.")
                .help("Named argument lists start with `$(`.")
        } else {
            // If not, we'll suggest inserting the argument list after the base expression. We
            // *could* suggest it at the next token, but if the next token is on a new line,
            // that gets confusing
            diag.span_suggest_insert_after(
                "Consider specifying positional arguments",
                self.base_expr,
                "(...)",
            )
            .span_suggest_insert_after("or named arguments", self.base_expr, "$(...)")
        }
    }
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("Lexer error at {} in file {}", 1.0, 0)]
    LexerError(usize, codespan::Span),
    #[error("Unexpected token. Got {}, expected {expected:?}", got.kind.as_str())]
    UnexpectedToken {
        got: Token,
        expected: Vec<&'static str>,
    },
    #[error("Expected to find a {} to match {friend:?}, got {got:?}", expected.as_str())]
    UnmatchedPair {
        friend: Token,
        expected: TokenKind,
        got: Token,
    },

    #[error("Expected expression, got {got:?}")]
    ExpectedExpression { got: Token },

    #[error("Entity missing block for {for_what}")]
    ExpectedBlock {
        for_what: String,
        got: Token,
        loc: Loc<()>,
    },

    #[error("Expected item, got: {got:?}")]
    ExpectedItem { got: Token },

    // Acts mostly like UnexpectedToken but produced by the argument list parser
    // if it encounters the UnexpectedEndOfSCListError, at which point more tokens
    // are added to the returned error. This can not be done to the previous variant
    // as recursive errors of the same kind would then add the token multiple times
    #[error("Unexpected end of argument list")]
    UnexpectedEndOfArgList {
        got: Token,
        expected: Vec<TokenKind>,
    },

    #[error("Expected type, got {0:?}")]
    ExpectedType(Token),

    #[error("Missing tuple index")]
    MissingTupleIndex { hash_loc: Loc<()> },

    #[error("Expected pipeline depth")]
    ExpectedPipelineDepth { got: Token },

    #[error("Expected register count")]
    ExpectedRegisterCount { got: Token },

    #[error("Expected offset")]
    ExpectedOffset { got: Token },

    #[error("Expected expression or stage")]
    ExpectedExpressionOrStage { got: Token },

    #[error("Empty decl statement")]
    EmptyDeclStatement { at: Loc<()> },

    #[error("Reg in function")]
    RegInFunction { at: Loc<()>, fn_keyword: Loc<()> },
    #[error("Stage references are not allowed in functions")]
    PipelineRefInFunction { at: Loc<()>, fn_keyword: Loc<()> },
    #[error("Stage references are not allowed in entities")]
    PipelineRefInEntity {
        at: Loc<()>,
        entity_keyword: Loc<()>,
    },

    #[error("Pipeline in impl")]
    EntityInImpl { loc: Loc<()> },

    #[error("(Internal) Expected an item context to be set")]
    InternalExpectedItemContext { at: Loc<()> },

    #[error("(Internal) Overwriting item context")]
    InternalOverwritingItemContext { at: Loc<()>, prev: Loc<()> },

    #[error("Expected array size")]
    ExpectedArraySize {
        array: Loc<()>,
        inner: Loc<TypeSpec>,
    },
    #[error("Stages are only allowed in the root of pipelines")]
    StageOutsidePipeline(Loc<()>),

    #[error("Attributes are not allowed here")]
    DisallowedAttributes {
        attributes: Loc<()>,
        item_start: Loc<TokenKind>,
    },

    #[error("Spade diagnostic")]
    SpadeDiagnostic(#[from] Diagnostic),
}

impl Error {
    /// If the error is UnexpectedToken, replace it with the error returned by the
    /// provided function. Otherwise, return the error unaffected.
    pub fn specify_unexpected_token(self, f: impl Fn(Token) -> Self) -> Self {
        match self {
            Error::UnexpectedToken { got, .. } => f(got),
            other => other,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

// Error returned by the comma_separated function. Must be explicitly converted
// to the general Error using one of the member methods
#[derive(Error, Debug, Clone)]
pub enum CommaSeparatedError {
    #[error("Inner")]
    Inner(#[from] Error),
    #[error("Unexpected token")]
    UnexpectedToken { got: Token, end_token: TokenKind },
}

pub type CommaSeparatedResult<T> = std::result::Result<T, CommaSeparatedError>;

impl CommaSeparatedError {
    pub fn extra_expected(self, mut extra: Vec<&'static str>) -> Error {
        match self {
            CommaSeparatedError::Inner(inner) => inner,
            CommaSeparatedError::UnexpectedToken { got, end_token } => {
                extra.push(",");
                extra.push(end_token.as_str());
                Error::UnexpectedToken {
                    got,
                    expected: extra,
                }
            }
        }
    }

    pub fn no_context(self) -> Error {
        self.extra_expected(vec![])
    }
}

#[local_impl]
impl<T> CSErrorTransformations for std::result::Result<T, CommaSeparatedError> {
    fn extra_expected(self, extra: Vec<&'static str>) -> Result<T> {
        self.map_err(|e| e.extra_expected(extra))
    }

    fn no_context(self) -> Result<T> {
        self.map_err(|e| e.no_context())
    }
}
