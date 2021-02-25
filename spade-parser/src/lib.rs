pub mod ast;
pub mod lexer;

use spade_common::location_info::{lspan, Loc, WithLocation};

use colored::*;
use logos::Lexer;
use thiserror::Error;

use parse_tree_macros::trace_parser;

use crate::ast::{
    Block, Entity, Expression, FunctionDecl, Identifier, Item, ModuleBody, Path, Register,
    Statement, TraitDef, TypeExpression, TypeParam, TypeSpec,
};
use crate::lexer::TokenKind;

/// A token with location info
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: logos::Span,
}

impl Token {
    pub fn new(kind: TokenKind, lexer: &Lexer<TokenKind>) -> Self {
        Self {
            kind,
            span: lexer.span(),
        }
    }
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("End of file")]
    Eof,
    #[error("Lexer error at {}", 0.0)]
    LexerError(codespan::Span),
    #[error("Unexpected token. got {}, expected {expected:?}", got.kind.as_str())]
    UnexpectedToken {
        got: Token,
        expected: Vec<&'static str>,
    },
    #[error("Expected to find a {} to match {friend:?}", expected.as_str())]
    UnmatchedPair { friend: Token, expected: TokenKind },

    #[error("Expected expression, got {got:?}")]
    ExpectedExpression { got: Token },

    #[error("Entity missing block for {for_what}")]
    ExpectedBlock {
        for_what: String,
        got: Token,
        loc: Loc<()>,
    },

    #[error("Missing tuple index")]
    MissingTupleIndex { hash_loc: Loc<()> },
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct Parser<'a> {
    lex: Lexer<'a, TokenKind>,
    peeked: Option<Token>,
    pub parse_stack: Vec<ParseStackEntry>,
}

impl<'a> Parser<'a> {
    pub fn new(lex: Lexer<'a, TokenKind>) -> Self {
        Self {
            lex,
            peeked: None,
            parse_stack: vec![],
        }
    }
}

macro_rules! operator_expr {
    ($this_operator:ident, $condition:ident, $next:ident) => {
        fn $this_operator(&mut self) -> Result<Loc<Expression>> {
            self.binary_operator(Self::$next, Self::$condition, Self::$this_operator)
        }
    };
}

// Actual parsing functions
impl<'a> Parser<'a> {
    #[trace_parser]
    pub fn identifier(&mut self) -> Result<Loc<Identifier>> {
        let token = self.eat_cond(TokenKind::is_ident, "Identifier")?;

        if let TokenKind::Identifier(name) = token.kind {
            Ok(Identifier(name).at(lspan(token.span)))
        } else {
            unreachable!("eat_cond should have checked this");
        }
    }

    #[trace_parser]
    pub fn path(&mut self) -> Result<Loc<Path>> {
        let mut result = vec![];
        loop {
            result.push(self.identifier()?);

            if let None = self.peek_and_eat_kind(&TokenKind::PathSeparator)? {
                break;
            }
        }
        // NOTE: (safe unwrap) The vec will have at least one element because the first thing
        // in the loop must pus an identifier.
        let start = result.first().unwrap().span;
        let end = result.last().unwrap().span;
        Ok(Path(result).at(start.merge(end)))
    }

    pub fn binary_operator(
        &mut self,
        lhs: impl Fn(&mut Self) -> Result<Loc<Expression>>,
        condition: impl Fn(&mut Self) -> Result<bool>,
        rhs: impl Fn(&mut Self) -> Result<Loc<Expression>>,
    ) -> Result<Loc<Expression>> {
        let start = lhs(self)?;

        if condition(self)? {
            let operator = self.eat_unconditional()?;
            let rest = rhs(self)?;

            let span = start.span.merge(rest.span);
            Ok(Expression::BinaryOperator(Box::new(start), operator.kind, Box::new(rest)).at(span))
        } else {
            Ok(start)
        }
    }

    // Expression parsing
    #[trace_parser]
    pub fn expression(&mut self) -> Result<Loc<Expression>> {
        let expr = self.logical_or_expression()?;

        if let Some(hash) = self.peek_and_eat_kind(&TokenKind::Hash)? {
            if let Some(index) = self.int_literal()? {
                let span = expr.span.merge(lspan(hash.span));
                Ok(Expression::TupleIndex(Box::new(expr), index).at(span))
            } else {
                Err(Error::MissingTupleIndex {
                    hash_loc: Loc::new((), lspan(hash.span)),
                })
            }
        } else {
            Ok(expr)
        }
    }

    operator_expr!(
        logical_or_expression,
        is_next_logical_or,
        logical_and_expression
    );
    operator_expr!(
        logical_and_expression,
        is_next_logical_and,
        comparison_operator
    );
    operator_expr!(
        comparison_operator,
        is_next_comparison_operator,
        shift_expression
    );
    operator_expr!(
        shift_expression,
        is_next_shift_operator,
        additive_expression
    );
    operator_expr!(
        additive_expression,
        is_next_addition_operator,
        multiplicative_expression
    );
    operator_expr!(
        multiplicative_expression,
        is_next_multiplication_operator,
        base_expression
    );

    #[trace_parser]
    pub fn base_expression(&mut self) -> Result<Loc<Expression>> {
        if self.peek_and_eat_kind(&TokenKind::OpenParen)?.is_some() {
            let mut inner = self.comma_separated(Self::expression, &TokenKind::CloseParen)?;
            let result = if inner.is_empty() {
                todo!("Implement unit literals")
            } else if inner.len() == 1 {
                // NOTE: safe unwrap, we know the size of the array
                Ok(inner.pop().unwrap())
            } else {
                let span = inner
                    .first()
                    .unwrap()
                    .span
                    .merge(inner.last().unwrap().span);
                Ok(Expression::TupleLiteral(inner).at(span))
            };
            self.eat(&TokenKind::CloseParen)?;
            result
        } else if let Some(tok) = self.peek_and_eat_kind(&TokenKind::True)? {
            Ok(Expression::BoolLiteral(true).at(lspan(tok.span)))
        } else if let Some(tok) = self.peek_and_eat_kind(&TokenKind::False)? {
            Ok(Expression::BoolLiteral(false).at(lspan(tok.span)))
        } else if let Some(val) = self.int_literal()? {
            Ok(val.map(Expression::IntLiteral))
        } else if let Some(block) = self.block()? {
            Ok(block.map(Box::new).map(Expression::Block))
        } else if let Some(if_expr) = self.if_expression()? {
            Ok(if_expr)
        } else {
            match self.path() {
                Ok(path) => {
                    let span = path.span;
                    Ok(Expression::Identifier(path).at(span))
                }
                Err(Error::UnexpectedToken { got, .. }) => Err(Error::ExpectedExpression { got }),
                Err(e) => Err(e),
            }
        }
    }

    #[trace_parser]
    pub fn if_expression(&mut self) -> Result<Option<Loc<Expression>>> {
        if let Some(start) = self.peek_and_eat_kind(&TokenKind::If)? {
            let cond = self.expression()?;
            let on_true = self.expression()?;
            self.eat(&TokenKind::Else)?;
            let (on_false, end_span) = self.expression()?.separate();

            Ok(Some(
                Expression::If(Box::new(cond), Box::new(on_true), Box::new(on_false))
                    .at(lspan(start.span).merge(end_span)),
            ))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn int_literal(&mut self) -> Result<Option<Loc<u128>>> {
        if self.peek_cond(TokenKind::is_integer, "integer")? {
            let token = self.eat_unconditional()?;
            match token.kind {
                TokenKind::Integer(val) => Ok(Some(Loc::new(val, lspan(token.span)))),
                _ => unreachable!(),
            }
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn block(&mut self) -> Result<Option<Loc<Block>>> {
        let start = if let Some(start) = self.peek_and_eat_kind(&TokenKind::OpenBrace)? {
            start
        } else {
            return Ok(None);
        };
        let statements = self.statements()?;
        let output_value = self.expression()?;
        let end_token = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(
            Block {
                statements,
                result: output_value,
            }
            .at(lspan(start.span).merge(lspan(end_token.span))),
        ))
    }

    #[trace_parser]
    pub fn type_expression(&mut self) -> Result<Loc<TypeExpression>> {
        if let Some(val) = self.int_literal()? {
            Ok(val.map(TypeExpression::Integer))
        } else {
            let inner = self.type_spec()?;

            Ok(TypeExpression::TypeSpec(Box::new(inner.clone())).at_loc(&inner))
        }
    }

    // Types
    #[trace_parser]
    pub fn type_spec(&mut self) -> Result<Loc<TypeSpec>> {
        if let Some(tuple) = self.tuple_spec()? {
            Ok(tuple)
        } else {
            let (path, span) = self.path()?.separate();

            // Check if this type has generic params
            let (params, generic_span) = if self.peek_kind(&TokenKind::Lt)? {
                let (type_expr, generic_span) = self.surrounded(
                    &TokenKind::Lt,
                    |s| s.type_expression().map(Some),
                    &TokenKind::Gt,
                )?;

                // Note: safe unwrap, if we got here, the expression must have matched
                // and so the size is present, otherwise we'd return early above
                let type_expr = type_expr.unwrap();
                (vec![type_expr], generic_span.span)
            } else {
                (vec![], span)
            };

            Ok(TypeSpec::Named(path, params).at(span.merge(generic_span)))
        }
    }

    #[trace_parser]
    pub fn tuple_spec(&mut self) -> Result<Option<Loc<TypeSpec>>> {
        if let Some(start) = self.peek_and_eat_kind(&TokenKind::OpenParen)? {
            let inner = self.comma_separated(Self::type_spec, &TokenKind::CloseParen)?;
            let end = self.eat(&TokenKind::CloseParen)?;

            let span = lspan(start.span).merge(lspan(end.span));

            Ok(Some(TypeSpec::Tuple(inner).at(span)))
        } else {
            Ok(None)
        }
    }

    /// A name with an associated type, as used in argument definitions as well
    /// as struct defintions
    ///
    /// name: Type
    // TODO: Use this for let bindings
    #[trace_parser]
    pub fn name_and_type(&mut self) -> Result<(Loc<Identifier>, Loc<TypeSpec>)> {
        let name = self.identifier()?;
        self.eat(&TokenKind::Colon)?;
        let t = self.type_spec()?;
        Ok((name, t))
    }

    // Statemenets

    #[trace_parser]
    pub fn binding(&mut self) -> Result<Option<Loc<Statement>>> {
        if self.peek_and_eat_kind(&TokenKind::Let)?.is_some() {
            let (ident, start_span) = self.identifier()?.separate();

            let t = if self.peek_and_eat_kind(&TokenKind::Colon)?.is_some() {
                Some(self.type_spec()?)
            } else {
                None
            };

            self.eat(&TokenKind::Assignment)?;
            let (value, end_span) = self.expression()?.separate();

            Ok(Some(
                Statement::Binding(ident, t, value).at(start_span.merge(end_span)),
            ))
        } else {
            Ok(None)
        }
    }

    #[trace_parser]
    pub fn register_reset_definition(&mut self) -> Result<(Loc<Expression>, Loc<Expression>)> {
        let condition = self.expression()?;
        self.eat(&TokenKind::Colon)?;
        let value = self.expression()?;

        Ok((condition, value))
    }

    #[trace_parser]
    pub fn register(&mut self) -> Result<Option<Loc<Statement>>> {
        if let Some(start_token) = self.peek_and_eat_kind(&TokenKind::Reg)? {
            // Clock selection
            let (clock, _clock_paren_span) = self.surrounded(
                &TokenKind::OpenParen,
                |s| s.expression().map(Some),
                &TokenKind::CloseParen,
            )?;

            // Identifier parsing can not fail since we map it into a Some. Therefore,
            // unwrap is safe
            let clock = clock.unwrap();

            // Name
            let name = self.identifier()?;

            // Optional type
            let value_type = if self.peek_and_eat_kind(&TokenKind::Colon)?.is_some() {
                Some(self.type_spec()?)
            } else {
                None
            };

            // Optional reset
            let reset = if self.peek_and_eat_kind(&TokenKind::Reset)?.is_some() {
                let (reset, _) = self.surrounded(
                    &TokenKind::OpenParen,
                    |s| s.register_reset_definition().map(Some),
                    &TokenKind::CloseParen,
                )?;
                reset
            } else {
                None
            };

            // Value
            self.eat(&TokenKind::Assignment)?;
            let (value, end_span) = self.expression()?.separate();

            let span = lspan(start_token.span).merge(end_span);
            let result = Statement::Register(
                Register {
                    name,
                    clock,
                    reset,
                    value,
                    value_type,
                }
                .at(span),
            )
            .at(span);
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    /// If the next token is the start of a statement, return that statement,
    /// otherwise None
    #[trace_parser]
    pub fn statement(&mut self) -> Result<Option<Loc<Statement>>> {
        let result = self.first_successful(vec![&Self::binding, &Self::register])?;
        if result.is_some() {
            self.eat(&TokenKind::Semi)?;
        }
        Ok(result)
    }

    #[trace_parser]
    pub fn statements(&mut self) -> Result<Vec<Loc<Statement>>> {
        let mut result = vec![];
        while let Some(statement) = self.statement()? {
            result.push(statement)
        }
        Ok(result)
    }

    #[trace_parser]
    pub fn self_arg(&mut self) -> Result<Option<Loc<()>>> {
        if self.peek_cond(
            |t| t == &TokenKind::Identifier("self".to_string()),
            "looking for self",
        )? {
            let tok = self.eat_unconditional()?;
            Ok(Some(().at(lspan(tok.span))))
        } else {
            Ok(None)
        }
    }

    // Entities
    #[trace_parser]
    pub fn entity(&mut self) -> Result<Option<Loc<Entity>>> {
        let start_token = if let Some(t) = self.peek_and_eat_kind(&TokenKind::Entity)? {
            t
        } else {
            return Ok(None);
        };

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

        // Input types
        self.eat(&TokenKind::OpenParen)?;
        let inputs = self.comma_separated(Self::name_and_type, &TokenKind::CloseParen)?;
        let close_paren = self.eat(&TokenKind::CloseParen)?;

        // Return type
        let output_type = if self.peek_and_eat_kind(&TokenKind::SlimArrow)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        // Body (TODO: might want to make this a separate structure like a block)
        let (block, block_span) = if let Some(block) = self.block()? {
            block.separate()
        } else {
            // The end of the entity definition depends on wether or not
            // a type is present.
            let end_loc = output_type
                .map(|t| t.loc().span)
                .unwrap_or_else(|| lspan(close_paren.span));

            return Err(Error::ExpectedBlock {
                // NOTE: Unwrap should be safe becase we have already checked
                // if this is a { or not
                for_what: "entity".to_string(),
                got: self.peek()?.unwrap(),
                loc: Loc::new((), lspan(start_token.span).merge(end_loc)),
            });
        };

        Ok(Some(
            Entity {
                name,
                inputs,
                output_type,
                body: block.map(|inner| Expression::Block(Box::new(inner))),
                type_params,
            }
            .at(lspan(start_token.span).merge(block_span)),
        ))
    }

    #[trace_parser]
    pub fn type_param(&mut self) -> Result<Loc<TypeParam>> {
        // If this is a type level integer
        if let Some(hash) = self.peek_and_eat_kind(&TokenKind::Hash)? {
            let (id, loc) = self.identifier()?.separate();
            Ok(TypeParam::Integer(id).at(lspan(hash.span).merge(loc)))
        } else {
            Ok(self.identifier()?.map(TypeParam::TypeName))
        }
    }

    #[trace_parser]
    pub fn generics_list(&mut self) -> Result<Vec<Loc<TypeParam>>> {
        if let Some(lt) = self.peek_and_eat_kind(&TokenKind::Lt)? {
            let params = self.comma_separated(Self::type_param, &TokenKind::Gt)?;
            self.eat(&TokenKind::Gt).map_err(|_| Error::UnmatchedPair {
                friend: lt,
                expected: TokenKind::Gt,
            })?;
            Ok(params)
        } else {
            Ok(vec![])
        }
    }

    // Traits
    #[trace_parser]
    pub fn function_decl(&mut self) -> Result<Option<Loc<FunctionDecl>>> {
        let start_token = if let Some(t) = self.peek_and_eat_kind(&TokenKind::Function)? {
            t
        } else {
            return Ok(None);
        };

        let name = self.identifier()?;

        let type_params = self.generics_list()?;

        // Input types
        self.eat(&TokenKind::OpenParen)?;
        let (self_arg, more_args) = if let Some(arg) = self.self_arg()? {
            if let Some(_) = self.peek_and_eat_kind(&TokenKind::Comma)? {
                (Some(arg), true)
            } else if let Some(_) = self.peek_and_eat_kind(&TokenKind::CloseParen)? {
                (Some(arg), false)
            } else {
                let next = self.eat_unconditional()?;
                return Err(Error::UnexpectedToken {
                    got: next,
                    expected: vec![TokenKind::Comma.as_str(), TokenKind::CloseParen.as_str()],
                });
            }
        } else {
            (None, true)
        };

        let inputs = if more_args {
            let inputs = self.comma_separated(Self::name_and_type, &TokenKind::CloseParen)?;
            self.eat(&TokenKind::CloseParen)?;
            inputs
        } else {
            vec![]
        };

        // Return type
        let return_type = if self.peek_and_eat_kind(&TokenKind::SlimArrow)?.is_some() {
            Some(self.type_spec()?)
        } else {
            None
        };

        let end_token = self.eat(&TokenKind::Semi)?;

        Ok(Some(
            FunctionDecl {
                name,
                self_arg,
                inputs,
                return_type,
                type_params,
            }
            .at(lspan(start_token.span).merge(lspan(end_token.span))),
        ))
    }

    #[trace_parser]
    pub fn trait_def(&mut self) -> Result<Option<Loc<TraitDef>>> {
        let start_token = if let Some(start) = self.peek_and_eat_kind(&TokenKind::Trait)? {
            start
        } else {
            return Ok(None);
        };

        let name = self.identifier()?;

        let mut result = TraitDef {
            name,
            functions: vec![],
        };

        self.eat(&TokenKind::OpenBrace)?;

        while let Some(decl) = self.function_decl()? {
            result.functions.push(decl);
        }
        let end_token = self.eat(&TokenKind::CloseBrace)?;

        Ok(Some(
            result.at(lspan(start_token.span).merge(lspan(end_token.span))),
        ))
    }

    #[trace_parser]
    pub fn item(&mut self) -> Result<Option<Item>> {
        self.first_successful(vec![
            &|s: &mut Self| s.entity().map(|e| e.map(Item::Entity)),
            &|s: &mut Self| s.trait_def().map(|e| e.map(Item::TraitDef)),
        ])
    }

    #[trace_parser]
    pub fn module_body(&mut self) -> Result<ModuleBody> {
        let mut members = vec![];
        while let Some(item) = self.item()? {
            members.push(item)
        }
        Ok(ModuleBody { members })
    }
}

// Helper functions for checking the type of tokens
impl<'a> Parser<'a> {
    fn is_next_addition_operator(&mut self) -> Result<bool> {
        Ok(match self.peek()?.map(|token| token.kind) {
            Some(TokenKind::Plus) => true,
            Some(TokenKind::Minus) => true,
            _ => false,
        })
    }
    fn is_next_shift_operator(&mut self) -> Result<bool> {
        Ok(match self.peek()?.map(|token| token.kind) {
            Some(TokenKind::LeftShift) => true,
            Some(TokenKind::RightShift) => true,
            _ => false,
        })
    }
    fn is_next_multiplication_operator(&mut self) -> Result<bool> {
        Ok(match self.peek()?.map(|token| token.kind) {
            Some(TokenKind::Asterisk) => true,
            Some(TokenKind::Slash) => true,
            _ => false,
        })
    }
    fn is_next_comparison_operator(&mut self) -> Result<bool> {
        Ok(match self.peek()?.map(|token| token.kind) {
            Some(TokenKind::Equals) => true,
            Some(TokenKind::Gt) => true,
            Some(TokenKind::Lt) => true,
            _ => false,
        })
    }
    fn is_next_logical_and(&mut self) -> Result<bool> {
        Ok(match self.peek()?.map(|token| token.kind) {
            Some(TokenKind::LogicalAnd) => true,
            _ => false,
        })
    }
    fn is_next_logical_or(&mut self) -> Result<bool> {
        Ok(match self.peek()?.map(|token| token.kind) {
            Some(TokenKind::LogicalOr) => true,
            _ => false,
        })
    }
}

// Helper functions for combining parsers
impl<'a> Parser<'a> {
    fn first_successful<T>(
        &mut self,
        parsers: Vec<&dyn Fn(&mut Self) -> Result<Option<T>>>,
    ) -> Result<Option<T>> {
        for parser in parsers {
            match parser(self) {
                Ok(Some(val)) => return Ok(Some(val)),
                Ok(None) => continue,
                Err(e) => return Err(e),
            }
        }
        Ok(None)
    }

    /// Attempts to parse an inner structure surrouned by two tokens, like `( x )`.
    ///
    /// If the `start` token is not found, an error is produced.
    ///
    /// If the `start` token is found, but the inner parser returns `None`, `None` is returned.
    ///
    /// If the end token is not found, return a missmatch error
    fn surrounded<T>(
        &mut self,
        start: &TokenKind,
        inner: impl Fn(&mut Self) -> Result<Option<T>>,
        end: &TokenKind,
    ) -> Result<(Option<T>, Loc<()>)> {
        let opener = self.eat(start)?;
        let result = inner(self)?;
        // TODO: Better error handling here. We are throwing away potential EOFs
        let end = self.eat(end).map_err(|_| Error::UnmatchedPair {
            friend: opener.clone(),
            expected: end.clone(),
        })?;

        Ok((
            result,
            Loc::new((), lspan(opener.span).merge(lspan(end.span))),
        ))
    }

    #[trace_parser]
    pub fn comma_separated<T>(
        &mut self,
        inner: impl Fn(&mut Self) -> Result<T>,
        // This end marker is used for allowing trailing commas. It should
        // be whatever ends the collection that is searched. I.e. (a,b,c,) should have
        // `)`, and {} should have `}`
        end_marker: &TokenKind,
    ) -> Result<Vec<T>> {
        let mut result = vec![];

        loop {
            // The list might be empty
            if self.peek_kind(end_marker)? {
                break;
            }
            result.push(inner(self)?);

            // Now we expect to either find a comma, in which case we resume the
            // search, or an end marker, in which case we abort
            if self.peek_kind(end_marker)? {
                break;
            } else {
                self.eat(&TokenKind::Comma)?;
            }
        }
        Ok(result)
    }
}

// Helper functions for advancing the token stream
impl<'a> Parser<'a> {
    fn eat(&mut self, expected: &TokenKind) -> Result<Token> {
        self.eat_cond(|k| k == expected, expected.as_str())
    }

    fn eat_cond(
        &mut self,
        condition: impl Fn(&TokenKind) -> bool,
        expected_description: &'static str,
    ) -> Result<Token> {
        // Check if we already have a peeked token
        let next = self.eat_unconditional()?;

        // Make sure we ate the correct token
        if !condition(&next.kind) {
            Err(Error::UnexpectedToken {
                got: next,
                expected: vec![expected_description],
            })
        } else {
            Ok(next)
        }
    }

    fn eat_unconditional(&mut self) -> Result<Token> {
        let food = self
            .peeked
            .take()
            .map(Ok)
            .unwrap_or_else(|| self.next_token())?;

        self.parse_stack.push(ParseStackEntry::Ate(food.clone()));
        Ok(food)
    }

    /// Peeks the next token. If it is the sepcified kind, returns that token, otherwise
    /// returns None
    fn peek_and_eat_kind(&mut self, kind: &TokenKind) -> Result<Option<Token>> {
        if self.peek_kind(kind)? {
            Ok(Some(self.eat_unconditional()?))
        } else {
            Ok(None)
        }
    }

    fn peek(&mut self) -> Result<Option<Token>> {
        if let Some(prev) = self.peeked.clone() {
            Ok(Some(prev))
        } else {
            let result = match self.next_token() {
                Ok(token) => Some(token),
                Err(Error::Eof) => None,
                Err(e) => return Err(e),
            };
            self.peeked = result.clone();
            Ok(result)
        }
    }

    fn peek_kind(&mut self, expected: &TokenKind) -> Result<bool> {
        let result = self.peek_cond_no_tracing(|kind| kind == expected)?;
        self.parse_stack
            .push(ParseStackEntry::PeekingFor(expected.clone(), result));
        Ok(result)
    }

    /// Peek the next token, returning true if the result satisfies the condition.
    ///
    /// If we reached EOF and the peek returns None, returns false
    fn peek_cond(&mut self, cond: impl Fn(&TokenKind) -> bool, msg: &str) -> Result<bool> {
        let result = self.peek_cond_no_tracing(cond)?;
        self.parse_stack.push(ParseStackEntry::PeekingWithCondition(
            msg.to_string(),
            result,
        ));
        Ok(result)
    }

    fn peek_cond_no_tracing(&mut self, cond: impl Fn(&TokenKind) -> bool) -> Result<bool> {
        self.peek().map(|token| {
            if let Some(inner) = token {
                cond(&inner.kind)
            } else {
                false
            }
        })
    }

    fn next_token(&mut self) -> Result<Token> {
        let kind = self.lex.next().ok_or(Error::Eof)?;

        if let TokenKind::Error = kind {
            Err(Error::LexerError(lspan(self.lex.span())))?
        };

        Ok(Token::new(kind, &self.lex))
    }
}

pub enum ParseStackEntry {
    Enter(String),
    Ate(Token),
    PeekingWithCondition(String, bool),
    PeekingFor(TokenKind, bool),
    Exit,
    ExitWithError(Error),
}
pub fn format_parse_stack(stack: &[ParseStackEntry]) -> String {
    let mut result = String::new();
    let mut indent_amount = 0;

    for entry in stack {
        let mut next_indent_amount = indent_amount;
        let message = match entry {
            ParseStackEntry::Enter(function) => {
                next_indent_amount += 1;
                format!("{} `{}`", "trying".white(), function.blue())
            }
            ParseStackEntry::Ate(token) => format!(
                "{} '{}'",
                "Eating".bright_yellow(),
                token.kind.as_str().bright_purple()
            ),
            ParseStackEntry::PeekingFor(kind, success) => format!(
                "{} {} {}",
                "peeking for".white(),
                kind.as_str().bright_blue(),
                if *success {
                    "✓".green()
                } else {
                    "𐄂".red()
                }
            ),
            ParseStackEntry::PeekingWithCondition(needle, success) => format!(
                "{} {} {}",
                "peeking conditionally for ".white(),
                needle.bright_blue(),
                if *success {
                    "✓".green()
                } else {
                    "𐄂".red()
                }
            ),
            ParseStackEntry::Exit => {
                next_indent_amount -= 1;
                format!("")
            }
            ParseStackEntry::ExitWithError(err) => {
                next_indent_amount -= 1;
                format!("{} {}", "Giving up: ".bright_red(), err)
            }
        };
        if let ParseStackEntry::Exit = entry {
        } else {
            for _ in 0..indent_amount {
                result += "| ";
            }
            result += &message;
            result += "\n"
        }
        indent_amount = next_indent_amount;
    }
    result
}
