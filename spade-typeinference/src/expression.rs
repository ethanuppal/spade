use parse_tree_macros::trace_typechecker;
use spade_common::location_info::Loc;
use spade_hir::expression::{BinaryOperator, UnaryOperator};
use spade_hir::symbol_table::SymbolTable;
use spade_hir::{ExprKind, Expression};
use spade_types::KnownType;

use crate::equation::{TypeVar, TypedExpression};
use crate::fixed_types::t_bool;
use crate::result::Error;
use crate::TraceStack;
use crate::TypeState;
use crate::{kvar, Result};

macro_rules! assuming_kind {
    ($pattern:pat = $expr:expr => $block:block) => {
        if let $pattern = &$expr.inner.kind {
            $block
        } else {
            panic!("Incorrect assumption about expression kind")
        };
    };
}

impl TypeState {
    #[trace_typechecker]
    pub fn visit_identifier(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Identifier(ident) = &expression => {
            // Add an equation for the anonymous id
            self.unify_expression_generic_error(
                &expression,
                &TypedExpression::Name(ident.clone()),
                symtab,
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_int_literal(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::IntLiteral(_) = &expression => {
            let t = self.new_generic_int(symtab);
            self.unify_types(&t, &expression.inner, symtab)
                .map_err(|(_, got)| Error::IntLiteralIncompatible {
                    got,
                    loc: expression.loc(),
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_bool_literal(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::BoolLiteral(_) = &expression => {
            self.unify_expression_generic_error(&expression, &t_bool(symtab), symtab)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_tuple_literal(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TupleLiteral(inner) = &expression => {
            let mut inner_types = vec![];
            for expr in inner {
                self.visit_expression(expr, symtab)?;
                // NOTE: safe unwrap, we know this expr has a type because we just visited
                let t = self.type_of(&TypedExpression::Id(expr.id)).unwrap();

                inner_types.push(t);
            }

            self.unify_expression_generic_error(
                &expression,
                &TypeVar::Tuple(inner_types),
                symtab,
            )?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_tuple_index(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::TupleIndex(tup, index) = &expression => {
            self.visit_expression(tup, symtab)?;
            let t = self.type_of(&TypedExpression::Id(tup.id));

            match t {
                Ok(TypeVar::Tuple(inner)) => {
                    if (index.inner as usize) < inner.len() {
                        self.unify_expression_generic_error(
                            &expression,
                            &inner[index.inner as usize],
                            symtab,
                        )?
                    } else {
                        return Err(Error::TupleIndexOutOfBounds {
                            index: index.clone(),
                            actual_size: inner.len() as u128,
                        });
                    }
                }
                Ok(t @ TypeVar::Known(_, _, _) | t @ TypeVar::Array { .. }) => {
                    return Err(Error::TupleIndexOfNonTuple {
                        got: t.clone(),
                        loc: tup.loc(),
                    })
                }
                Ok(TypeVar::Unknown(_)) => {
                    return Err(Error::TupleIndexOfGeneric { loc: tup.loc() })
                }
                Err(e) => return Err(e),
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_array_literal(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::ArrayLiteral(members) = &expression => {
            let inner_type = self.new_generic();
            for expr in members {
                self.visit_expression(expr, symtab)?;

                self.add_equation(TypedExpression::Id(expr.id), inner_type.clone());

                self.unify_types(expr, &inner_type, symtab)
                    .map_err(|(expected, got)| Error::ArrayElementMissmatch {
                        got,
                        expected,
                        loc: expr.loc(),
                        first_element: members.first().unwrap().loc(),
                    })?;
            }
            let size_type = kvar!(KnownType::Integer(members.len() as u128));
            let result_type = TypeVar::Array {
                inner: Box::new(inner_type),
                size: Box::new(size_type),
            };

            self.unify_expression_generic_error(expression, &result_type, symtab)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_index(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Index(target, index) = &expression => {
            // self.visit_expression(&target, symtab)?;
            self.visit_expression(&index, symtab)?;

            let int_type = self.new_generic_int(&symtab);
            // self.add_equation(TypedExpression::Id(index.id), int_type.clone());
            self.unify_types(&index.inner, &int_type, symtab)
                .map_err(|(got, _)| {
                    Error::IndexMustBeInteger{got, loc: index.loc()}
                })?;

            // self.unify_expression_generic_error(expr, other, symtab)
            // let inner_type = self.new_generic();

            // todo!("Impl array indexing type check")
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_block_expr(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Block(block) = &expression => {
            self.visit_block(block, symtab)?;

            // Unify the return type of the block with the type of this expression
            self.unify_types(&expression.inner, &block.result.inner, symtab)
                // NOTE: We could be more specific about this error specifying
                // that the type of the block must match the return type, though
                // that might just be spammy.
                .map_err(|(expected, got)| Error::UnspecifiedTypeError {
                    expected,
                    got,
                    loc: block.result.loc(),
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_if(&mut self, expression: &Loc<Expression>, symtab: &SymbolTable) -> Result<()> {
        assuming_kind!(ExprKind::If(cond, on_true, on_false) = &expression => {
            self.visit_expression(&cond, symtab)?;
            self.visit_expression(&on_true, symtab)?;
            self.visit_expression(&on_false, symtab)?;

            self.unify_types(&cond.inner, &t_bool(symtab), symtab)
                .map_err(|(got, _)| Error::NonBooleanCondition {
                    got,
                    loc: cond.loc(),
                })?;
            self.unify_types(&on_true.inner, &on_false.inner, symtab)
                .map_err(|(expected, got)| Error::IfConditionMismatch {
                    expected,
                    got,
                    first_branch: on_true.loc(),
                    incorrect_branch: on_false.loc(),
                })?;
            self.unify_types(expression, &on_false.inner, symtab)
                .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                    expected,
                    got,
                    loc: expression.loc(),
                })?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_match(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::Match(cond, branches) = &expression => {
            self.visit_expression(&cond, symtab)?;

            for (i, (pattern, result)) in branches.iter().enumerate() {
                self.visit_pattern(pattern, symtab)?;
                self.visit_expression(result, symtab)?;

                self.unify_types(&cond.inner, pattern, symtab)
                    .map_err(|(expected, got)| {
                        // TODO, Consider introducing a more specific error
                        Error::UnspecifiedTypeError {
                            expected,
                            got,
                            loc: pattern.loc(),
                        }
                    })?;

                if i != 0 {
                    self.unify_types(&branches[0].1, result, symtab).map_err(
                        |(expected, got)| Error::MatchBranchMissmatch {
                            expected,
                            got,
                            first_branch: branches[0].1.loc(),
                            incorrect_branch: result.loc(),
                        },
                    )?;
                }
            }

            assert!(
                !branches.is_empty(),
                "Empty match statements should be checked by ast lowering"
            );

            self.unify_expression_generic_error(&branches[0].1, expression, symtab)?;
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_binary_operator(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::BinaryOperator(lhs, op, rhs) = &expression => {
            self.visit_expression(&lhs, symtab)?;
            self.visit_expression(&rhs, symtab)?;
            match *op {
                BinaryOperator::Add
                | BinaryOperator::Sub
                | BinaryOperator::Mul
                | BinaryOperator::LeftShift
                | BinaryOperator::BitwiseAnd
                | BinaryOperator::BitwiseOr
                | BinaryOperator::RightShift => {
                    let int_type = self.new_generic_int(symtab);
                    // TODO: Make generic over types that can be added
                    self.unify_expression_generic_error(&lhs, &int_type, symtab)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;
                    self.unify_expression_generic_error(expression, &rhs.inner, symtab)?
                }
                BinaryOperator::Eq
                | BinaryOperator::Gt
                | BinaryOperator::Lt
                | BinaryOperator::Ge
                | BinaryOperator::Le => {
                    let int_type = self.new_generic_int(symtab);
                    // TODO: Make generic over types that can be added
                    self.unify_expression_generic_error(&lhs, &int_type, symtab)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;
                    self.unify_expression_generic_error(expression, &t_bool(symtab), symtab)?
                }
                BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::Xor => {
                    // TODO: Make generic over types that can be ored
                    self.unify_expression_generic_error(&lhs, &t_bool(symtab), symtab)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;

                    self.unify_expression_generic_error(expression, &t_bool(symtab), symtab)?
                }
            }
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_unary_operator(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        assuming_kind!(ExprKind::UnaryOperator(op, operand) = &expression => {
            self.visit_expression(&operand, symtab)?;
            match op {
                UnaryOperator::Sub => {
                    let int_type = self.new_generic_int(symtab);
                    self.unify_expression_generic_error(operand, &int_type, symtab)?
                }
                UnaryOperator::Not => {
                    self.unify_expression_generic_error(operand, &t_bool(symtab), symtab)?
                }
            }
        });
        Ok(())
    }
}
