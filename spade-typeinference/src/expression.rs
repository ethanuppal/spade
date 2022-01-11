use parse_tree_macros::trace_typechecker;
use spade_common::location_info::Loc;
use spade_hir::expression::{BinaryOperator, UnaryOperator};
use spade_hir::symbol_table::SymbolTable;
use spade_hir::{ExprKind, Expression};
use spade_types::KnownType;

use crate::equation::{InnerTypeVar, TypeVarRef, TypedExpression};
use crate::fixed_types::t_bool;
use crate::result::Error;
use crate::TypeState;
use crate::{kvar, Result};
use crate::{HasType, TraceStackEntry};

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
            )?.commit(self);
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
            self.unify(t.as_ref(), &expression.inner, symtab)
                .map_err(|(_, got)| Error::IntLiteralIncompatible {
                    got,
                    loc: expression.loc(),
                })?.commit(self);
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
            self.unify_expression_generic_error(&expression, &t_bool(symtab), symtab)?.commit(self);
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
            for expr in inner {
                self.visit_expression(expr, symtab)?;
                // NOTE: safe unwrap, we know this expr has a type because we just visited
            }

            let mut inner_types = vec![];
            for expr in inner {
                let t = self.type_of(&TypedExpression::Id(expr.id)).unwrap();

                inner_types.push(t);
            }

            self.unify_expression_generic_error(
                &expression,
                TypeVarRef::tuple(inner_types).as_ref(),
                symtab,
            )?.commit(self);
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

            match t.as_ref().map(|t| t.as_ref()) {
                Ok(InnerTypeVar::Tuple(inner)) => {
                    if (index.inner as usize) < inner.len() {
                        self.unify_expression_generic_error(
                            &expression,
                            &inner[index.inner as usize],
                            symtab,
                        )?.commit(self)
                    } else {
                        return Err(Error::TupleIndexOutOfBounds {
                            index: index.clone(),
                            actual_size: inner.len() as u128,
                        });
                    }
                }
                Ok(t @ InnerTypeVar::Known(_, _, _) | t @ InnerTypeVar::Array { .. }) => {
                    return Err(Error::TupleIndexOfNonTuple {
                        got: t.clone(),
                        loc: tup.loc(),
                    })
                }
                Ok(InnerTypeVar::Unknown(_)) => {
                    return Err(Error::TupleIndexOfGeneric { loc: tup.loc() })
                }
                Err(e) => return Err(e.clone()),
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
            for expr in members {
                self.visit_expression(expr, symtab)?;
            }

            for (l, r) in members.iter().zip(members.iter().skip(1)) {
                self.unify(l, r, symtab)
                    .map_err(|(expected, got)| Error::ArrayElementMissmatch {
                        got,
                        expected,
                        loc: r.loc(),
                        first_element: members.first().unwrap().loc(),
                    })?.commit(self);
            }

            let inner_type = if members.is_empty() {
                self.new_generic()
            }
            else {
                members[0].get_type(self)?
            };

            let size_type = kvar!(KnownType::Integer(members.len() as u128));
            let result_type = TypeVarRef::array (
                inner_type,
                TypeVarRef::from_owned(size_type, self),
            );

            self.unify_expression_generic_error(expression, result_type.as_ref(), symtab)?.commit(self);
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
            // Visit child nodes
            self.visit_expression(&target, symtab)?;
            self.visit_expression(&index, symtab)?;

            // Add constraints
            let inner_type = self.new_generic();

            // Unify inner type with this expression
            self.unify_expression_generic_error(
                &expression,
                inner_type.as_ref(),
                symtab
            )?.commit(self);

            let int_type = self.new_generic_int(&symtab);
            // self.add_equation(TypedExpression::Id(index.id), int_type.clone());
            self.unify(&index.inner, int_type.as_ref(), symtab)
                .map_err(|(got, _)| {
                    Error::IndexMustBeInteger{got, loc: index.loc()}
                })?.commit(self);

            let array_type = TypeVarRef::array(
                expression.get_type(self)?,
                self.new_generic()
            );
            self.unify(&target.inner, array_type.as_ref(), symtab)
                .map_err(|(got, _)| {
                    Error::IndexeeMustBeArray{got, loc: target.loc()}
                })?.commit(self);
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
            self.unify(&expression.inner, &block.result.inner, symtab)
                // NOTE: We could be more specific about this error specifying
                // that the type of the block must match the return type, though
                // that might just be spammy.
                .map_err(|(expected, got)| Error::UnspecifiedTypeError {
                    expected,
                    got,
                    loc: block.result.loc(),
                })?.commit(self);
        });
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_if(&mut self, expression: &Loc<Expression>, symtab: &SymbolTable) -> Result<()> {
        assuming_kind!(ExprKind::If(cond, on_true, on_false) = &expression => {
            self.visit_expression(&cond, symtab)?;
            self.visit_expression(&on_true, symtab)?;
            self.visit_expression(&on_false, symtab)?;

            self.unify(&cond.inner, &t_bool(symtab), symtab)
                .map_err(|(got, _)| Error::NonBooleanCondition {
                    got,
                    loc: cond.loc(),
                })?.commit(self);
            self.unify(&on_true.inner, &on_false.inner, symtab)
                .map_err(|(expected, got)| Error::IfConditionMismatch {
                    expected,
                    got,
                    first_branch: on_true.loc(),
                    incorrect_branch: on_false.loc(),
                })?.commit(self);
            self.unify(expression, &on_false.inner, symtab)
                .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                    expected,
                    got,
                    loc: expression.loc(),
                })?.commit(self);
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

                self.unify(&cond.inner, pattern, symtab)
                    .map_err(|(expected, got)| {
                        // TODO, Consider introducing a more specific error
                        Error::UnspecifiedTypeError {
                            expected,
                            got,
                            loc: pattern.loc(),
                        }
                    })?.commit(self);

                if i != 0 {
                    self.unify(&branches[0].1, result, symtab).map_err(
                        |(expected, got)| Error::MatchBranchMissmatch {
                            expected,
                            got,
                            first_branch: branches[0].1.loc(),
                            incorrect_branch: result.loc(),
                        },
                    )?.commit(self);
                }
            }

            assert!(
                !branches.is_empty(),
                "Empty match statements should be checked by ast lowering"
            );

            self.unify_expression_generic_error(&branches[0].1, expression, symtab)?.commit(self);
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
                    self.unify_expression_generic_error(&lhs, int_type.as_ref(), symtab)?.commit(self);
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?.commit(self);
                    self.unify_expression_generic_error(expression, &rhs.inner, symtab)?.commit(self)
                }
                BinaryOperator::Eq
                | BinaryOperator::Gt
                | BinaryOperator::Lt
                | BinaryOperator::Ge
                | BinaryOperator::Le => {
                    let int_type = self.new_generic_int(symtab);
                    // TODO: Make generic over types that can be added
                    self.unify_expression_generic_error(&lhs, int_type.as_ref(), symtab)?.commit(self);
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?.commit(self);
                    self.unify_expression_generic_error(expression, &t_bool(symtab), symtab)?.commit(self)
                }
                BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::Xor => {
                    // TODO: Make generic over types that can be ored
                    self.unify_expression_generic_error(&lhs, &t_bool(symtab), symtab)?.commit(self);
                    self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?.commit(self);

                    self.unify_expression_generic_error(expression, &t_bool(symtab), symtab)?.commit(self)
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
                    self.unify_expression_generic_error(operand, int_type.as_ref(), symtab)?.commit(self)
                }
                UnaryOperator::Not => {
                    self.unify_expression_generic_error(operand, &t_bool(symtab), symtab)?.commit(self)
                }
            }
        });
        Ok(())
    }
}
