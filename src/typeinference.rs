use std::collections::HashMap;

use crate::hir::Block;
use crate::hir::Path;
use crate::hir::{Entity, Item};
use crate::hir::{ExprKind, Expression};
use crate::location_info::Loc;
use crate::types::Type;
use crate::{global_symbols::GlobalSymbols, hir::Statement};

#[derive(PartialEq, Debug)]
pub enum TypeVar {
    /// The type is fully known and is the specified type
    Known(Loc<Type>),
    /// The type is completely unknown
    Unknown,
    /// The type is compatible with another typed expression
    Compatible(TypedExpression),
    /// The types are exactly identical
    Equal(TypedExpression),
}

#[derive(Eq, PartialEq, Hash, Debug)]
pub enum TypedExpression {
    Id(u64),
    Name(Path),
}

pub struct TypeState<'a> {
    next_type_id: u64,
    equations: HashMap<TypedExpression, TypeVar>,
    global_symbols: &'a GlobalSymbols,
    next_typeid: u64,
}

impl<'a> TypeState<'a> {
    pub fn new(global_symbols: &'a GlobalSymbols) -> Self {
        Self {
            next_type_id: 0,
            equations: HashMap::new(),
            global_symbols,
            next_typeid: 0,
        }
    }

    /// Visit an item to assign type variables and equations to every subexpression
    /// in the item
    pub fn visit_item(&mut self, item: &Item) {
        match item {
            Item::Entity(e) => self.visit_entity(&e.inner),
        }
    }

    pub fn visit_entity(&mut self, entity: &Entity) {
        // Create equations for all inputs
        for (name, t) in &entity.inputs {
            self.add_equation(
                TypedExpression::Name(name.clone().to_path()),
                TypeVar::Known(t.clone()),
            );
        }

        // Equate the type of the block with the return type of the entity
        self.add_equation(
            TypedExpression::Id(entity.body.inner.id),
            TypeVar::Known(entity.output_type.clone()),
        );
    }

    pub fn visit_expression(&mut self, expression: &Expression) {
        // Add an equation for the value itself
        self.add_unknown(TypedExpression::Id(expression.id));

        // Recurse down the expression
        match &expression.kind {
            ExprKind::Identifier(ident) => {
                let as_type_expr = TypedExpression::Name(ident.inner.clone());
                // Look up the type of the identifier as a sanity check
                if let None = self.equations.get(&as_type_expr) {
                    panic!(
                        "Type variable for {} has not been added but is referenced by expression {:?}",
                        ident.inner,
                        expression
                    );
                }

                self.add_equation(
                    TypedExpression::Id(expression.id),
                    TypeVar::Compatible(as_type_expr),
                );
            }
            ExprKind::IntLiteral(_) => {
                unimplemented! {}
            }
            ExprKind::FnCall(_, _) => {
                unimplemented! {}
            }
            ExprKind::Block(_) => {
                unimplemented! {}
            }
            ExprKind::If(_, _, _) => {
                unimplemented! {}
            }
        }
    }

    pub fn visit_block(&mut self, block: &Block) {
        unimplemented!()
    }

    pub fn visit_statement(&mut self, statement: &Statement) {
        match statement {
            Statement::Binding(name, None, expr) => {
                self.add_equation(
                    TypedExpression::Name(name.clone().to_path()),
                    TypeVar::Equal(TypedExpression::Id(expr.inner.id)),
                );

                self.visit_expression(&expr.inner);
            }
            Statement::Binding(name, Some(t), expr) => {
                self.add_equation(
                    TypedExpression::Name(name.clone().to_path()),
                    TypeVar::Known(t.clone()),
                );
                self.add_equation(
                    TypedExpression::Id(expr.inner.id),
                    TypeVar::Equal(TypedExpression::Name(name.clone().to_path())),
                );

                self.visit_expression(&expr.inner)
            }
            Statement::Register(_) => {
                todo! {}
            }
        }
    }
}

// Private helper functions
impl<'a> TypeState<'a> {
    fn new_typeid(&mut self) -> u64 {
        let result = self.next_typeid;
        self.next_typeid += 1;
        result
    }

    fn add_equation(&mut self, expression: TypedExpression, var: TypeVar) {
        self.equations.insert(expression, var);
    }

    /// Adds an equation for `expression` having an unknown type
    fn add_unknown(&mut self, expression: TypedExpression) {
        let id = self.new_typeid();
        self.equations.insert(expression, TypeVar::Unknown);
    }
}

#[cfg(test)]
impl<'a> TypeState<'a> {
    pub fn get_equations(&self) -> &HashMap<TypedExpression, TypeVar> {
        &self.equations
    }
}

// https://eli.thegreenplace.net/2018/type-inference/

#[cfg(test)]
mod type_equation_generation {
    use super::*;

    use super::TypeVar as TVar;
    use super::TypedExpression as TExpr;

    use crate::{
        hir::Identifier,
        location_info::WithLocation,
        testutil::{hir_ident, hir_path},
    };

    macro_rules! type_eqs {
        ($($eq:expr),*$(,)?) => {
            vec![$($eq),*].into_iter().collect::<HashMap<_, _>>()
        }
    }

    #[test]
    fn identifier_expression_gets_correct_type_equation() {
        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        let ident = Path::from_strs(&["a"]);
        // Pre-add a varialbe for the identifier
        state.add_unknown(TypedExpression::Name(ident.clone()));

        let input = ExprKind::Identifier(ident.clone().nowhere()).with_id(0);
        state.visit_expression(&input);

        let expected = type_eqs![
            (
                TExpr::Id(0),
                TVar::Compatible(TypedExpression::Name(ident.clone()))
            ),
            (TExpr::Name(ident), TVar::Unknown),
        ];

        assert_eq!(state.get_equations(), &expected);
    }

    #[test]
    fn visiting_untyped_bindings_works() {
        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        let lhs = hir_path("a");
        let rhs = hir_path("b");

        state.add_unknown(TypedExpression::Name(rhs.inner.clone()));

        let stmt = Statement::Binding(
            Identifier::Named("a".to_string()).nowhere(),
            None,
            ExprKind::Identifier(rhs.clone()).with_id(0).nowhere(),
        );

        state.visit_statement(&stmt);

        let expected = type_eqs![
            (TExpr::Name(lhs.inner), TVar::Equal(TExpr::Id(0))),
            (
                TExpr::Id(0),
                TypeVar::Compatible(TExpr::Name(rhs.inner.clone()))
            ),
            (TExpr::Name(rhs.inner), TVar::Unknown)
        ];

        assert_eq!(state.get_equations(), &expected);
    }

    #[test]
    fn visiting_typed_bindings_works() {
        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        let lhs = hir_path("a");
        let rhs = hir_path("b");

        state.add_unknown(TypedExpression::Name(rhs.inner.clone()));

        let t = Type::Int(16).nowhere();

        let stmt = Statement::Binding(
            Identifier::Named("a".to_string()).nowhere(),
            Some(t.clone()),
            ExprKind::Identifier(rhs.clone()).with_id(0).nowhere(),
        );

        state.visit_statement(&stmt);

        let expected = type_eqs![
            (TExpr::Name(lhs.inner.clone()), TVar::Known(t)),
            (TExpr::Id(0), TVar::Equal(TExpr::Name(lhs.inner))),
            (
                TExpr::Id(0),
                TypeVar::Compatible(TExpr::Name(rhs.inner.clone()))
            ),
            (TExpr::Name(rhs.inner), TVar::Unknown)
        ];

        assert_eq!(state.get_equations(), &expected);
    }
}
