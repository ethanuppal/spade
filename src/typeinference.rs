use std::collections::HashMap;

use thiserror::Error;

use crate::hir::Block;
use crate::hir::Path;
use crate::hir::{Entity, Item};
use crate::hir::{ExprKind, Expression};
use crate::location_info::Loc;
use crate::types::Type;
use crate::{global_symbols::GlobalSymbols, hir::Statement};

#[derive(Debug, Error, PartialEq, Clone)]
pub enum Error {
    #[error("The specified expression has no type information {}", 0.0)]
    UnknownType(TypedExpression),
}
pub type Result<T> = std::result::Result<T, Error>;

pub type TypeEquations = HashMap<TypedExpression, TypeVar>;

#[derive(PartialEq, Debug, Clone)]
pub enum TypeVar {
    /// The type is known and specified by the user
    Specified(Loc<Type>),
    /// The type is known from the expression
    Known(Type),
    /// The type is completely unknown
    Generic,
}

pub enum Term {
    Variable,
    Function { t: TypeVar, args: Vec<Term> },
}

#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum TypedExpression {
    Id(u64),
    Name(Path),
}

pub struct TypeState<'a> {
    next_type_id: u64,
    equations: TypeEquations,
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

    /// Returns the type of the expression with the specified id. Error if unknown
    pub fn type_of(&self, expr: TypedExpression) -> Result<TypeVar> {
        for (e, t) in &self.equations {
            if e == &expr {
                return Ok(t.clone());
            }
        }
        Err(Error::UnknownType(expr).into())
    }

    /// Visit an item to assign type variables and equations to every subexpression
    /// in the item
    pub fn visit_item(&mut self, item: &Item) {
        match item {
            Item::Entity(e) => self.visit_entity(&e.inner),
        }
    }

    pub fn visit_entity(&mut self, entity: &Entity) {
        unimplemented! {}
    }

    pub fn visit_expression(&mut self, expression: &Expression) {
        // Recurse down the expression
        match &expression.kind {
            ExprKind::Identifier(ident) => {
                unimplemented! {}
            }
            ExprKind::IntLiteral(_) => self.add_equation(
                TypedExpression::Id(expression.id),
                TypeVar::Known(Type::KnownInt),
            ),
            ExprKind::BoolLiteral(_) => {
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
        unimplemented!()
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
}

#[cfg(test)]
impl<'a> TypeState<'a> {
    pub fn get_equations(&self) -> &HashMap<TypedExpression, TypeVar> {
        &self.equations
    }
}

// https://www.youtube.com/watch?v=xJXcZp2vgLs
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

    #[test]
    fn int_literals_have_type_known_int() {
        let symtab = GlobalSymbols::new();
        let mut state = TypeState::new(&symtab);

        let input = ExprKind::IntLiteral(0).with_id(0);

        state.visit_expression(&input);

        assert_eq!(state.type_of(TExpr::Id(0)), Ok(TVar::Known(Type::KnownInt)));
    }

    #[test]
    fn if_statements_have_correctly_infered_types() {
        // let symtab = GlobalSymbols::new();
        // let mut state = TypeState::new(&symtab);

        // let input = ExprKind::If(
        //     Box::new(Expression::ident(0, "a").nowhere()),
        //     Box::new(Expression::ident(1, "b").nowhere()),
        //     Box::new(Expression::ident(2, "c").nowhere())
        // );
        // let input = ExprKind::IntLiteral(0).with_id(0);

        // state.visit_expression(&input);
        //         result: Expression::ident(1, "b").nowhere()
        // assert_eq!(state.type_of(TExpr::Id(0)), Ok(TVar::Known(Type::KnownInt)));
    }

    // #[test]
    // fn identifier_expression_gets_correct_type_equation() {
    //     let symtab = GlobalSymbols::new();
    //     let mut state = TypeState::new(&symtab);

    //     let ident = Path::from_strs(&["a"]);
    //     // Pre-add a varialbe for the identifier
    //     state.add_unknown(TypedExpression::Name(ident.clone()));

    //     let input = ExprKind::Identifier(ident.clone().nowhere()).with_id(0);
    //     state.visit_expression(&input);

    //     let expected = type_eqs![
    //         (
    //             TExpr::Id(0),
    //             TVar::Compatible(TypedExpression::Name(ident.clone()))
    //         ),
    //         (TExpr::Name(ident), TVar::Unknown),
    //     ];

    //     assert_eq!(state.get_equations(), &expected);
    // }

    // #[test]
    // fn visiting_untyped_bindings_works() {
    //     let symtab = GlobalSymbols::new();
    //     let mut state = TypeState::new(&symtab);

    //     let lhs = hir_path("a");
    //     let rhs = hir_path("b");

    //     state.add_unknown(TypedExpression::Name(rhs.inner.clone()));

    //     let stmt = Statement::Binding(
    //         Identifier::Named("a".to_string()).nowhere(),
    //         None,
    //         ExprKind::Identifier(rhs.clone()).with_id(0).nowhere(),
    //     );

    //     state.visit_statement(&stmt);

    //     let expected = type_eqs![
    //         (TExpr::Name(lhs.inner), TVar::Equal(TExpr::Id(0))),
    //         (
    //             TExpr::Id(0),
    //             TypeVar::Compatible(TExpr::Name(rhs.inner.clone()))
    //         ),
    //         (TExpr::Name(rhs.inner), TVar::Unknown)
    //     ];

    //     assert_eq!(state.get_equations(), &expected);
    // }

    // #[test]
    // fn visiting_typed_bindings_works() {
    //     let symtab = GlobalSymbols::new();
    //     let mut state = TypeState::new(&symtab);

    //     let lhs = hir_path("a");
    //     let rhs = hir_path("b");

    //     state.add_unknown(TypedExpression::Name(rhs.inner.clone()));

    //     let t = Type::Int(16).nowhere();

    //     let stmt = Statement::Binding(
    //         Identifier::Named("a".to_string()).nowhere(),
    //         Some(t.clone()),
    //         ExprKind::Identifier(rhs.clone()).with_id(0).nowhere(),
    //     );

    //     state.visit_statement(&stmt);

    //     let expected = type_eqs![
    //         (TExpr::Name(lhs.inner.clone()), TVar::Known(t)),
    //         (TExpr::Id(0), TVar::Equal(TExpr::Name(lhs.inner))),
    //         (
    //             TExpr::Id(0),
    //             TypeVar::Compatible(TExpr::Name(rhs.inner.clone()))
    //         ),
    //         (TExpr::Name(rhs.inner), TVar::Unknown)
    //     ];

    //     assert_eq!(state.get_equations(), &expected);
    // }

    // #[test]
    // fn visiting_register_defintions_works() {
    //     unimplemented! {}
    // }
}

/*
#[cfg(test)]
mod type_equation_solution {
    use super::*;

    use crate::{location_info::WithLocation, testutil::hir_path};

    use super::TypeVar as TVar;
    use super::TypedExpression as TExpr;

    #[test]
    fn binding_with_known_types() {
        let t = Type::Int(16).nowhere();

        let lhs = hir_path("a");
        let rhs = hir_path("b");

        let equations = type_eqs![
            (TExpr::Name(lhs.inner.clone()), TVar::Known(t)),
            (TExpr::Id(0), TVar::Equal(TExpr::Name(lhs.inner.clone()))),
            (
                TExpr::Id(0),
                TypeVar::Compatible(TExpr::Name(rhs.inner.clone()))
            ),
            (TExpr::Name(rhs.inner.clone()), TVar::Unknown)
        ];

        let expected = vec![
            (TExpr::Name(lhs.inner), Type::Int(16)),
            (TExpr::Name(rhs.inner), Type::Int(16))
        ].into_iter().collect::<HashMap<_, _>>();

        let result = solve_type_equations(&equations);

        assert_eq!(result, expected);
    }
}
*/
