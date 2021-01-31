// This algorithm is based off the excelent lecture here
// https://www.youtube.com/watch?v=xJXcZp2vgLs

use std::collections::HashMap;

use colored::*;
use parse_tree_macros::trace_typechecker;

use crate::hir::Statement;
use crate::hir::{ExprKind, Expression};
use crate::{
    fixed_types::{t_bool, t_int},
    hir::{Entity, TypeExpression},
};
use crate::{
    hir::{self, Block},
    location_info::Loc,
};

pub mod equation;
pub mod result;

use equation::{TypeEquations, TypeVar, TypedExpression};
use result::{Error, Result};

use self::{
    equation::{ConcreteType, KnownType},
    result::UnificationError,
};

pub struct TypeState {
    equations: TypeEquations,
    next_typeid: u64,

    pub trace_stack: Vec<TraceStack>,
}

impl TypeState {
    pub fn new() -> Self {
        Self {
            equations: HashMap::new(),
            next_typeid: 0,
            trace_stack: vec![],
        }
    }

    pub fn type_var_from_hir(hir_type: &Loc<crate::hir::Type>) -> TypeVar {
        let (hir_type, loc) = hir_type.clone().split_loc();
        match hir_type {
            hir::Type::Concrete(t) => TypeVar::Known(KnownType::Path(t), vec![], Some(loc)),
            hir::Type::Generic(t, params) => {
                let params = params
                    .iter()
                    .map(|expr| {
                        let (expr, loc) = expr.clone().split_loc();
                        match expr {
                            TypeExpression::Integer(i) => {
                                TypeVar::Known(KnownType::Integer(i), vec![], Some(loc))
                            }
                            TypeExpression::Ident(t) => {
                                TypeVar::Known(KnownType::Path(t), vec![], Some(loc))
                            }
                        }
                    })
                    .collect();

                TypeVar::Known(KnownType::Path(t.inner), params, Some(loc))
            }
            hir::Type::Unit => TypeVar::Known(KnownType::Unit, vec![], Some(loc)),
        }
    }

    /// Returns the type of the expression with the specified id. Error if unknown
    pub fn type_of(&self, expr: &TypedExpression) -> Result<TypeVar> {
        for (e, t) in &self.equations {
            if e == expr {
                return Ok(t.clone());
            }
        }
        Err(Error::UnknownType(expr.clone()).into())
    }

    /// Converts the specified type to a concrete type, returning an error
    /// if it fails
    pub fn ungenerify_type(var: &TypeVar) -> Result<ConcreteType> {
        match var {
            TypeVar::Known(t, params, _) => {
                let params = params
                    .iter()
                    .map(Self::ungenerify_type)
                    .collect::<Result<Vec<_>>>()?;

                Ok(ConcreteType {
                    base: t.clone(),
                    params,
                })
            }
            TypeVar::Generic(_) => Err(Error::GenericTypeInstanciation),
        }
    }

    /// Returns the type of the expression as a concrete type. If the type is not known,
    /// or tye type is Generic, panics
    pub fn expr_type(&self, expr: &Expression) -> ConcreteType {
        Self::ungenerify_type(
            &self
                .type_of(&TypedExpression::Id(expr.id))
                .expect("Expression had no specified type"),
        )
        .expect("Expr had generic type")
    }

    /// Returns the type of the specified name as a concrete type. If the type is not known,
    /// or tye type is Generic, panics
    pub fn type_of_name(&self, name: &hir::Path) -> ConcreteType {
        Self::ungenerify_type(
            &self
                .type_of(&TypedExpression::Name(name.clone()))
                .expect("Expression had no specified type"),
        )
        .expect("Expr had generic type")
    }

    pub fn new_generic_int(&mut self) -> TypeVar {
        TypeVar::Known(t_int(), vec![TypeVar::Generic(self.new_typeid())], None)
    }

    #[trace_typechecker]
    pub fn visit_entity(&mut self, entity: &Entity) -> Result<()> {
        // Add equations for the inputs
        for (name, t) in &entity.head.inputs {
            self.add_equation(
                TypedExpression::Name(name.clone().to_path()),
                Self::type_var_from_hir(t),
            );
        }

        self.visit_expression(&entity.body)?;

        // Ensure that the output type matches what the user specified
        self.unify_types(
            &TypedExpression::Id(entity.body.inner.id),
            &Self::type_var_from_hir(&entity.head.output_type),
        )
        .map_err(|(got, expected)| Error::EntityOutputTypeMissmatch {
            expected,
            got,
            type_spec: entity.head.output_type.loc(),
            output_expr: entity.body.loc(),
        })?;
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_expression(&mut self, expression: &Loc<Expression>) -> Result<()> {
        let new_id = self.new_typeid();
        self.add_equation(
            TypedExpression::Id(expression.inner.id),
            TypeVar::Generic(new_id),
        );
        // Recurse down the expression
        match &expression.inner.kind {
            ExprKind::Identifier(ident) => {
                // Add an equation for the anonymous id
                self.unify_expression_generic_error(
                    &expression,
                    &TypedExpression::Name(ident.inner.clone()),
                )?;
            }
            ExprKind::IntLiteral(_) => {
                let t = self.new_generic_int();
                self.unify_types(&t, &expression.inner)
                    .map_err(|(_, got)| Error::IntLiteralIncompatible {
                        got,
                        loc: expression.loc(),
                    })?;
            }
            ExprKind::BoolLiteral(_) => {
                unimplemented! {}
            }
            ExprKind::FnCall(name, params) => {
                // TODO: Propper error handling
                if let ["intrinsics", operator] = name
                    .inner
                    .maybe_slices()
                    .expect("Anonymous paths are unsupported as functions")
                    .as_slice()
                {
                    let (lhs, rhs) = if let [lhs, rhs] = params.as_slice() {
                        (lhs, rhs)
                    } else {
                        panic!("intrinsics::{} called with more than 2 arguments", operator)
                    };

                    self.visit_expression(&lhs)?;
                    self.visit_expression(&rhs)?;
                    let int_type = self.new_generic_int();
                    // TODO: Make generic over types that can be added
                    self.unify_expression_generic_error(&lhs, &int_type)?;
                    self.unify_expression_generic_error(&lhs, &rhs.inner)?;
                    match *operator {
                        "add" | "sub" => {
                            self.unify_expression_generic_error(expression, &rhs.inner)?
                        }
                        "eq" | "gt" | "lt" => {
                            self.unify_expression_generic_error(expression, &t_bool())?
                        }
                        other => panic!("unrecognised intrinsic {:?}", other),
                    }
                } else {
                    panic!("Unrecognised function {}", name.inner)
                }
            }
            ExprKind::Block(block) => {
                self.visit_block(block)?;

                // Unify the return type of the block with the type of this expression
                self.unify_types(&expression.inner, &block.result.inner)
                    // NOTE: We could be more specific about this error specifying
                    // that the type of the block must match the return type, though
                    // that might just be spammy.
                    .map_err(|(expected, got)| Error::UnspecifiedTypeError {
                        expected,
                        got,
                        loc: block.result.loc(),
                    })?;
            }
            ExprKind::If(cond, on_true, on_false) => {
                self.visit_expression(&cond)?;
                self.visit_expression(&on_true)?;
                self.visit_expression(&on_false)?;

                self.unify_types(&cond.inner, &t_bool())
                    .map_err(|(got, _)| Error::NonBooleanCondition {
                        got,
                        loc: cond.loc(),
                    })?;
                self.unify_types(&on_true.inner, &on_false.inner)
                    .map_err(|(expected, got)| Error::IfConditionMissmatch {
                        expected,
                        got,
                        first_branch: on_true.loc(),
                        incorrect_branch: on_false.loc(),
                    })?;
                self.unify_types(expression, &on_false.inner)
                    .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                        expected,
                        got,
                        loc: expression.loc(),
                    })?;
            }
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_block(&mut self, block: &Block) -> Result<()> {
        if !block.statements.is_empty() {
            todo!("Blocks with statements are currently not type checked")
        }
        self.visit_expression(&block.result)
    }

    pub fn visit_statement(&mut self, _statement: &Statement) {
        unimplemented!()
    }
}

// Private helper functions
impl<'a> TypeState {
    fn new_typeid(&mut self) -> u64 {
        let result = self.next_typeid;
        self.next_typeid += 1;
        result
    }

    fn add_equation(&mut self, expression: TypedExpression, var: TypeVar) {
        self.trace_stack
            .push(TraceStack::AddingEquation(expression.clone(), var.clone()));
        self.equations.insert(expression, var);
    }

    fn unify_types(
        &mut self,
        e1: &impl HasType,
        e2: &impl HasType,
    ) -> std::result::Result<(), UnificationError> {
        let v1 = e1
            .get_type(self)
            .expect("Tried to unify types but the lhs was not found");
        let v2 = e2
            .get_type(self)
            .expect("Tried to unify types but the rhs was not found");

        // Used because we want to avoid borrowchecker errors when we add stuff to the
        // trace
        let v1cpy = v1.clone();
        let v2cpy = v2.clone();
        // Figure out the most general type, and take note if we need to
        // do any replacement of the types in the rest of the state
        let (new_type, replaced_type) = match (&v1, &v2) {
            (TypeVar::Known(t1, p1, _), TypeVar::Known(t2, p2, _)) => {
                if p1.len() != p2.len() {
                    return Err((v1.clone(), v2.clone()));
                }

                for (t1, t2) in p1.iter().zip(p2.iter()) {
                    self.unify_types(t1, t2)?
                }

                if t1 == t2 {
                    Ok((v1, None))
                } else {
                    Err((v1.clone(), v2.clone()))
                }
            }
            (TypeVar::Known(_, _, _), TypeVar::Generic(_)) => Ok((v1, Some(v2))),
            (TypeVar::Generic(_), TypeVar::Known(_, _, _)) => Ok((v2, Some(v1))),
            (TypeVar::Generic(_), TypeVar::Generic(_)) => Ok((v1, Some(v2))),
        }?;

        if let Some(replaced_type) = replaced_type {
            for (_, rhs) in &mut self.equations {
                if *rhs == replaced_type {
                    *rhs = new_type.clone()
                }

                // If there are type parameters, replace things there too
                match rhs {
                    TypeVar::Known(_, params, _) => {
                        params.iter_mut().for_each(|p| {
                            if *p == replaced_type {
                                *p = new_type.clone()
                            }
                        });
                    }
                    TypeVar::Generic(_) => {}
                }
            }
        }

        self.trace_stack
            .push(TraceStack::Unified(v1cpy, v2cpy, new_type.clone()));
        Ok(())
    }

    fn unify_expression_generic_error(
        &mut self,
        expr: &Loc<Expression>,
        other: &impl HasType,
    ) -> Result<()> {
        self.unify_types(&expr.inner, other)
            .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                got,
                expected,
                loc: expr.loc(),
            })
    }
}

#[cfg(test)]
impl TypeState {
    pub fn print_equations(&self) {
        for (lhs, rhs) in &self.equations {
            println!("{}: {}", lhs, rhs);
        }
    }
}

pub trait HasType {
    fn get_type<'a>(&self, state: &TypeState) -> Result<TypeVar>;
}

impl HasType for TypeVar {
    fn get_type<'a>(&self, _: &TypeState) -> Result<TypeVar> {
        Ok(self.clone())
    }
}
impl HasType for Loc<TypeVar> {
    fn get_type<'a>(&self, _: &TypeState) -> Result<TypeVar> {
        Ok(self.inner.clone())
    }
}
impl HasType for TypedExpression {
    fn get_type<'a>(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(self)
    }
}
impl HasType for Expression {
    fn get_type<'a>(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.id))
    }
}
impl HasType for Loc<Expression> {
    fn get_type<'a>(&self, state: &TypeState) -> Result<TypeVar> {
        state.type_of(&TypedExpression::Id(self.inner.id))
    }
}
impl HasType for KnownType {
    fn get_type<'a>(&self, _state: &TypeState) -> Result<TypeVar> {
        Ok(TypeVar::Known(self.clone(), vec![], None))
    }
}

pub enum TraceStack {
    /// Entering the specified visitor
    Enter(String),
    /// Exited the most recent visitor and the node had the specified type
    Exit,
    /// Unified .0 with .1 producing .2
    Unified(TypeVar, TypeVar, TypeVar),
    AddingEquation(TypedExpression, TypeVar),
}

pub fn format_trace_stack(stack: &[TraceStack]) -> String {
    let mut result = String::new();
    let mut indent_amount = 0;

    for entry in stack {
        let mut next_indent_amount = indent_amount;
        let message = match entry {
            TraceStack::Enter(function) => {
                next_indent_amount += 1;
                format!("{} `{}`", "visiting".white(), function.blue())
            }
            TraceStack::AddingEquation(expr, t) => {
                format!("{} {:?} <- {:?}", "eq".yellow(), expr, t)
            }
            TraceStack::Unified(lhs, rhs, result) => {
                format!("{} {}, {} -> {}", "unified".green(), lhs, rhs, result)
            }
            TraceStack::Exit => {
                next_indent_amount -= 1;
                format!("")
            }
        };
        if let TraceStack::Exit = entry {
        } else {
            for _ in 0..indent_amount {
                result += "| ";
            }
            result += &message;
            result += "\n";
        }
        indent_amount = next_indent_amount;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    use super::TypeVar as TVar;
    use super::TypedExpression as TExpr;

    use crate::{
        assert_matches,
        fixed_types::{t_clock, INT_PATH},
        hir::{Block, Identifier, Path},
    };
    use crate::{hir::EntityHead, location_info::WithLocation};

    fn sized_int(size: u128) -> TVar {
        TVar::Known(
            t_int(),
            vec![TVar::Known(KnownType::Integer(size), vec![], None)],
            None,
        )
    }

    fn unsized_int(id: u64) -> TVar {
        TVar::Known(t_int(), vec![TVar::Generic(id)], None)
    }

    macro_rules! get_type {
        ($state:ident, $e:expr) => {
            if let Ok(t) = $state.type_of($e) {
                t
            } else {
                println!("{}", format_trace_stack(&$state.trace_stack));
                panic!("Failed to get type of {:?}", $e)
            }
        };
    }

    macro_rules! ensure_same_type {
        ($state:ident, $t1:expr, $t2:expr) => {
            let _t1 = $t1.get_type(&$state);
            let _t2 = $t2.get_type(&$state);
            if _t1 != _t2 {
                println!("{}", format_trace_stack(&$state.trace_stack));
                $state.print_equations();

                if let (Ok(t1), Ok(t2)) = (&_t1, &_t2) {
                    println!("Types were OK and have values {}, {}", t1, t2);
                    println!("Raw: {:?}, {:?}", t1, t2);
                } else {
                    println!("{:?}\n!=\n{:?}", _t1, _t2);
                }
                panic!("Types are not the same")
            }
        };
    }

    #[test]
    fn int_literals_have_type_known_int() {
        let mut state = TypeState::new();

        let input = ExprKind::IntLiteral(0).with_id(0).nowhere();

        state.visit_expression(&input).expect("Type error");

        assert_eq!(state.type_of(&TExpr::Id(0)), Ok(unsized_int(1)));
    }

    #[test]
    fn if_statements_have_correctly_infered_types() {
        let mut state = TypeState::new();

        let input = ExprKind::If(
            Box::new(Expression::ident(0, "a").nowhere()),
            Box::new(Expression::ident(1, "b").nowhere()),
            Box::new(Expression::ident(2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(Path::from_strs(&["a"]));
        let expr_b = TExpr::Name(Path::from_strs(&["b"]));
        let expr_c = TExpr::Name(Path::from_strs(&["c"]));
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), TVar::Generic(101));
        state.add_equation(expr_c.clone(), TVar::Generic(102));

        state.visit_expression(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(), vec![], None));
        ensure_same_type!(state, t1, t2);
        ensure_same_type!(state, t1, t3);

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn if_statements_get_correct_type_when_branches_are_of_known_type() {
        let mut state = TypeState::new();

        let input = ExprKind::If(
            Box::new(Expression::ident(0, "a").nowhere()),
            Box::new(Expression::ident(1, "b").nowhere()),
            Box::new(Expression::ident(2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(Path::from_strs(&["a"]));
        let expr_b = TExpr::Name(Path::from_strs(&["b"]));
        let expr_c = TExpr::Name(Path::from_strs(&["c"]));
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), unsized_int(101));
        state.add_equation(expr_c.clone(), TVar::Generic(102));

        state.visit_expression(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(), vec![], None));
        ensure_same_type!(state, t1, unsized_int(101));
        ensure_same_type!(state, t2, unsized_int(101));
        ensure_same_type!(state, t3, unsized_int(101));

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn type_inference_fails_if_if_branches_have_incompatible_types() {
        let mut state = TypeState::new();

        let input = ExprKind::If(
            Box::new(Expression::ident(0, "a").nowhere()),
            Box::new(Expression::ident(1, "b").nowhere()),
            Box::new(Expression::ident(2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(Path::from_strs(&["a"]));
        let expr_b = TExpr::Name(Path::from_strs(&["b"]));
        let expr_c = TExpr::Name(Path::from_strs(&["c"]));
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), unsized_int(101));
        state.add_equation(expr_c.clone(), TVar::Known(t_clock(), vec![], None));

        assert_ne!(state.visit_expression(&input), Ok(()));
    }

    #[test]
    fn type_inference_for_entities_works() {
        let input = Entity {
            name: Identifier::Named("test".to_string()).nowhere(),
            head: EntityHead {
                inputs: vec![(
                    Identifier::Named("input".to_string()).nowhere(),
                    hir::Type::Generic(
                        Path::from_strs(INT_PATH).nowhere(),
                        vec![hir::TypeExpression::Integer(5).nowhere()],
                    )
                    .nowhere(),
                )],
                output_type: hir::Type::Generic(
                    Path::from_strs(INT_PATH).nowhere(),
                    vec![hir::TypeExpression::Integer(5).nowhere()],
                )
                .nowhere(),
                type_params: vec![],
            },
            body: ExprKind::Identifier(Path::from_strs(&["input"]).nowhere())
                .with_id(0)
                .nowhere(),
        };

        let mut state = TypeState::new();

        state.visit_entity(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        ensure_same_type!(
            state,
            t0,
            TypeVar::Known(
                t_int(),
                vec![TypeVar::Known(KnownType::Integer(5), vec![], None)],
                None
            )
        );
    }

    #[test]
    fn entity_return_types_must_match() {
        let input = Entity {
            name: Identifier::Named("test".to_string()).nowhere(),
            head: EntityHead {
                inputs: vec![(
                    Identifier::Named("input".to_string()).nowhere(),
                    hir::Type::Generic(
                        Path::from_strs(&["int"]).nowhere(),
                        vec![hir::TypeExpression::Integer(5).nowhere()],
                    )
                    .nowhere(),
                )],
                output_type: hir::Type::Concrete(Path::from_strs(&["bool"])).nowhere(),
                type_params: vec![],
            },
            body: ExprKind::Identifier(Path::from_strs(&["input"]).nowhere())
                .with_id(0)
                .nowhere(),
        };

        let mut state = TypeState::new();

        assert_matches!(
            state.visit_entity(&input),
            Err(Error::EntityOutputTypeMissmatch { .. })
        );
    }

    #[test]
    fn block_visiting_without_definitions_works() {
        let input = ExprKind::Block(Box::new(Block {
            statements: vec![],
            result: ExprKind::IntLiteral(5).with_id(0).nowhere(),
        }))
        .with_id(1)
        .nowhere();

        let mut state = TypeState::new();

        state.visit_expression(&input).unwrap();

        ensure_same_type!(state, TExpr::Id(0), unsized_int(2));
        ensure_same_type!(state, TExpr::Id(1), unsized_int(2));
    }

    #[test]
    fn integer_literals_are_compatible_with_fixed_size_ints() {
        let mut state = TypeState::new();

        let input = ExprKind::If(
            Box::new(Expression::ident(0, "a").nowhere()),
            Box::new(Expression::ident(1, "b").nowhere()),
            Box::new(Expression::ident(2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(Path::from_strs(&["a"]));
        let expr_b = TExpr::Name(Path::from_strs(&["b"]));
        let expr_c = TExpr::Name(Path::from_strs(&["c"]));
        state.add_equation(expr_a.clone(), TVar::Generic(100));
        state.add_equation(expr_b.clone(), unsized_int(101));
        state.add_equation(expr_c.clone(), sized_int(5));

        state.visit_expression(&input).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(), vec![], None));
        ensure_same_type!(state, t1, sized_int(5));
        ensure_same_type!(state, t2, sized_int(5));
        ensure_same_type!(state, t3, sized_int(5));

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }
}
