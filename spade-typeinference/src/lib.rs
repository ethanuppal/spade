// This algorithm is based off the excelent lecture here
// https://www.youtube.com/watch?v=xJXcZp2vgLs

use hir::symbol_table::TypeSymbol;
use hir::{Argument, ParameterList};
use hir::{ExecutableItem, ItemList};
use parse_tree_macros::trace_typechecker;
use spade_common::location_info::Loc;
use spade_hir as hir;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::{
    expression::BinaryOperator, Block, Entity, ExprKind, Expression, Register, Statement,
};
use spade_types::KnownType;
use std::collections::HashMap;

use colored::*;

pub mod equation;
pub mod error_reporting;
pub mod fixed_types;
pub mod mir_type_lowering;
pub mod pipeline;
pub mod result;
pub mod testutil;

use crate::fixed_types::t_clock;
use crate::fixed_types::{t_bool, t_int};

use equation::{TypeEquations, TypeVar, TypedExpression};
use result::{Error, Result};

use self::result::{UnificationError, UnificationErrorExt, UnificationTrace};

pub struct ProcessedEntity {
    pub entity: Entity,
    pub type_state: TypeState,
}

pub struct ProcessedPipeline {
    pub pipeline: hir::Pipeline,
    pub type_state: TypeState,
}

pub enum ProcessedItem {
    EnumInstance,
    Entity(ProcessedEntity),
    Pipeline(ProcessedPipeline),
}

pub struct ProcessedItemList {
    pub executables: Vec<ProcessedItem>,
}

impl ProcessedItemList {
    pub fn typecheck(
        items: &ItemList,
        symbol_table: &SymbolTable,
        print_trace: bool,
    ) -> Result<Self> {
        Ok(Self {
            executables: items
                .executables
                .clone()
                .into_iter()
                .map(|(_name, item)| {
                    let mut type_state = TypeState::new();

                    // To avoid borrowing type_state too early, we'll do a macro to build
                    // closures. Kind of ugly, but it gets the job done
                    macro_rules! err_processor {
                        () => {
                            |e| {
                                if print_trace {
                                    println!("{}", format_trace_stack(&type_state.trace_stack))
                                }
                                e
                            }
                        };
                    }

                    match item {
                        ExecutableItem::EnumInstance { .. } => Ok(ProcessedItem::EnumInstance),
                        ExecutableItem::Entity(entity) => {
                            type_state
                                .visit_entity(&entity, symbol_table)
                                .map_err(err_processor!())?;
                            Ok(ProcessedItem::Entity(ProcessedEntity {
                                entity: entity.inner,
                                type_state,
                            }))
                        }
                        ExecutableItem::Pipeline(pipeline) => {
                            type_state
                                .visit_pipeline(&pipeline, symbol_table)
                                .map_err(err_processor!())?;
                            Ok(ProcessedItem::Pipeline(ProcessedPipeline {
                                pipeline: pipeline.inner,
                                type_state,
                            }))
                        }
                    }
                })
                .collect::<Result<Vec<_>>>()?,
        })
    }
}

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

    pub fn hir_type_expr_to_var(e: &hir::TypeExpression) -> TypeVar {
        match e {
            hir::TypeExpression::Integer(i) => TypeVar::Known(KnownType::Integer(*i), vec![], None),
            hir::TypeExpression::TypeSpec(spec) => Self::type_var_from_hir(spec),
        }
    }

    pub fn type_var_from_hir(hir_type: &crate::hir::TypeSpec) -> TypeVar {
        match hir_type {
            hir::TypeSpec::Declared(base, params) => {
                let params = params
                    .into_iter()
                    .map(|e| Self::hir_type_expr_to_var(e))
                    .collect();

                TypeVar::Known(KnownType::Type(base.inner.clone()), params, None)
            }
            hir::TypeSpec::Generic(name) => {
                // NOTE: Should we care about this being generic here?
                TypeVar::Known(KnownType::Type(name.inner.clone()), vec![], None)
            }
            hir::TypeSpec::Tuple(inner) => {
                let inner = inner.iter().map(|t| Self::type_var_from_hir(t)).collect();
                TypeVar::Tuple(inner)
            }
            hir::TypeSpec::Unit(_) => {
                todo!("Support unit type in type inference")
            }
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

    pub fn new_generic_int(&mut self, symtab: &SymbolTable) -> TypeVar {
        TypeVar::Known(t_int(symtab), vec![self.new_generic()], None)
    }

    fn new_generic(&mut self) -> TypeVar {
        let id = self.new_typeid();
        TypeVar::Unknown(id)
    }

    #[trace_typechecker]
    pub fn visit_entity(&mut self, entity: &Entity, symtab: &SymbolTable) -> Result<()> {
        // Add equations for the inputs
        for (name, t) in &entity.inputs {
            self.add_equation(
                TypedExpression::Name(name.clone()),
                Self::type_var_from_hir(t),
            );
        }

        self.visit_expression(&entity.body, symtab)?;

        // Ensure that the output type matches what the user specified, and unit otherwise
        if let Some(output_type) = &entity.head.output_type {
            self.unify_types(
                &TypedExpression::Id(entity.body.inner.id),
                &Self::type_var_from_hir(&output_type),
                symtab,
            )
            .map_err(|(got, expected)| Error::EntityOutputTypeMismatch {
                expected,
                got,
                type_spec: output_type.loc(),
                output_expr: entity.body.loc(),
            })?;
        } else {
            todo!("Support unit types")
            // self.unify_types(
            //     &TypedExpression::Id(entity.body.inner.id),
            //     &TypeVar::Known(KnownType::Type(BaseType::Unit), vec![], None),
            // )
            // .map_err(|(got, expected)| Error::UnspecedEntityOutputTypeMismatch {
            //     expected,
            //     got,
            //     output_expr: entity.body.loc(),
            // })?;
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_argument_list(
        &mut self,
        args: &[Argument],
        params: &ParameterList,
        symtab: &SymbolTable,
    ) -> Result<()> {
        for (
            i,
            Argument {
                target,
                value,
                kind,
            },
        ) in args.iter().enumerate()
        {
            let target_type = Self::type_var_from_hir(&params.arg_type(&target));
            self.visit_expression(&value, symtab)?;

            self.unify_types(&target_type, value, symtab).map_err(
                |(expected, got)| match kind {
                    hir::ArgumentKind::Positional => Error::PositionalArgumentMismatch {
                        index: i,
                        expr: value.loc(),
                        expected,
                        got,
                    },
                    hir::ArgumentKind::Named => Error::NamedArgumentMismatch {
                        name: target.clone(),
                        expr: value.loc(),
                        expected,
                        got,
                    },
                    hir::ArgumentKind::ShortNamed => Error::ShortNamedArgumentMismatch {
                        name: target.clone(),
                        expected,
                        got,
                    },
                },
            )?;
        }

        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_expression(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
    ) -> Result<()> {
        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Id(expression.inner.id), new_type);
        // Recurse down the expression
        match &expression.inner.kind {
            ExprKind::Identifier(ident) => {
                // Add an equation for the anonymous id
                self.unify_expression_generic_error(
                    &expression,
                    &TypedExpression::Name(ident.clone()),
                    symtab,
                )?;
            }
            ExprKind::IntLiteral(_) => {
                let t = self.new_generic_int(symtab);
                self.unify_types(&t, &expression.inner, symtab)
                    .map_err(|(_, got)| Error::IntLiteralIncompatible {
                        got,
                        loc: expression.loc(),
                    })?;
            }
            ExprKind::BoolLiteral(_) => {
                self.unify_expression_generic_error(&expression, &t_bool(symtab), symtab)?;
            }
            ExprKind::TupleLiteral(inner) => {
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
            }
            ExprKind::TupleIndex(tup, index) => {
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
                    Ok(t @ TypeVar::Known(_, _, _)) => {
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
            }
            ExprKind::Block(block) => {
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
            }
            ExprKind::If(cond, on_true, on_false) => {
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
            }
            ExprKind::BinaryOperator(lhs, op, rhs) => {
                self.visit_expression(&lhs, symtab)?;
                self.visit_expression(&rhs, symtab)?;
                match *op {
                    BinaryOperator::Add
                    | BinaryOperator::Sub
                    | BinaryOperator::Mul
                    | BinaryOperator::LeftShift
                    | BinaryOperator::RightShift => {
                        let int_type = self.new_generic_int(symtab);
                        // TODO: Make generic over types that can be added
                        self.unify_expression_generic_error(&lhs, &int_type, symtab)?;
                        self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;
                        self.unify_expression_generic_error(expression, &rhs.inner, symtab)?
                    }
                    BinaryOperator::Eq | BinaryOperator::Gt | BinaryOperator::Lt => {
                        let int_type = self.new_generic_int(symtab);
                        // TODO: Make generic over types that can be added
                        self.unify_expression_generic_error(&lhs, &int_type, symtab)?;
                        self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;
                        self.unify_expression_generic_error(expression, &t_bool(symtab), symtab)?
                    }
                    BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr => {
                        // TODO: Make generic over types that can be ored
                        self.unify_expression_generic_error(&lhs, &t_bool(symtab), symtab)?;
                        self.unify_expression_generic_error(&lhs, &rhs.inner, symtab)?;

                        self.unify_expression_generic_error(expression, &t_bool(symtab), symtab)?
                    }
                }
            }
            ExprKind::EntityInstance(name, args) => {
                let head = symtab.entity_by_id(&name.inner);
                // Unify the types of the arguments
                self.visit_argument_list(args, &head.inputs, symtab)?;

                let return_type = Self::type_var_from_hir(
                    &head
                        .output_type
                        .as_ref()
                        .expect("Unit return type from entity is unsupported"),
                );
                self.unify_expression_generic_error(expression, &return_type, symtab)?;
            }
            ExprKind::PipelineInstance {
                depth: _,
                name,
                args,
            } => {
                let head = symtab.pipeline_by_id(&name.inner);
                // Unify the types of the arguments
                self.visit_argument_list(args, &head.inputs, symtab)?;

                let return_type = Self::type_var_from_hir(
                    &head
                        .output_type
                        .as_ref()
                        .expect("Unit return type from entity is unsupported"),
                );
                self.unify_expression_generic_error(expression, &return_type, symtab)?;
            }
            ExprKind::FnCall(name, args) => {
                let head = symtab.function_by_id(&name.inner);
                // Unify the types of the arguments
                self.visit_argument_list(args, &head.inputs, symtab)?;

                let return_type = Self::type_var_from_hir(
                    &head
                        .output_type
                        .as_ref()
                        .expect("Unit return type from entity is unsupported"),
                );
                self.unify_expression_generic_error(expression, &return_type, symtab)?;
            }
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_block(&mut self, block: &Block, symtab: &SymbolTable) -> Result<()> {
        for statement in &block.statements {
            self.visit_statement(statement, symtab)?
        }
        self.visit_expression(&block.result, symtab)
    }

    #[trace_typechecker]
    pub fn visit_statement(&mut self, stmt: &Loc<Statement>, symtab: &SymbolTable) -> Result<()> {
        match &stmt.inner {
            Statement::Binding(pattern, t, value) => {
                self.visit_expression(value, symtab)?;

                if t.is_some() {
                    todo!("Let bindings with fixed types are unsupported")
                }

                let new_type = self.new_generic();
                match &pattern.inner {
                    hir::Pattern::Integer(_) => todo!(),
                    hir::Pattern::Bool(_) => todo!(),
                    hir::Pattern::Name(name) => {
                        self.add_equation(TypedExpression::Name(name.clone().inner), new_type);

                        self.unify_expression_generic_error(
                            &value,
                            &TypedExpression::Name(name.clone().inner),
                            symtab,
                        )?;
                    }
                    hir::Pattern::Tuple(_) => todo!(),
                    hir::Pattern::Type(_, _) => todo!(),
                }

                Ok(())
            }
            Statement::Register(reg) => self.visit_register(reg, symtab),
        }
    }

    #[trace_typechecker]
    pub fn visit_register(&mut self, reg: &Register, symtab: &SymbolTable) -> Result<()> {
        let new_type = self.new_generic();
        let name = match &reg.pattern.inner {
            hir::Pattern::Integer(_) => todo!(),
            hir::Pattern::Bool(_) => todo!(),
            hir::Pattern::Name(name) => {
                self.add_equation(TypedExpression::Name(name.clone().inner), new_type);

                if let Some(t) = &reg.value_type {
                    self.unify_types(
                        &TypedExpression::Name(name.inner.clone()),
                        &Self::type_var_from_hir(&t),
                        symtab,
                    )
                    .map_err(|(got, expected)| {
                        Error::UnspecifiedTypeError {
                            expected,
                            got,
                            loc: name.loc(),
                        }
                    })?;
                }
                name
            }
            hir::Pattern::Tuple(_) => todo!(),
            hir::Pattern::Type(_, _) => todo!(),
        };

        self.visit_expression(&reg.clock, symtab)?;
        self.visit_expression(&reg.value, symtab)?;

        if let Some((rst_cond, rst_value)) = &reg.reset {
            self.visit_expression(&rst_cond, symtab)?;
            self.visit_expression(&rst_value, symtab)?;
            // Ensure cond is a boolean
            self.unify_types(&rst_cond.inner, &t_bool(symtab), symtab)
                .map_err(|(got, expected)| Error::NonBoolReset {
                    expected,
                    got,
                    loc: rst_cond.loc(),
                })?;

            // Ensure the reset value has the same type as the register itself
            self.unify_types(&rst_value.inner, &reg.value.inner, symtab)
                .map_err(|(got, expected)| Error::RegisterResetMismatch {
                    expected,
                    got,
                    loc: rst_cond.loc(),
                })?;
        }

        self.unify_types(&reg.clock, &t_clock(symtab), symtab)
            .map_err(|(got, expected)| Error::NonClockClock {
                expected,
                got,
                loc: reg.clock.loc(),
            })?;

        self.unify_expression_generic_error(
            &reg.value,
            &TypedExpression::Name(name.clone().inner),
            symtab,
        )?;

        Ok(())
    }
}

// Private helper functions
impl TypeState {
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
        symtab: &SymbolTable,
    ) -> std::result::Result<(), UnificationError> {
        let v1 = e1
            .get_type(self)
            .expect("Tried to unify types but the lhs was not found");
        let v2 = e2
            .get_type(self)
            .expect("Tried to unify types but the rhs was not found");

        self.trace_stack
            .push(TraceStack::TryingUnify(v1.clone(), v2.clone()));

        // Used because we want to avoid borrowchecker errors when we add stuff to the
        // trace
        let v1cpy = v1.clone();
        let v2cpy = v2.clone();

        let err_producer = || {
            (
                UnificationTrace::new(v1.clone()),
                UnificationTrace::new(v2.clone()),
            )
        };
        macro_rules! unify_if {
            ($condition:expr, $new_type:expr, $replaced_type:expr) => {
                if $condition {
                    Ok(($new_type, $replaced_type))
                } else {
                    Err(err_producer())
                }
            };
        }

        // Figure out the most general type, and take note if we need to
        // do any replacement of the types in the rest of the state
        let (new_type, replaced_type) = match (&v1, &v2) {
            (TypeVar::Known(t1, p1, _), TypeVar::Known(t2, p2, _)) => match (t1, t2) {
                (KnownType::Integer(val1), KnownType::Integer(val2)) => {
                    unify_if!(val1 == val2, v1, None)
                }
                (KnownType::Type(n1), KnownType::Type(n2)) => {
                    match (
                        &symtab.type_symbol_by_id(n1).inner,
                        &symtab.type_symbol_by_id(n2).inner,
                    ) {
                        (TypeSymbol::Declared(ts1), TypeSymbol::Declared(ts2)) => {
                            if p1.len() != p2.len() {
                                return Err(err_producer());
                            }

                            for (t1, t2) in p1.iter().zip(p2.iter()) {
                                self.unify_types(t1, t2, symtab)
                                    .add_context(v1.clone(), v2.clone())?
                            }

                            unify_if!(ts1 == ts2, v1, None)
                        }
                        (TypeSymbol::Declared(_), TypeSymbol::GenericArg) => Ok((v1, Some(v2))),
                        (TypeSymbol::GenericArg, TypeSymbol::Declared(_)) => Ok((v2, Some(v1))),
                        (TypeSymbol::GenericArg, TypeSymbol::GenericArg) => Ok((v1, Some(v2))),
                        (TypeSymbol::Declared(_), TypeSymbol::GenericInt) => todo!(),
                        (TypeSymbol::GenericArg, TypeSymbol::GenericInt) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::Declared(_)) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::GenericArg) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::GenericInt) => todo!(),
                    }
                }
                (KnownType::Integer(_), KnownType::Type(_)) => Err(err_producer()),
                (KnownType::Type(_), KnownType::Integer(_)) => Err(err_producer()),
            },
            (TypeVar::Tuple(i1), TypeVar::Tuple(i2)) => {
                if i1.len() != i2.len() {
                    return Err(err_producer());
                }

                for (t1, t2) in i1.iter().zip(i2.iter()) {
                    self.unify_types(t1, t2, symtab)
                        .add_context(v1.clone(), v2.clone())?
                }

                Ok((v1, None))
            }
            (TypeVar::Known(_, _, _), TypeVar::Tuple(_)) => Err(err_producer()),
            (TypeVar::Tuple(_), TypeVar::Known(_, _, _)) => Err(err_producer()),
            (TypeVar::Unknown(_), TypeVar::Unknown(_)) => Ok((v1, Some(v2))),
            (_other, TypeVar::Unknown(_)) => Ok((v1, Some(v2))),
            (TypeVar::Unknown(_), _other) => Ok((v2, Some(v1))),
        }?;

        if let Some(replaced_type) = replaced_type {
            for (_, rhs) in &mut self.equations {
                Self::replace_type_var(rhs, &replaced_type, new_type.clone())
            }
        }

        self.trace_stack
            .push(TraceStack::Unified(v1cpy, v2cpy, new_type.clone()));
        Ok(())
    }

    fn replace_type_var(in_var: &mut TypeVar, from: &TypeVar, replacement: TypeVar) {
        // First, do recursive replacement
        match in_var {
            TypeVar::Known(_, params, _) => {
                for param in params {
                    Self::replace_type_var(param, from, replacement.clone())
                }
            }
            TypeVar::Tuple(inner) => {
                for t in inner {
                    Self::replace_type_var(t, from, replacement.clone())
                }
            }
            TypeVar::Unknown(_) => {}
        }

        if in_var == from {
            *in_var = replacement;
        }
    }

    fn unify_expression_generic_error(
        &mut self,
        expr: &Loc<Expression>,
        other: &impl HasType,
        symtab: &SymbolTable,
    ) -> Result<()> {
        self.unify_types(&expr.inner, other, symtab)
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

pub trait HasType: std::fmt::Debug {
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
    TryingUnify(TypeVar, TypeVar),
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
            TraceStack::TryingUnify(lhs, rhs) => {
                format!("{} of {} with {}", "trying unification".cyan(), lhs, rhs)
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

    use crate::testutil::{sized_int, unsized_int};
    use crate::{ensure_same_type, get_type};
    use crate::{
        fixed_types::t_clock,
        hir::{self, Block},
    };
    use hir::Pattern;
    use hir::{dtype, testutil::t_num, Argument};
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;
    use spade_hir::symbol_table::{SymbolTable, Thing};

    #[test]
    fn int_literals_have_type_known_int() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::IntLiteral(0).with_id(0).nowhere();

        state.visit_expression(&input, &symtab).expect("Type error");

        assert_eq!(state.type_of(&TExpr::Id(0)), Ok(unsized_int(1, &symtab)));
    }

    #[test]
    fn if_statements_have_correctly_infered_types() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::If(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            Box::new(Expression::ident(1, 1, "b").nowhere()),
            Box::new(Expression::ident(2, 2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_equation(expr_a.clone(), TVar::Unknown(100));
        state.add_equation(expr_b.clone(), TVar::Unknown(101));
        state.add_equation(expr_c.clone(), TVar::Unknown(102));

        state.visit_expression(&input, &symtab).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(&symtab), vec![], None));
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
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::If(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            Box::new(Expression::ident(1, 1, "b").nowhere()),
            Box::new(Expression::ident(2, 2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_equation(expr_a.clone(), TVar::Unknown(100));
        state.add_equation(expr_b.clone(), unsized_int(101, &symtab));
        state.add_equation(expr_c.clone(), TVar::Unknown(102));

        state.visit_expression(&input, &symtab).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(&symtab), vec![], None));
        ensure_same_type!(state, t1, unsized_int(101, &symtab));
        ensure_same_type!(state, t2, unsized_int(101, &symtab));
        ensure_same_type!(state, t3, unsized_int(101, &symtab));

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn type_inference_fails_if_if_branches_have_incompatible_types() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::If(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            Box::new(Expression::ident(1, 1, "b").nowhere()),
            Box::new(Expression::ident(2, 2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_equation(expr_a.clone(), TVar::Unknown(100));
        state.add_equation(expr_b.clone(), unsized_int(101, &symtab));
        state.add_equation(expr_c.clone(), TVar::Known(t_clock(&symtab), vec![], None));

        assert_ne!(state.visit_expression(&input, &symtab), Ok(()));
    }

    #[ignore]
    #[test]
    fn type_inference_for_entities_works() {
        todo!("Figure out how we handle built in types and name_ids");
        // let input = Entity {
        //     head: EntityHead {
        //         inputs: vec![(
        //             name_id(0, "input"),
        //             hir::Type::Generic(
        //                 Path::from_strs(&["int"]).nowhere(),
        //                 vec![hir::TypeExpression::Integer(5).nowhere()],
        //             )
        //             .nowhere(),
        //         )],
        //         output_type: hir::Type::Generic(
        //             Path::from_strs(&["int"]).nowhere(),
        //             vec![hir::TypeExpression::Integer(5).nowhere()],
        //         )
        //         .nowhere(),
        //         type_params: vec![],
        //     },
        //     body: ExprKind::Identifier(Path::from_strs(&["input"]).nowhere())
        //         .with_id(0)
        //         .nowhere(),
        // };

        // let mut state = TypeState::new();

        // state.visit_entity(&input).unwrap();

        // let t0 = get_type!(state, &TExpr::Id(0));
        // ensure_same_type!(
        //     state,
        //     t0,
        //     TypeVar::Known(
        //         t_int(&symtab),
        //         vec![TypeVar::Known(KnownType::Integer(5), vec![], None)],
        //         None
        //     )
        // );
    }

    #[ignore]
    #[test]
    fn entity_return_types_must_match() {
        todo!("Figure out how we handle built in types and name_ids");
        // let input = Entity {
        //     head: EntityHead {
        //         inputs: vec![(
        //             Identifier::Named("input".to_string()).nowhere(),
        //             hir::Type::Generic(
        //                 Path::from_strs(&["int"]).nowhere(),
        //                 vec![hir::TypeExpression::Integer(5).nowhere()],
        //             )
        //             .nowhere(),
        //         )],
        //         output_type: hir::Type::Concrete(Path::from_strs(&["bool"])).nowhere(),
        //         type_params: vec![],
        //     },
        //     body: ExprKind::Identifier(Path::from_strs(&["input"]).nowhere())
        //         .with_id(0)
        //         .nowhere(),
        // };

        // let mut state = TypeState::new();

        // assert_matches!(
        //     state.visit_entity(&input),
        //     Err(Error::EntityOutputTypeMismatch { .. })
        // );
    }

    #[test]
    fn block_visiting_without_definitions_works() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::Block(Box::new(Block {
            statements: vec![],
            result: ExprKind::IntLiteral(5).with_id(0).nowhere(),
        }))
        .with_id(1)
        .nowhere();

        let mut state = TypeState::new();

        state.visit_expression(&input, &symtab).unwrap();

        ensure_same_type!(state, TExpr::Id(0), unsized_int(2, &symtab));
        ensure_same_type!(state, TExpr::Id(1), unsized_int(2, &symtab));
    }

    #[test]
    fn integer_literals_are_compatible_with_fixed_size_ints() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::If(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            Box::new(Expression::ident(1, 1, "b").nowhere()),
            Box::new(Expression::ident(2, 2, "c").nowhere()),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_equation(expr_a.clone(), TVar::Unknown(100));
        state.add_equation(expr_b.clone(), unsized_int(101, &symtab));
        state.add_equation(expr_c.clone(), sized_int(5, &symtab));

        state.visit_expression(&input, &symtab).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));
        let t3 = get_type!(state, &TExpr::Id(3));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);
        let tc = get_type!(state, &expr_c);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(&symtab), vec![], None));
        ensure_same_type!(state, t1, sized_int(5, &symtab));
        ensure_same_type!(state, t2, sized_int(5, &symtab));
        ensure_same_type!(state, t3, sized_int(5, &symtab));

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
        ensure_same_type!(state, t2, tc);
    }

    #[test]
    fn registers_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Register {
            pattern: Pattern::Name(name_id(0, "a")).nowhere(),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(3)
                .nowhere(),
            reset: None,
            value: ExprKind::IntLiteral(0).with_id(0).nowhere(),
            value_type: None,
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_equation(expr_clk.clone(), TVar::Unknown(100));

        state.visit_register(&input, &symtab).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let tclk = get_type!(state, &TExpr::Name(name_id(1, "clk").inner));
        ensure_same_type!(state, t0, unsized_int(3, &symtab));
        ensure_same_type!(state, ta, unsized_int(3, &symtab));
        ensure_same_type!(state, tclk, t_clock(&symtab));
    }

    #[test]
    fn self_referential_registers_typepcheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Register {
            pattern: Pattern::Name(name_id(0, "a")).nowhere(),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(3)
                .nowhere(),
            reset: None,
            value: ExprKind::Identifier(name_id(0, "a").inner)
                .with_id(0)
                .nowhere(),
            value_type: None,
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_equation(expr_clk.clone(), TVar::Unknown(100));

        state.visit_register(&input, &symtab).unwrap();

        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let tclk = get_type!(state, &TExpr::Name(name_id(1, "clk").inner));
        ensure_same_type!(state, ta, TVar::Unknown(2));
        ensure_same_type!(state, tclk, t_clock(&symtab));
    }

    #[test]
    fn registers_with_resets_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let rst_cond = name_id(2, "rst").inner;
        let rst_value = name_id(3, "rst_value").inner;
        let input = hir::Register {
            pattern: Pattern::Name(name_id(0, "a")).nowhere(),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(3)
                .nowhere(),
            reset: Some((
                ExprKind::Identifier(rst_cond.clone()).with_id(1).nowhere(),
                ExprKind::Identifier(rst_value.clone()).with_id(2).nowhere(),
            )),
            value: ExprKind::IntLiteral(0).with_id(0).nowhere(),
            value_type: None,
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        let expr_rst_cond = TExpr::Name(name_id(2, "rst").inner);
        let expr_rst_value = TExpr::Name(name_id(3, "rst_value").inner);
        state.add_equation(expr_clk.clone(), TVar::Unknown(100));
        state.add_equation(expr_rst_cond.clone(), TVar::Unknown(101));
        state.add_equation(expr_rst_value.clone(), TVar::Unknown(102));

        state.visit_register(&input, &symtab).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let tclk = get_type!(state, &TExpr::Name(name_id(1, "clk").inner));
        let trst_cond = get_type!(state, &TExpr::Name(rst_cond.clone()));
        let trst_val = get_type!(state, &TExpr::Name(rst_value.clone()));
        ensure_same_type!(state, t0, unsized_int(3, &symtab));
        ensure_same_type!(state, ta, unsized_int(3, &symtab));
        ensure_same_type!(state, tclk, t_clock(&symtab));
        ensure_same_type!(state, trst_cond, t_bool(&symtab));
        ensure_same_type!(state, trst_val, unsized_int(3, &symtab));
    }

    #[test]
    fn untyped_let_bindings_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Statement::Binding(
            Pattern::Name(name_id(0, "a")).nowhere(),
            None,
            ExprKind::IntLiteral(0).with_id(0).nowhere(),
        )
        .nowhere();

        let mut state = TypeState::new();

        state.visit_statement(&input, &symtab).unwrap();

        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        ensure_same_type!(state, ta, unsized_int(1, &symtab));
    }

    #[test]
    fn tuple_type_specs_propagate_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = Register {
            pattern: Pattern::Name(name_id(0, "test")).nowhere(),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(0)
                .nowhere(),
            reset: None,
            value: ExprKind::TupleLiteral(vec![
                ExprKind::IntLiteral(5).with_id(1).nowhere(),
                ExprKind::BoolLiteral(true).with_id(2).nowhere(),
            ])
            .with_id(3)
            .nowhere(),
            value_type: Some(
                hir::TypeSpec::Tuple(vec![
                    dtype!(symtab => "int"; ( t_num(5) )),
                    hir::dtype!(symtab => "bool"),
                ])
                .nowhere(),
            ),
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_equation(expr_clk.clone(), TVar::Unknown(100));

        state.visit_register(&input, &symtab).unwrap();

        let ttup = get_type!(state, &TExpr::Id(3));
        let reg = get_type!(state, &TExpr::Name(name_id(0, "test").inner));
        let expected = TypeVar::Tuple(vec![
            sized_int(5, &symtab),
            TypeVar::Known(t_bool(&symtab), vec![], None),
        ]);
        ensure_same_type!(state, ttup, expected);
        ensure_same_type!(state, reg, expected);
    }

    #[test]
    fn entity_type_inference_works() {
        // Add the head to the symtab
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        // Add the entity to the symtab
        let entity = hir::EntityHead {
            inputs: hir::ParameterList(vec![
                (ast_ident("a"), dtype!(symtab => "bool")),
                (ast_ident("b"), dtype!(symtab => "int"; (t_num(10)))),
            ]),
            output_type: Some(dtype!(symtab => "int"; (t_num(5)))),
            type_params: vec![],
        };

        let entity_name = symtab.add_thing(ast_path("test").inner, Thing::Entity(entity.nowhere()));

        let input = ExprKind::EntityInstance(
            entity_name.nowhere(),
            vec![
                Argument {
                    target: ast_ident("a"),
                    value: Expression::ident(0, 0, "x").nowhere(),
                    kind: hir::ArgumentKind::Named,
                },
                Argument {
                    target: ast_ident("b"),
                    value: Expression::ident(1, 1, "b").nowhere(),
                    kind: hir::ArgumentKind::Named,
                },
            ],
        )
        .with_id(2)
        .nowhere();

        let mut state = TypeState::new();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        state.add_equation(expr_a.clone(), TVar::Unknown(100));
        state.add_equation(expr_b.clone(), TVar::Unknown(101));

        state.visit_expression(&input, &symtab).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(&symtab), vec![], None));
        ensure_same_type!(
            state,
            t1,
            TVar::Known(
                t_int(&symtab),
                vec![TypeVar::Known(KnownType::Integer(10), vec![], None)],
                None,
            )
        );
        ensure_same_type!(
            state,
            t2,
            TVar::Known(
                t_int(&symtab),
                vec![TypeVar::Known(KnownType::Integer(5), vec![], None)],
                None,
            )
        );

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
    }

    #[test]
    fn pipeline_type_inference_works() {
        // Add the head to the symtab
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        // Add the entity to the symtab
        let entity = hir::PipelineHead {
            depth: 2.nowhere(),
            inputs: hir::ParameterList(vec![
                (ast_ident("a"), dtype!(symtab => "bool")),
                (ast_ident("b"), dtype!(symtab => "int"; ( t_num(10) ))),
            ]),
            output_type: Some(dtype!(symtab => "int"; ( t_num(5) ))),
        };

        let entity_name =
            symtab.add_thing(ast_path("test").inner, Thing::Pipeline(entity.nowhere()));

        let input = ExprKind::PipelineInstance {
            depth: 2.nowhere(),
            name: entity_name.nowhere(),
            args: vec![
                Argument {
                    target: ast_ident("a"),
                    value: Expression::ident(0, 0, "x").nowhere(),
                    kind: hir::ArgumentKind::Named,
                },
                Argument {
                    target: ast_ident("b"),
                    value: Expression::ident(1, 1, "b").nowhere(),
                    kind: hir::ArgumentKind::Named,
                },
            ],
        }
        .with_id(2)
        .nowhere();

        let mut state = TypeState::new();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        state.add_equation(expr_a.clone(), TVar::Unknown(100));
        state.add_equation(expr_b.clone(), TVar::Unknown(101));

        state.visit_expression(&input, &symtab).unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);

        // Check the generic type variables
        ensure_same_type!(state, t0, TVar::Known(t_bool(&symtab), vec![], None));
        ensure_same_type!(
            state,
            t1,
            TVar::Known(
                t_int(&symtab),
                vec![TypeVar::Known(KnownType::Integer(10), vec![], None)],
                None,
            )
        );
        ensure_same_type!(
            state,
            t2,
            TVar::Known(
                t_int(&symtab),
                vec![TypeVar::Known(KnownType::Integer(5), vec![], None)],
                None,
            )
        );

        // Check the constraints added to the literals
        ensure_same_type!(state, t0, ta);
        ensure_same_type!(state, t1, tb);
    }
}
