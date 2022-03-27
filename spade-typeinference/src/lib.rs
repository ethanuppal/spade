// This algorithm is based off the excelent lecture here
// https://www.youtube.com/watch?v=xJXcZp2vgLs
//
// The basic idea is to go through every node in the HIR tree, for every typed thing,
// add an equation indicating a constraint on that thing. This can only be done once
// and should be done by the visitor for that node. The visitor should then unify
// types according to the rules of the node.

use hir::symbol_table::{Patternable, PatternableKind, TypeSymbol};
use hir::{Argument, FunctionLike, ParameterList, Pattern, PatternArgument, TypeParam};
use hir::{ExecutableItem, ItemList};
use parse_tree_macros::trace_typechecker;
use spade_common::location_info::Loc;
use spade_common::name::NameID;
use spade_hir as hir;
use spade_hir::symbol_table::SymbolTable;
use spade_hir::{Block, Entity, ExprKind, Expression, Register, Statement};
use spade_types::KnownType;
use std::collections::HashMap;
use std::sync::atomic::AtomicU64;
use trace_stack::TraceStack;

pub mod equation;
pub mod error_reporting;
pub mod expression;
pub mod fixed_types;
pub mod mir_type_lowering;
pub mod pipeline;
pub mod result;
pub mod testutil;
pub mod trace_stack;

use crate::fixed_types::t_clock;
use crate::fixed_types::{t_bool, t_int};
use crate::trace_stack::{format_trace_stack, TraceStackEntry};

use equation::{FreeTypeVar, InnerTypeVar, TypeEquations, TypeVarRef, TypedExpression};
use result::{Error, Result};

use self::result::{UnificationError, UnificationErrorExt, UnificationTrace};

// NOTE(allow) This is a debug macro which is not normally used but can come in handy
#[allow(unused_macros)]
macro_rules! add_trace {
    ($self:expr, $($arg : tt) *) => {
        $self.trace_stack.push(TraceStack::Message(format!($($arg)*)))
    }
}

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
    StructInstance,
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
                        ExecutableItem::StructInstance { .. } => Ok(ProcessedItem::StructInstance),
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

// A token indicating the existence of a generic list in type TypeState. Used to
// ensure that the generic list is dropped at an appropriate time and not aquired
// later
#[must_use]
pub struct GenericListToken {
    id: usize,
}

/// State of the type inference algorithm
pub struct TypeState {
    equations: TypeEquations,
    /// The next type id. Can be incremented without mutable references thanks to
    /// the atomic. This is done to ensure that one can call `new_type` without having
    /// a mutable reference.
    ///
    /// This in turn is done since owning a &mut of the type state represents none of
    /// the live type variables changing
    next_typeid: AtomicU64,
    // List of the mapping between generic parameters and type vars. Managed here
    // because unification must update *all* TypeVars in existence.
    generic_lists: Vec<HashMap<NameID, InnerTypeVar>>,

    pub trace_stack: TraceStack,
}

impl TypeState {
    pub fn new() -> Self {
        Self {
            equations: HashMap::new(),
            next_typeid: AtomicU64::new(0),
            trace_stack: TraceStack::new(),
            generic_lists: vec![],
        }
    }

    // Get a generic list with a safe unwrap since a token is aquired
    fn get_generic_list<'a>(
        &'a self,
        generic_list_token: &'a GenericListToken,
    ) -> &'a HashMap<NameID, InnerTypeVar> {
        &self.generic_lists[generic_list_token.id]
    }

    fn hir_type_expr_to_var<'a>(
        &'a self,
        e: &hir::TypeExpression,
        generic_list_token: &GenericListToken,
    ) -> TypeVarRef<'a> {
        match e {
            hir::TypeExpression::Integer(i) => {
                TypeVarRef::known(KnownType::Integer(*i), vec![], None)
            }
            hir::TypeExpression::TypeSpec(spec) => self.type_var_from_hir(spec, generic_list_token),
        }
    }

    fn type_var_from_hir<'a>(
        &'a self,
        hir_type: &crate::hir::TypeSpec,
        generic_list_token: &GenericListToken,
    ) -> TypeVarRef<'a> {
        let generic_list = self.get_generic_list(generic_list_token);
        match hir_type {
            hir::TypeSpec::Declared(base, params) => {
                let params = params
                    .into_iter()
                    .map(|e| self.hir_type_expr_to_var(e, generic_list_token))
                    .collect();

                TypeVarRef::known(KnownType::Type(base.inner.clone()), params, None)
            }
            hir::TypeSpec::Generic(name) => match generic_list.get(name) {
                Some(t) => TypeVarRef::from_owned(t.clone(), self),
                None => {
                    panic!("No entry for {} in generic_list", name)
                }
            },
            hir::TypeSpec::Tuple(inner) => {
                let inner = inner
                    .iter()
                    .map(|t| self.type_var_from_hir(t, generic_list_token))
                    .collect();
                TypeVarRef::tuple(inner)
            }
            hir::TypeSpec::Array { inner, size } => {
                let inner = self.type_var_from_hir(inner, generic_list_token);
                let size = self.hir_type_expr_to_var(size, generic_list_token);

                TypeVarRef::array(inner, size)
            }
            hir::TypeSpec::Unit(_) => {
                todo!("Support unit type in type inference")
            }
        }
    }

    /// Returns the type of the expression with the specified id. Error if unknown
    pub fn type_of<'a>(&'a self, expr: &TypedExpression) -> Result<TypeVarRef<'a>> {
        for (e, t) in &self.equations {
            if e == expr {
                return Ok(TypeVarRef::from_ref(&t, self));
            }
        }
        Err(Error::UnknownType(expr.clone()).into())
    }

    pub fn new_generic_int<'a>(&'a self, symtab: &SymbolTable) -> TypeVarRef<'a> {
        TypeVarRef::known(t_int(symtab), vec![self.new_generic()], None)
    }

    fn new_generic<'a>(&'a self) -> TypeVarRef<'a> {
        let id = self.new_typeid();
        TypeVarRef::from_owned(InnerTypeVar::Unknown(id), self)
    }

    #[trace_typechecker]
    pub fn visit_entity(&mut self, entity: &Entity, symtab: &SymbolTable) -> Result<()> {
        let generic_list = if entity.head.type_params.is_empty() {
            self.create_generic_list(&[])
        } else {
            todo!("Support entity definitions with generics")
        };

        // Add equations for the inputs
        for (name, t) in &entity.inputs {
            let tvar = self.type_var_from_hir(t, &generic_list);
            self.add_equation(TypedExpression::Name(name.clone()), tvar)
                .commit(self);
        }

        self.visit_expression(&entity.body, symtab, &generic_list)?;

        // Ensure that the output type matches what the user specified, and unit otherwise
        if let Some(output_type) = &entity.head.output_type {
            let tvar = self.type_var_from_hir(&output_type, &generic_list);
            self.unify(
                &TypedExpression::Id(entity.body.inner.id),
                tvar.as_ref(),
                symtab,
            )
            .map_err(|(got, expected)| Error::EntityOutputTypeMismatch {
                expected,
                got,
                type_spec: output_type.loc(),
                output_expr: entity.body.loc(),
            })?
            .commit(self);
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
    fn visit_argument_list(
        &mut self,
        args: &[Argument],
        params: &ParameterList,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
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
            self.visit_expression(&value, symtab, generic_list)?;
            let target_type = self.type_var_from_hir(&params.arg_type(&target), generic_list);

            self.unify(target_type.as_ref(), value, symtab)
                .map_err(|(expected, got)| match kind {
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
                })?
                .commit(self);
        }

        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_expression(
        &mut self,
        expression: &Loc<Expression>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Id(expression.inner.id), new_type)
            .commit(self);

        // Recurse down the expression
        match &expression.inner.kind {
            ExprKind::Identifier(_) => self.visit_identifier(expression, symtab)?,
            ExprKind::IntLiteral(_) => self.visit_int_literal(expression, symtab)?,
            ExprKind::BoolLiteral(_) => self.visit_bool_literal(expression, symtab)?,
            ExprKind::TupleLiteral(_) => {
                self.visit_tuple_literal(expression, symtab, generic_list)?
            }
            ExprKind::TupleIndex(_, _) => {
                self.visit_tuple_index(expression, symtab, generic_list)?
            }
            ExprKind::ArrayLiteral(_) => {
                self.visit_array_literal(expression, symtab, generic_list)?
            }
            ExprKind::FieldAccess(_, _) => {
                self.visit_field_access(expression, symtab, generic_list)?
            }
            ExprKind::Index(_, _) => self.visit_index(expression, symtab, generic_list)?,
            ExprKind::Block(_) => self.visit_block_expr(expression, symtab, generic_list)?,
            ExprKind::If(_, _, _) => self.visit_if(expression, symtab, generic_list)?,
            ExprKind::Match(_, _) => self.visit_match(expression, symtab, generic_list)?,
            ExprKind::BinaryOperator(_, _, _) => {
                self.visit_binary_operator(expression, symtab, generic_list)?
            }
            ExprKind::UnaryOperator(_, _) => {
                self.visit_unary_operator(expression, symtab, generic_list)?
            }
            ExprKind::EntityInstance(name, args) => {
                let head = symtab.entity_by_id(&name.inner);
                self.handle_function_like(expression, &head.inner, args, symtab)?;
            }
            ExprKind::PipelineInstance {
                depth: _,
                name,
                args,
            } => {
                let head = symtab.pipeline_by_id(&name.inner);
                self.handle_function_like(expression, &head.inner, args, symtab)?;
            }
            ExprKind::FnCall(name, args) => {
                let head = symtab.function_by_id(&name.inner);
                self.handle_function_like(expression, &head.inner, args, symtab)?;
            }
        }
        Ok(())
    }

    // Common handler for entities, functions and pipelines
    #[trace_typechecker]
    fn handle_function_like(
        &mut self,
        expression: &Loc<Expression>,
        head: &impl FunctionLike,
        args: &[Argument],
        symtab: &SymbolTable,
    ) -> Result<()> {
        // Add new symbols for all the type parameters
        let generic_list = self.create_generic_list(head.type_params());

        // Unify the types of the arguments
        self.visit_argument_list(args, &head.inputs(), symtab, &generic_list)?;

        let return_type = self.type_var_from_hir(
            &head
                .output_type()
                .as_ref()
                .expect("Unit return type from entity is unsupported"),
            &generic_list,
        );

        self.unify_expression_generic_error(expression, return_type.as_ref(), symtab)?
            .commit(self);

        Ok(())
    }

    fn create_generic_list(&mut self, params: &[Loc<TypeParam>]) -> GenericListToken {
        let id = self.generic_lists.len();
        let new_list = params
            .iter()
            .map(|param| {
                let name = match &param.inner {
                    hir::TypeParam::TypeName(_, name) => name.clone(),
                    hir::TypeParam::Integer(_, name) => name.clone(),
                };

                let t = self.new_generic();
                (name, t)
            })
            .map(|(name, t)| (name, t.as_ref().clone()))
            .collect();
        self.generic_lists.push(new_list);
        GenericListToken { id }
    }

    #[trace_typechecker]
    pub fn visit_block(
        &mut self,
        block: &Block,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        for statement in &block.statements {
            self.visit_statement(statement, symtab, generic_list)?
        }
        self.visit_expression(&block.result, symtab, generic_list)
    }

    #[trace_typechecker]
    pub fn visit_pattern(&mut self, pattern: &Loc<Pattern>, symtab: &SymbolTable) -> Result<()> {
        let new_type = self.new_generic();
        self.add_equation(TypedExpression::Id(pattern.inner.id), new_type)
            .commit(self);
        match &pattern.inner.kind {
            hir::PatternKind::Integer(_) => {
                let int_t = &self.new_generic_int(&symtab);
                self.unify(pattern, int_t.as_ref(), symtab)
                    .expect("Failed to unify new_generic with int")
                    .commit(self);
            }
            hir::PatternKind::Bool(_) => {
                self.unify(pattern, &t_bool(symtab), symtab)
                    .expect("Expected new_generic with boolean")
                    .commit(self);
            }
            hir::PatternKind::Name { name, pre_declared } => {
                if !pre_declared {
                    self.add_equation(
                        TypedExpression::Name(name.clone().inner),
                        pattern.get_type(self)?,
                    )
                    .commit(self);
                }
            }
            hir::PatternKind::Tuple(subpatterns) => {
                for pattern in subpatterns {
                    self.visit_pattern(pattern, symtab)?;
                }
                let tuple_type = TypeVarRef::tuple(
                    subpatterns
                        .iter()
                        .map(|pattern| {
                            let p_type = pattern.get_type(self)?;
                            Ok(p_type)
                        })
                        .collect::<Result<_>>()?,
                );

                self.unify(pattern, tuple_type.as_ref(), symtab)
                    .expect("Unification of new_generic with tuple type can not fail")
                    .commit(self);
            }
            hir::PatternKind::Type(name, args) => {
                let (condition_type, params, generic_list) =
                    match symtab.patternable_type_by_id(name).inner {
                        Patternable {
                            kind: PatternableKind::Enum,
                            params: _,
                        } => {
                            let enum_variant = symtab.enum_variant_by_id(name).inner;
                            let generic_list = self.create_generic_list(&enum_variant.type_params);

                            let condition_type =
                                self.type_var_from_hir(&enum_variant.output_type, &generic_list);

                            (condition_type, enum_variant.params, generic_list)
                        }
                        Patternable {
                            kind: PatternableKind::Struct,
                            params: _,
                        } => {
                            let s = symtab.struct_by_id(name).inner;
                            let generic_list = self.create_generic_list(&s.type_params);

                            let condition_type =
                                self.type_var_from_hir(&s.self_type, &generic_list);

                            (condition_type, s.params, generic_list)
                        }
                    };

                self.unify(pattern, condition_type.as_ref(), symtab)
                    .expect("Unification of new_generic with enum can not fail")
                    .commit(self);

                for (
                    i,
                    (
                        PatternArgument {
                            target,
                            value: pattern,
                            kind,
                        },
                        (_, target_type),
                    ),
                ) in args.iter().zip(params.0.iter()).enumerate()
                {
                    self.visit_pattern(pattern, symtab)?;
                    let target_type = self.type_var_from_hir(&target_type, &generic_list);

                    self.unify(target_type.as_ref(), pattern, symtab)
                        .map_err(|(expected, got)| match kind {
                            hir::ArgumentKind::Positional => Error::PositionalArgumentMismatch {
                                index: i,
                                expr: pattern.loc(),
                                expected,
                                got,
                            },
                            hir::ArgumentKind::Named => Error::NamedArgumentMismatch {
                                name: target.clone(),
                                expr: pattern.loc(),
                                expected,
                                got,
                            },
                            hir::ArgumentKind::ShortNamed => Error::ShortNamedArgumentMismatch {
                                name: target.clone(),
                                expected,
                                got,
                            },
                        })?
                        .commit(self);
                }
            }
        }
        Ok(())
    }

    #[trace_typechecker]
    pub fn visit_statement(
        &mut self,
        stmt: &Loc<Statement>,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        match &stmt.inner {
            Statement::Binding(pattern, t, value) => {
                self.visit_expression(value, symtab, generic_list)?;

                self.visit_pattern(pattern, symtab)?;

                self.unify(&TypedExpression::Id(pattern.id), value, symtab)
                    .map_err(|(expected, got)| Error::PatternTypeMissmatch {
                        pattern: pattern.loc(),
                        expected,
                        got,
                    })?
                    .commit(self);

                if let Some(t) = t {
                    let generic_list = self.create_generic_list(&[]);
                    let tvar = self.type_var_from_hir(&t, &generic_list);
                    self.unify(&TypedExpression::Id(pattern.id), tvar.as_ref(), symtab)
                        .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                            expected,
                            got,
                            loc: value.loc(),
                        })?
                        .commit(self);
                }

                Ok(())
            }
            Statement::Register(reg) => self.visit_register(reg, symtab, generic_list),
            Statement::Declaration(names) => {
                for name in names {
                    let new_type = self.new_generic();
                    self.add_equation(TypedExpression::Name(name.clone().inner), new_type)
                        .commit(self);
                }
                Ok(())
            }
        }
    }

    #[trace_typechecker]
    pub fn visit_register(
        &mut self,
        reg: &Register,
        symtab: &SymbolTable,
        generic_list: &GenericListToken,
    ) -> Result<()> {
        self.visit_pattern(&reg.pattern, symtab)?;

        self.visit_expression(&reg.clock, symtab, generic_list)?;
        self.visit_expression(&reg.value, symtab, generic_list)?;

        if let Some((rst_cond, rst_value)) = &reg.reset {
            self.visit_expression(&rst_cond, symtab, generic_list)?;
            self.visit_expression(&rst_value, symtab, generic_list)?;
            // Ensure cond is a boolean
            self.unify(&rst_cond.inner, &t_bool(symtab), symtab)
                .map_err(|(got, expected)| Error::NonBoolReset {
                    expected,
                    got,
                    loc: rst_cond.loc(),
                })?
                .commit(self);

            // Ensure the reset value has the same type as the register itself
            self.unify(&rst_value.inner, &reg.value.inner, symtab)
                .map_err(|(got, expected)| Error::RegisterResetMismatch {
                    expected,
                    got,
                    loc: rst_cond.loc(),
                })?
                .commit(self);
        }

        self.unify(&reg.clock, &t_clock(symtab), symtab)
            .map_err(|(got, expected)| Error::NonClockClock {
                expected,
                got,
                loc: reg.clock.loc(),
            })?
            .commit(self);

        self.unify(&TypedExpression::Id(reg.pattern.id), &reg.value, symtab)
            .map_err(|(expected, got)| Error::PatternTypeMissmatch {
                pattern: reg.pattern.loc(),
                expected,
                got,
            })?
            .commit(self);

        if let Some(t) = &reg.value_type {
            let token = self.create_generic_list(&[]);
            let tvar = self.type_var_from_hir(&t, &token);
            self.unify(&TypedExpression::Id(reg.pattern.id), tvar.as_ref(), symtab)
                .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                    expected,
                    got,
                    loc: reg.pattern.loc(),
                })?
                .commit(self);
        }

        Ok(())
    }
}

/// The result of a unification, i.e. a new type and potentially a type to replace.
/// Must be used by calling `commit`. This type should never be bound to a variable
/// as it contains unmanaged `InnerTypeVar` which could go stale.
///
/// This is required in order for the lifetime based variable system to work as it allows
/// the unfication, which uses lifetime limited type variables to work without mutable
/// references to the TypeState, which can be committed after the fact.
///
/// Has a drop bomb to ensure it is used
#[must_use]
struct UnificationTask {
    // List of (new, replacement) pairs
    pub tasks: Vec<(InnerTypeVar, Option<InnerTypeVar>)>,
}

impl UnificationTask {
    /// Returns the last type that was unified but has not been committed yet. This is
    /// effectively the resulting type of the unification process.
    ///
    /// Should not be called outside unify
    fn last_result_type(&self) -> InnerTypeVar {
        self.tasks
            .last()
            .expect("attempting to get last_result_type on unification task")
            .0
            .clone()
    }

    fn join(mut self, other: &mut UnificationTask) {
        other.tasks.append(&mut self.tasks);
        std::mem::forget(self);
    }

    fn commit(self, state: &mut TypeState) {
        for (new_type, replaced_type) in &self.tasks {
            if let Some(replaced_type) = replaced_type {
                let replaced_type = replaced_type;
                for (_, rhs) in &mut state.equations {
                    TypeState::replace_type_var(rhs, &replaced_type, new_type)
                }
                for generic_list in &mut state.generic_lists {
                    for (_, lhs) in generic_list.iter_mut() {
                        TypeState::replace_type_var(lhs, &replaced_type, new_type)
                    }
                }
            }
        }

        std::mem::forget(self)
    }
}

impl Drop for UnificationTask {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            panic!("Dropped a UnificationTask which was not committed")
        }
    }
}

// Similar to `UnificationTask` but for the addition of equations
#[must_use]
struct EquationTask {
    pub expression: TypedExpression,
    pub var: InnerTypeVar,
}

impl EquationTask {
    fn commit(self, state: &mut TypeState) {
        state.trace_stack.push(TraceStackEntry::AddingEquation(
            self.expression.clone(),
            FreeTypeVar::new(self.var.clone()),
        ));
        if let Some(prev) = state
            .equations
            .insert(self.expression.clone(), self.var.clone())
        {
            let var = self.var.clone();
            let expr = self.expression.clone();
            std::mem::forget(self);
            println!("{}", format_trace_stack(&state.trace_stack));
            panic!("Adding equation for {} == {} but a previous eq exists.\n\tIt was previously bound to {}", expr, var, prev)
        }
        std::mem::forget(self);
    }
}
impl Drop for EquationTask {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            panic!("Dropped an EquationTask which was not committed")
        }
    }
}

// Private helper functions
impl TypeState {
    fn new_typeid(&self) -> u64 {
        self.next_typeid
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    fn add_equation<'a>(&self, expression: TypedExpression, var: TypeVarRef<'a>) -> EquationTask {
        EquationTask {
            expression,
            var: var.as_ref().clone(),
        }
    }

    #[cfg(test)]
    fn add_eq_from_tvar(&mut self, expression: TypedExpression, var: InnerTypeVar) {
        self.add_equation(expression, TypeVarRef::from_owned(var, self))
            .commit(self)
    }

    fn unify(
        &self,
        e1: &impl HasType,
        e2: &impl HasType,
        symtab: &SymbolTable,
    ) -> std::result::Result<UnificationTask, UnificationError> {
        let v1 = e1
            .get_type(self)
            .expect("Tried to unify types but the lhs was not found");
        let v2 = e2
            .get_type(self)
            .expect("Tried to unify types but the rhs was not found");

        self.trace_stack
            .push(TraceStackEntry::TryingUnify(v1.as_free(), v2.as_free()));

        // Copy the original types so we can properly trace the progress of the
        // unification
        let v1cpy = v1.clone();
        let v2cpy = v2.clone();

        let err_producer = || {
            (
                UnificationTrace::new(v1.as_free()),
                UnificationTrace::new(v2.as_free()),
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

        let mut task = UnificationTask { tasks: vec![] };

        macro_rules! try_with_context {
            ($value: expr) => {
                match $value {
                    Ok(result) => result,
                    e => {
                        std::mem::forget(task);
                        return e.add_context(v1.clone(), v2.clone());
                    }
                }
            };
        }

        // Figure out the most general type, and take note if we need to
        // do any replacement of the types in the rest of the state
        let result = match (&v1.as_ref(), &v2.as_ref()) {
            (InnerTypeVar::Known(t1, p1, _), InnerTypeVar::Known(t2, p2, _)) => match (t1, t2) {
                (KnownType::Integer(val1), KnownType::Integer(val2)) => {
                    unify_if!(val1 == val2, v1, None)
                }
                (KnownType::Type(n1), KnownType::Type(n2)) => {
                    match (
                        &symtab.type_symbol_by_id(n1).inner,
                        &symtab.type_symbol_by_id(n2).inner,
                    ) {
                        (TypeSymbol::Declared(_, _), TypeSymbol::Declared(_, _)) => {
                            if n1 != n2 {
                                std::mem::forget(task);
                                return Err(err_producer());
                            }
                            if p1.len() != p2.len() {
                                std::mem::forget(task);
                                return Err(err_producer());
                            }

                            for (t1, t2) in p1.iter().zip(p2.iter()) {
                                try_with_context!(self.unify(t1, t2, symtab)).join(&mut task);
                            }

                            let new_ts1 = symtab.type_symbol_by_id(n1).inner;
                            let new_ts2 = symtab.type_symbol_by_id(n2).inner;
                            let new_v1 = e1
                                .get_type(self)
                                .expect("Tried to unify types but the lhs was not found");
                            unify_if!(new_ts1 == new_ts2, new_v1, None)
                        }
                        (TypeSymbol::Declared(_, _), TypeSymbol::GenericArg) => Ok((v1, Some(v2))),
                        (TypeSymbol::GenericArg, TypeSymbol::Declared(_, _)) => Ok((v2, Some(v1))),
                        (TypeSymbol::GenericArg, TypeSymbol::GenericArg) => Ok((v1, Some(v2))),
                        (TypeSymbol::Declared(_, _), TypeSymbol::GenericInt) => todo!(),
                        (TypeSymbol::GenericArg, TypeSymbol::GenericInt) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::Declared(_, _)) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::GenericArg) => todo!(),
                        (TypeSymbol::GenericInt, TypeSymbol::GenericInt) => todo!(),
                    }
                }
                (KnownType::Integer(_), KnownType::Type(_)) => Err(err_producer()),
                (KnownType::Type(_), KnownType::Integer(_)) => Err(err_producer()),
            },
            (InnerTypeVar::Tuple(i1), InnerTypeVar::Tuple(i2)) => {
                if i1.len() != i2.len() {
                    std::mem::forget(task);
                    return Err(err_producer());
                }

                for (t1, t2) in i1.iter().zip(i2.iter()) {
                    try_with_context!(self.unify(t1, t2, symtab)).join(&mut task);
                }

                Ok((v1, None))
            }
            (
                InnerTypeVar::Array {
                    inner: i1,
                    size: s1,
                },
                InnerTypeVar::Array {
                    inner: i2,
                    size: s2,
                },
            ) => {
                let inner_task = try_with_context!(self.unify(i1.as_ref(), i2.as_ref(), symtab));
                let inner = inner_task.last_result_type();
                inner_task.join(&mut task);
                let size_task = try_with_context!(self.unify(s1.as_ref(), s2.as_ref(), symtab));
                let size = size_task.last_result_type();
                size_task.join(&mut task);

                Ok((
                    TypeVarRef::array(
                        TypeVarRef::from_owned(inner.clone(), self),
                        TypeVarRef::from_owned(size.clone(), self),
                    ),
                    None,
                ))
            }
            // Unknown with other
            (InnerTypeVar::Unknown(_), InnerTypeVar::Unknown(_)) => Ok((v1, Some(v2))),
            (_other, InnerTypeVar::Unknown(_)) => Ok((v1, Some(v2))),
            (InnerTypeVar::Unknown(_), _other) => Ok((v2, Some(v1))),
            // Incompatibilities
            (InnerTypeVar::Known(_, _, _), _other) => Err(err_producer()),
            (_other, InnerTypeVar::Known(_, _, _)) => Err(err_producer()),
            (InnerTypeVar::Tuple(_), _other) => Err(err_producer()),
            (_other, InnerTypeVar::Tuple(_)) => Err(err_producer()),
        };

        let (new_type, replaced_type) = match result {
            Ok(result) => result,
            Err(e) => {
                std::mem::forget(task);
                return Err(e);
            }
        };

        task.tasks.push((
            new_type.as_ref().clone(),
            replaced_type.map(|i| i.as_ref().clone()),
        ));

        self.trace_stack.push(TraceStackEntry::Unified(
            v1cpy.as_free(),
            v2cpy.as_free(),
            new_type.as_free(),
        ));

        Ok(task)
    }

    fn replace_type_var(
        in_var: &mut InnerTypeVar,
        from: &InnerTypeVar,
        replacement: &InnerTypeVar,
    ) {
        // First, do recursive replacement
        match in_var {
            InnerTypeVar::Known(_, params, _) => {
                for param in params {
                    Self::replace_type_var(param, from, replacement)
                }
            }
            InnerTypeVar::Tuple(inner) => {
                for t in inner {
                    Self::replace_type_var(t, from, replacement)
                }
            }
            InnerTypeVar::Array { inner, size } => {
                Self::replace_type_var(inner, from, replacement);
                Self::replace_type_var(size, from, replacement);
            }
            InnerTypeVar::Unknown(_) => {}
        }

        if in_var == from {
            *in_var = replacement.clone();
        }
    }

    fn unify_expression_generic_error<'a>(
        &self,
        expr: &Loc<Expression>,
        other: &impl HasType,
        symtab: &SymbolTable,
    ) -> Result<UnificationTask> {
        self.unify(&expr.inner, other, symtab)
            .map_err(|(got, expected)| Error::UnspecifiedTypeError {
                got,
                expected,
                loc: expr.loc(),
            })
    }
}

impl TypeState {
    pub fn print_equations(&self) {
        for (lhs, rhs) in &self.equations {
            println!("{}: {}", lhs, rhs);
        }
    }
}

pub trait HasType: std::fmt::Debug {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>>;
}

impl HasType for InnerTypeVar {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>> {
        Ok(TypeVarRef::from_ref(self, state))
    }
}
impl HasType for Loc<InnerTypeVar> {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>> {
        self.inner.get_type(state)
    }
}
impl HasType for TypedExpression {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>> {
        state.type_of(self)
    }
}
impl HasType for Expression {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>> {
        state.type_of(&TypedExpression::Id(self.id))
    }
}
impl HasType for Loc<Expression> {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>> {
        state.type_of(&TypedExpression::Id(self.inner.id))
    }
}
impl HasType for Pattern {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>> {
        state.type_of(&TypedExpression::Id(self.id))
    }
}
impl HasType for Loc<Pattern> {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>> {
        state.type_of(&TypedExpression::Id(self.inner.id))
    }
}
impl HasType for KnownType {
    fn get_type<'a, 'b: 'a>(&'b self, state: &'a TypeState) -> Result<TypeVarRef<'a>> {
        Ok(TypeVarRef::from_owned(
            InnerTypeVar::Known(self.clone(), vec![], None),
            state,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use super::InnerTypeVar as TVar;
    use super::TypedExpression as TExpr;

    use crate::testutil::{sized_int, unsized_int};
    use crate::{ensure_same_type, get_type};
    use crate::{
        fixed_types::t_clock,
        hir::{self, Block},
    };
    use hir::symbol_table::TypeDeclKind;
    use hir::PatternKind;
    use hir::{dtype, testutil::t_num, Argument};
    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;
    use spade_hir::symbol_table::{SymbolTable, Thing};

    #[test]
    fn int_literals_have_type_known_int() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        let generic_list = state.create_generic_list(&vec![]);
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::IntLiteral(0).with_id(0).nowhere();

        state
            .visit_expression(&input, &symtab, &generic_list)
            .expect("Type error");

        ensure_same_type!(state, TExpr::Id(0), unsized_int(1, &symtab));
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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Check the generic type variables
        ensure_same_type!(
            state,
            TExpr::Id(0),
            TVar::Known(t_bool(&symtab), vec![], None)
        );
        ensure_same_type!(state, TExpr::Id(1), TExpr::Id(2));
        ensure_same_type!(state, TExpr::Id(1), TExpr::Id(3));

        // Check the constraints added to the literals
        ensure_same_type!(state, TExpr::Id(0), expr_a);
        ensure_same_type!(state, TExpr::Id(1), expr_b);
        ensure_same_type!(state, TExpr::Id(2), expr_c);
    }

    #[test]
    fn if_expressions_get_correct_type_when_branches_are_of_known_type() {
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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), unsized_int(101, &symtab));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Check the generic type variables
        ensure_same_type!(
            state,
            TExpr::Id(0),
            TVar::Known(t_bool(&symtab), vec![], None)
        );
        ensure_same_type!(state, TExpr::Id(1), unsized_int(101, &symtab));
        ensure_same_type!(state, TExpr::Id(2), unsized_int(101, &symtab));
        ensure_same_type!(state, TExpr::Id(3), unsized_int(101, &symtab));

        // Check the constraints added to the literals
        ensure_same_type!(state, TExpr::Id(0), expr_a);
        ensure_same_type!(state, TExpr::Id(1), expr_b);
        ensure_same_type!(state, TExpr::Id(2), expr_c);
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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), unsized_int(101, &symtab));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Known(t_clock(&symtab), vec![], None));

        let generic_list = state.create_generic_list(&vec![]);
        assert_ne!(
            state.visit_expression(&input, &symtab, &generic_list),
            Ok(())
        );
    }

    #[test]
    fn match_expressions_have_correctly_infered_types() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let first_pattern = PatternKind::Tuple(vec![
            PatternKind::name(name_id(10, "x1")).with_id(20).nowhere(),
            PatternKind::name(name_id(11, "x2")).with_id(21).nowhere(),
        ])
        .with_id(22)
        .nowhere();

        let input = ExprKind::Match(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            vec![
                (first_pattern, Expression::ident(1, 1, "b").nowhere()),
                (
                    PatternKind::name(name_id(12, "y")).with_id(23).nowhere(),
                    Expression::ident(2, 2, "c").nowhere(),
                ),
            ],
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), unsized_int(101, &symtab));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Ensure branches have the same type
        ensure_same_type!(state, expr_b, &expr_c);
        // And that the match block has the same type
        ensure_same_type!(state, expr_c, TExpr::Id(3));

        // Ensure patterns have same type as each other, and as the expression
        ensure_same_type!(state, expr_a, TExpr::Id(22));
        ensure_same_type!(state, TExpr::Id(22), TExpr::Id(23));
    }

    #[test]
    fn patterns_constrain_expression_types() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let first_pattern = PatternKind::Tuple(vec![
            PatternKind::Bool(true).with_id(20).nowhere(),
            PatternKind::Bool(true).with_id(21).nowhere(),
        ])
        .with_id(22)
        .nowhere();

        let input = ExprKind::Match(
            Box::new(Expression::ident(0, 0, "a").nowhere()),
            vec![
                (first_pattern, Expression::ident(1, 1, "b").nowhere()),
                (
                    PatternKind::name(name_id(11, "y")).with_id(23).nowhere(),
                    Expression::ident(2, 2, "c").nowhere(),
                ),
            ],
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        let expr_c = TExpr::Name(name_id(2, "c").inner);
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));
        state.add_eq_from_tvar(expr_c.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        let expected_type = TVar::Tuple(vec![kvar!(t_bool(&symtab)), kvar!(t_bool(&symtab))]);

        // Ensure patterns have same type as each other, and as the expression
        ensure_same_type!(state, expr_a, expected_type);
    }

    #[test]
    fn not_all_types_are_the_same() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let not_bool = symtab.add_type_with_id(
            100,
            ast_path("not_bool").inner,
            TypeSymbol::Declared(vec![], TypeDeclKind::Enum).nowhere(),
        );

        let lhs = PatternKind::name(name_id(0, "x")).with_id(22).nowhere();

        state.add_eq_from_tvar(
            TExpr::Name(name_id(1, "a").inner),
            kvar!(KnownType::Type(not_bool)),
        );

        let input = Statement::Binding(
            lhs,
            Some(dtype!(symtab => "bool")),
            Expression::ident(1, 1, "a").nowhere(),
        )
        .nowhere();

        let generic_list = state.create_generic_list(&vec![]);
        assert!(state
            .visit_statement(&input, &symtab, &generic_list)
            .is_err());
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

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), unsized_int(101, &symtab));
        state.add_eq_from_tvar(expr_c.clone(), sized_int(5, &symtab));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Check the generic type variables
        ensure_same_type!(
            state,
            TExpr::Id(0),
            TVar::Known(t_bool(&symtab), vec![], None)
        );
        ensure_same_type!(state, TExpr::Id(1), sized_int(5, &symtab));
        ensure_same_type!(state, TExpr::Id(2), sized_int(5, &symtab));
        ensure_same_type!(state, TExpr::Id(3), sized_int(5, &symtab));

        // Check the constraints added to the literals
        ensure_same_type!(state, TExpr::Id(0), expr_a);
        ensure_same_type!(state, TExpr::Id(1), expr_b);
        ensure_same_type!(state, TExpr::Id(2), expr_c);
    }

    #[test]
    fn array_indexing_infers_all_types_corectly() {
        let mut state = TypeState::new();
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = ExprKind::Index(
            Box::new(
                ExprKind::Identifier(name_id(0, "a").inner)
                    .with_id(1)
                    .nowhere(),
            ),
            Box::new(
                ExprKind::Identifier(name_id(1, "b").inner)
                    .with_id(2)
                    .nowhere(),
            ),
        )
        .with_id(3)
        .nowhere();

        // Add eqs for the literals
        let expr_a = TExpr::Name(name_id(0, "a").inner);
        let expr_b = TExpr::Name(name_id(1, "b").inner);
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // The index should be an integer
        ensure_same_type!(state, expr_b, unsized_int(4, &symtab));
        // The target should be an array

        ensure_same_type!(
            state,
            &expr_a,
            TVar::Array {
                inner: Box::new(TVar::Unknown(0)),
                size: Box::new(TVar::Unknown(5))
            }
        );

        // The result should be the inner type
        ensure_same_type!(state, TExpr::Id(3), TVar::Unknown(0));
    }

    #[test]
    fn registers_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Register {
            pattern: PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
            clock: ExprKind::Identifier(name_id(1, "clk").inner)
                .with_id(3)
                .nowhere(),
            reset: None,
            value: ExprKind::IntLiteral(0).with_id(0).nowhere(),
            value_type: None,
        };

        let mut state = TypeState::new();

        let expr_clk = TExpr::Name(name_id(1, "clk").inner);
        state.add_eq_from_tvar(expr_clk.clone(), TVar::Unknown(100));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_register(&input, &symtab, &generic_list)
            .unwrap();

        ensure_same_type!(state, TExpr::Id(0), unsized_int(3, &symtab));
        ensure_same_type!(
            state,
            TExpr::Name(name_id(0, "a").inner),
            unsized_int(3, &symtab)
        );
        ensure_same_type!(state, expr_clk, t_clock(&symtab));
    }

    #[test]
    fn self_referential_registers_typepcheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Register {
            pattern: PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
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
        state.add_eq_from_tvar(expr_clk.clone(), TVar::Unknown(100));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_register(&input, &symtab, &generic_list)
            .unwrap();

        ensure_same_type!(state, TExpr::Name(name_id(0, "a").inner), TVar::Unknown(2));
        ensure_same_type!(state, expr_clk, t_clock(&symtab));
    }

    #[test]
    fn registers_with_resets_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let rst_cond = name_id(2, "rst").inner;
        let rst_value = name_id(3, "rst_value").inner;
        let input = hir::Register {
            pattern: PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
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
        state.add_eq_from_tvar(expr_clk.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_rst_cond.clone(), TVar::Unknown(101));
        state.add_eq_from_tvar(expr_rst_value.clone(), TVar::Unknown(102));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_register(&input, &symtab, &generic_list)
            .unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        let tclk = get_type!(state, &TExpr::Name(name_id(1, "clk").inner));
        let trst_cond = get_type!(state, &TExpr::Name(rst_cond.clone()));
        let trst_val = get_type!(state, &TExpr::Name(rst_value.clone()));
        ensure_same_type!(state, t0.as_ref(), unsized_int(3, &symtab));
        ensure_same_type!(state, ta.as_ref(), unsized_int(3, &symtab));
        ensure_same_type!(state, tclk.as_ref(), t_clock(&symtab));
        ensure_same_type!(state, trst_cond.as_ref(), t_bool(&symtab));
        ensure_same_type!(state, trst_val.as_ref(), unsized_int(3, &symtab));
    }

    #[test]
    fn untyped_let_bindings_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Statement::Binding(
            PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
            None,
            ExprKind::IntLiteral(0).with_id(0).nowhere(),
        )
        .nowhere();

        let mut state = TypeState::new();

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_statement(&input, &symtab, &generic_list)
            .unwrap();

        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        ensure_same_type!(state, ta.as_ref(), unsized_int(1, &symtab));
    }

    #[test]
    fn typed_let_bindings_typecheck_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = hir::Statement::Binding(
            PatternKind::name(name_id(0, "a")).with_id(10).nowhere(),
            Some(dtype!(symtab => "int"; (t_num(5)))),
            ExprKind::IntLiteral(0).with_id(0).nowhere(),
        )
        .nowhere();

        let mut state = TypeState::new();

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_statement(&input, &symtab, &generic_list)
            .unwrap();

        let ta = get_type!(state, &TExpr::Name(name_id(0, "a").inner));
        ensure_same_type!(state, ta.as_ref(), sized_int(5, &symtab));
    }

    #[test]
    fn tuple_type_specs_propagate_correctly() {
        let mut symtab = SymbolTable::new();
        spade_ast_lowering::builtins::populate_symtab(&mut symtab, &mut ItemList::new());

        let input = Register {
            pattern: PatternKind::name(name_id(0, "test")).with_id(10).nowhere(),
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
        state.add_eq_from_tvar(expr_clk.clone(), TVar::Unknown(100));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_register(&input, &symtab, &generic_list)
            .unwrap();

        let ttup = get_type!(state, &TExpr::Id(3));
        let reg = get_type!(state, &TExpr::Name(name_id(0, "test").inner));
        let expected = InnerTypeVar::Tuple(vec![
            sized_int(5, &symtab),
            InnerTypeVar::Known(t_bool(&symtab), vec![], None),
        ]);
        ensure_same_type!(state, ttup.as_ref(), &expected);
        ensure_same_type!(state, reg.as_ref(), &expected);
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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        let t0 = get_type!(state, &TExpr::Id(0));
        let t1 = get_type!(state, &TExpr::Id(1));
        let t2 = get_type!(state, &TExpr::Id(2));

        let ta = get_type!(state, &expr_a);
        let tb = get_type!(state, &expr_b);

        // Check the generic type variables
        ensure_same_type!(
            state,
            t0.as_ref(),
            TVar::Known(t_bool(&symtab), vec![], None)
        );
        ensure_same_type!(
            state,
            t1.as_ref(),
            TVar::Known(
                t_int(&symtab),
                vec![InnerTypeVar::Known(KnownType::Integer(10), vec![], None)],
                None,
            )
        );
        ensure_same_type!(
            state,
            t2.as_ref(),
            TVar::Known(
                t_int(&symtab),
                vec![InnerTypeVar::Known(KnownType::Integer(5), vec![], None)],
                None,
            )
        );

        // Check the constraints added to the literals
        ensure_same_type!(state, t0.as_ref(), ta.as_ref());
        ensure_same_type!(state, t1.as_ref(), tb.as_ref());
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
            type_params: vec![],
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
        state.add_eq_from_tvar(expr_a.clone(), TVar::Unknown(100));
        state.add_eq_from_tvar(expr_b.clone(), TVar::Unknown(101));

        let generic_list = state.create_generic_list(&vec![]);
        state
            .visit_expression(&input, &symtab, &generic_list)
            .unwrap();

        // Check the generic type variables
        ensure_same_type!(
            state,
            TExpr::Id(0),
            TVar::Known(t_bool(&symtab), vec![], None)
        );
        ensure_same_type!(
            state,
            TExpr::Id(1),
            TVar::Known(
                t_int(&symtab),
                vec![InnerTypeVar::Known(KnownType::Integer(10), vec![], None)],
                None,
            )
        );
        ensure_same_type!(
            state,
            TExpr::Id(2),
            TVar::Known(
                t_int(&symtab),
                vec![InnerTypeVar::Known(KnownType::Integer(5), vec![], None)],
                None,
            )
        );

        // Check the constraints added to the literals
        ensure_same_type!(state, &TExpr::Id(0), &expr_a);
        ensure_same_type!(state, &TExpr::Id(1), &expr_b);
    }
}
