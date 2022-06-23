use spade_ast as ast;
use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};
use spade_diagnostics::Diagnostic;
use spade_hir as hir;

use crate::{
    attributes::report_unused_attributes, comptime::ComptimeCondExt, error::Result, unit_name,
    visit_expression, Context, LocExt, SelfContext,
};
use spade_hir::symbol_table::SymbolTable;

pub struct PipelineContext {
    /// All stages within the pipeline, possibly labelled
    pub stages: Vec<Option<Loc<Identifier>>>,
    /// The stage we are currently lowering
    pub current_stage: usize,
}

impl PipelineContext {
    pub fn get_stage(&self, name: &Identifier) -> Option<usize> {
        for (i, stage_name) in self.stages.iter().enumerate() {
            if stage_name.as_ref().map(|n| &n.inner) == Some(name) {
                return Some(i);
            }
        }
        None
    }

    /// Returns the location of the previous definition of stage `name` if such
    /// a definition exists
    pub fn previous_def(&self, name: &Identifier) -> Option<Loc<Identifier>> {
        for stage_name in &self.stages {
            if stage_name.as_ref().map(|n| &n.inner) == Some(name) {
                return stage_name.clone();
            }
        }
        None
    }
}

pub fn pipeline_head(input: &ast::Pipeline, symtab: &mut SymbolTable) -> Result<hir::PipelineHead> {
    let depth = input.depth.map(|u| u as usize);

    // FIXME: Support type parameters in pipelines
    // lifeguard https://gitlab.com/spade-lang/spade/-/issues/124
    let type_params = vec![];
    if !input.type_params.is_empty() {
        panic!("Pipelines currently do not support type parameters")
    }

    let inputs = crate::visit_parameter_list(&input.inputs, symtab, SelfContext::FreeStanding)?;

    let output_type = if let Some(output_type) = &input.output_type {
        Some(super::visit_type_spec(output_type, symtab)?)
    } else {
        None
    };

    Ok(hir::PipelineHead {
        name: input.name.clone(),
        depth,
        inputs,
        output_type,
        type_params,
    })
}

fn visit_pipeline_statement(
    statement: &ast::Statement,
    current_stage: &mut usize,
    ctx: &mut Context,
    pipeline_ctx: &mut PipelineContext,
) -> Result<()> {
    match &statement {
        ast::Statement::Label(name) => {
            if let Some(previous) = &pipeline_ctx.stages[*current_stage] {
                // FIXME: We might actually want to support multiple labels
                // for the same stage... If so we need to rewrite
                // some other parts
                return Err(
                    Diagnostic::error(name, "Multiple labels for the same stage")
                        .primary_label("This stage has already been labeled")
                        .secondary_label(previous, "Previously labeled here")
                        .into(),
                );
            }

            if let Some(prev) = pipeline_ctx.previous_def(name) {
                return Err(Diagnostic::error(name, "Stage was already defined")
                    .primary_label(format!("'{} has already been defined", name))
                    .secondary_label(prev, "Previously defined here")
                    .into());
            }
            pipeline_ctx.stages[*current_stage] = Some(name.clone());
        }
        ast::Statement::Declaration(_) => {}
        ast::Statement::Binding(_, _, _) => {}
        ast::Statement::PipelineRegMarker(count) => {
            for _ in 0..*count {
                *current_stage += 1;
                pipeline_ctx.stages.push(None)
            }
        }
        ast::Statement::Register(_) => {}
        ast::Statement::Assert(_) => {}
        ast::Statement::Comptime(inner) => {
            if let Some(inner_stmts) = inner.maybe_unpack(&ctx.symtab)? {
                for inner_stmt in inner_stmts {
                    visit_pipeline_statement(&inner_stmt, current_stage, ctx, pipeline_ctx)?;
                }
            }
        }
        ast::Statement::Set { .. } => {}
    };
    Ok(())
}

#[tracing::instrument(skip(pipeline, ctx))]
pub fn visit_pipeline(pipeline: &Loc<ast::Pipeline>, ctx: &mut Context) -> Result<hir::Item> {
    let ast::Pipeline {
        depth,
        name,
        inputs: ast_inputs,
        output_type: _,
        body,
        type_params,
        mut attributes,
    } = pipeline.inner.clone();

    ctx.symtab.new_scope();

    // FIXME: Unify this code with the entity code
    let (id, head) = ctx
        .symtab
        .lookup_pipeline(&Path(vec![pipeline.name.clone()]).at_loc(&pipeline.name.loc()))
        .expect("Attempting to lower a pipeline that has not been added to the symtab previously");

    if head.inputs.0.is_empty() {
        return Err(
            Diagnostic::error(ast_inputs.loc(), "Missing clock argument for pipeline")
                .note("All pipelines need to take at least a clock as an argument")
                .into(),
        );
    }

    let unit_name = unit_name(&mut attributes, &id.at_loc(&name), &name, &type_params)?;

    // If this is a builtin pipeline
    if pipeline.body.is_none() {
        report_unused_attributes(&attributes)?;
        return Ok(hir::Item::BuiltinPipeline(unit_name, head));
    }

    // Add the inputs to the symtab
    let inputs = head
        .inputs
        .0
        .iter()
        .map(|(ident, ty)| {
            (
                ctx.symtab.add_local_variable(ident.clone()).at_loc(ident),
                ty.clone(),
            )
        })
        .collect();

    let mut context = PipelineContext {
        stages: vec![None],
        current_stage: 0,
    };

    let mut current_stage = 0;
    for statement in &body.as_ref().unwrap().assume_block().statements {
        visit_pipeline_statement(statement, &mut current_stage, ctx, &mut context)?;
    }

    if current_stage as u128 != depth.inner {
        return Err(
            Diagnostic::error(pipeline, "Wrong number of pipeline stages")
                .primary_label(format!("Found {} stages here", current_stage))
                .secondary_label(depth, format!("{} stages specified here", depth))
                .into(),
        );
    }

    ctx.pipeline_ctx.replace(context);
    let body = body.as_ref().unwrap().try_visit(visit_expression, ctx)?;
    ctx.pipeline_ctx = None;

    ctx.symtab.close_scope();

    // Any remaining attributes are unused and will have an error reported
    report_unused_attributes(&attributes)?;

    Ok(hir::Item::Pipeline(
        hir::Pipeline {
            head: head.inner,
            name: unit_name,
            inputs,
            body,
        }
        .at_loc(pipeline),
    ))
}

#[cfg(test)]
mod pipeline_visiting {
    use super::*;

    use spade_ast::testutil::ast_ident;
    use spade_common::{
        id_tracker::ExprIdTracker, location_info::WithLocation, name::testutil::name_id,
    };

    use pretty_assertions::assert_eq;

    #[test]
    fn relative_stage_references_work() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 2.nowhere(),
            inputs: ast::ParameterList::without_self(vec![(
                ast_ident("clk"),
                ast::TypeSpec::Unit(().nowhere()).nowhere(),
            )])
            .nowhere(),
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            body: Some(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![
                        ast::Statement::PipelineRegMarker(1).nowhere(),
                        ast::Statement::Binding(
                            ast::Pattern::name("a"),
                            None,
                            ast::Expression::IntLiteral(0).nowhere(),
                        )
                        .nowhere(),
                        ast::Statement::PipelineRegMarker(1).nowhere(),
                        ast::Statement::Binding(
                            ast::Pattern::name("b"),
                            None,
                            ast::Expression::PipelineReference {
                                stage_kw_and_reference_loc: ().nowhere(),
                                stage: ast::PipelineStageReference::Relative((-1).nowhere()),
                                name: ast_ident("a"),
                            }
                            .nowhere(),
                        )
                        .nowhere(),
                    ],
                    result: ast::Expression::IntLiteral(0).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
            attributes: ast::AttributeList(vec![]),
        }
        .nowhere();

        let expected_statements = vec![
            hir::Statement::PipelineRegMarker.nowhere(),
            hir::Statement::named_let(2, name_id(2, "a"), hir::ExprKind::IntLiteral(0).with_id(3))
                .nowhere(),
            hir::Statement::PipelineRegMarker.nowhere(),
            hir::Statement::named_let(
                4,
                name_id(3, "b"),
                hir::ExprKind::PipelineRef {
                    stage: 1usize.nowhere(),
                    name: name_id(2, "a"),
                    declares_name: false,
                }
                .idless(),
            )
            .nowhere(),
        ];

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(
            &input,
            &mut Context {
                symtab,
                idtracker,
                pipeline_ctx: None,
            },
        );

        assert_eq!(
            result
                .unwrap()
                .assume_pipeline()
                .body
                .assume_block()
                .statements,
            expected_statements
        );
    }

    #[test]
    fn absolute_stage_references_work() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 2.nowhere(),
            inputs: ast::ParameterList::without_self(vec![(
                ast_ident("clk"),
                ast::TypeSpec::Unit(().nowhere()).nowhere(),
            )])
            .nowhere(),
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            body: Some(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![
                        ast::Statement::PipelineRegMarker(1).nowhere(),
                        ast::Statement::Label(ast_ident("s")).nowhere(),
                        ast::Statement::Binding(
                            ast::Pattern::name("a"),
                            None,
                            ast::Expression::IntLiteral(0).nowhere(),
                        )
                        .nowhere(),
                        ast::Statement::PipelineRegMarker(1).nowhere(),
                        ast::Statement::Binding(
                            ast::Pattern::name("b"),
                            None,
                            ast::Expression::PipelineReference {
                                stage_kw_and_reference_loc: ().nowhere(),
                                stage: ast::PipelineStageReference::Absolute(ast_ident("s")),
                                name: ast_ident("a"),
                            }
                            .nowhere(),
                        )
                        .nowhere(),
                    ],
                    result: ast::Expression::IntLiteral(0).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
            attributes: ast::AttributeList(vec![]),
        }
        .nowhere();

        let expected_statements = vec![
            hir::Statement::PipelineRegMarker.nowhere(),
            hir::Statement::Label(ast_ident("s")).nowhere(),
            hir::Statement::named_let(2, name_id(2, "a"), hir::ExprKind::IntLiteral(0).with_id(3))
                .nowhere(),
            hir::Statement::PipelineRegMarker.nowhere(),
            hir::Statement::named_let(
                4,
                name_id(3, "b"),
                hir::ExprKind::PipelineRef {
                    stage: 1usize.nowhere(),
                    name: name_id(2, "a"),
                    declares_name: false,
                }
                .idless(),
            )
            .nowhere(),
        ];

        let mut symtab = SymbolTable::new();
        let idtracker = ExprIdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(
            &input,
            &mut Context {
                symtab,
                idtracker,
                pipeline_ctx: None,
            },
        );

        assert_eq!(
            result
                .unwrap()
                .assume_pipeline()
                .body
                .assume_block()
                .statements,
            expected_statements
        );
    }
}
