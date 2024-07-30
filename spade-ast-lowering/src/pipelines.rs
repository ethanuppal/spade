use hir::symbol_table::TypeSymbol;
use spade_ast as ast;
use spade_common::location_info::WithLocation;
use spade_common::{location_info::Loc, name::Path};
use spade_diagnostics::Diagnostic;
use spade_hir as hir;

use crate::{comptime::ComptimeCondExt, error::Result, Context};

pub struct PipelineContext {
    /// Scope of the pipeline body
    pub scope: usize,
}

fn visit_pipeline_statement(statement: &ast::Statement, ctx: &mut Context) -> Result<()> {
    match &statement {
        ast::Statement::Label(name) => {
            ctx.symtab.add_unique_type(
                Path::ident(name.clone()).at_loc(name),
                TypeSymbol::GenericInt.at_loc(name),
            )?;
        }
        ast::Statement::Declaration(_) => {}
        ast::Statement::Binding(_) => {}
        ast::Statement::PipelineRegMarker(_, _) => {}
        ast::Statement::Register(_) => {}
        ast::Statement::Assert(_) => {}
        ast::Statement::Comptime(inner) => {
            if let Some(inner_stmts) = inner.maybe_unpack(&ctx.symtab)? {
                for inner_stmt in inner_stmts {
                    visit_pipeline_statement(&inner_stmt, ctx)?;
                }
            }
        }
        ast::Statement::Set { .. } => {}
    };
    Ok(())
}

/// Performs the pipelining tasks we need to do before visiting staements during
/// ast lowering. In particular, this adds type symbols for each pipeline stage
pub fn maybe_perform_pipelining_tasks(
    unit: &Loc<ast::Unit>,
    head: &Loc<hir::UnitHead>,
    ctx: &mut Context,
) -> Result<Option<PipelineContext>> {
    let ast::Unit {
        head:
            ast::UnitHead {
                unit_kind,
                inputs: ast_inputs,
                ..
            },
        body,
    } = &unit.inner;

    match &unit_kind.inner {
        ast::UnitKind::Function => Ok(None),
        ast::UnitKind::Entity => Ok(None),
        ast::UnitKind::Pipeline(_) => {
            let context = PipelineContext {
                scope: ctx.symtab.current_scope() + 1,
            };

            if head.inputs.0.is_empty() {
                return Err(Diagnostic::error(
                    ast_inputs.loc(),
                    "Missing clock argument for pipeline",
                )
                .note("All pipelines need to take at least a clock as an argument"));
            }

            for statement in &body.as_ref().unwrap().assume_block().statements {
                visit_pipeline_statement(statement, ctx)?;
            }

            Ok(Some(context))
        }
    }
}
