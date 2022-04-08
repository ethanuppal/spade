use spade_ast as ast;
use spade_common::{
    id_tracker::ExprIdTracker,
    location_info::{Loc, WithLocation},
    name::Path,
};
use spade_hir as hir;

use crate::{
    error::{Error, Result},
    visit_expression, LocExt,
};
use spade_hir::symbol_table::SymbolTable;

pub fn pipeline_head(input: &ast::Pipeline, symtab: &mut SymbolTable) -> Result<hir::PipelineHead> {
    let depth = input.depth.map(|u| u as usize);

    // TODO: Support type params
    let type_params = vec![];

    let inputs = crate::visit_parameter_list(&input.inputs, symtab)?;

    let output_type = if let Some(output_type) = &input.output_type {
        Some(output_type.try_map_ref(|ty| super::visit_type_spec(ty, symtab))?)
    } else {
        None
    };

    Ok(hir::PipelineHead {
        depth,
        inputs,
        output_type,
        type_params,
    })
}

pub fn visit_pipeline(
    pipeline: &Loc<ast::Pipeline>,
    symtab: &mut SymbolTable,
    idtracker: &mut ExprIdTracker,
) -> Result<Option<Loc<hir::Pipeline>>> {
    let ast::Pipeline {
        depth,
        name: _,
        inputs: _,
        output_type: _,
        body,
        type_params: _,
    } = pipeline.inner.clone();

    symtab.new_scope();

    // TODO: We should probably unify this code with the entity code at some point
    let (id, head) = symtab
        .lookup_pipeline(&Path(vec![pipeline.name.clone()]).at_loc(&pipeline.name.loc()))
        .expect("Attempting to lower a pipeline that has not been added to the symtab previously");
    let head = head.clone(); // An offering to the borrow checker. May ferris have mercy on us all

    if head.inputs.0.is_empty() {
        return Err(Error::MissingPipelineClock { at_loc: head.loc() });
    }

    // If this is a builtin pipeline
    if pipeline.body.is_none() {
        return Ok(None);
    }

    // Add the inputs to the symtab
    let inputs = head
        .inputs
        .0
        .iter()
        .map(|(ident, ty)| (symtab.add_local_variable(ident.clone()), ty.clone()))
        .collect();

    let num_regs = body
        .as_ref()
        .unwrap()
        .assume_block()
        .statements
        .iter()
        .filter(|s| s.inner == ast::Statement::PipelineRegMarker)
        .count();

    if num_regs as u128 != depth.inner {
        return Err(Error::IncorrectStageCount {
            got: num_regs,
            expected: depth,
            pipeline: pipeline.clone(),
        });
    }

    let body = body
        .as_ref()
        .unwrap()
        .try_visit(visit_expression, symtab, idtracker)?;

    symtab.close_scope();

    Ok(Some(
        hir::Pipeline {
            head: head.inner,
            name: id.at_loc(&pipeline.name),
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
    use spade_common::location_info::WithLocation;

    use pretty_assertions::assert_eq;

    #[test]
    fn incorrect_stage_count_causes_error() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 3.nowhere(),
            inputs: ast::ParameterList(vec![(
                ast_ident("clk"),
                ast::TypeSpec::Unit(().nowhere()).nowhere(),
            )]),
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            body: Some(
                ast::Expression::Block(Box::new(ast::Block {
                    statements: vec![
                        ast::Statement::PipelineRegMarker.nowhere(),
                        ast::Statement::PipelineRegMarker.nowhere(),
                    ],
                    result: ast::Expression::IntLiteral(0).nowhere(),
                }))
                .nowhere(),
            ),
            type_params: vec![],
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut id_tracker = ExprIdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(&input, &mut symtab, &mut id_tracker);

        assert_eq!(
            result,
            Err(Error::IncorrectStageCount {
                got: 2,
                expected: 3.nowhere(),
                pipeline: input
            })
        );
    }

    #[test]
    fn pipeline_without_clock_is_an_error() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 2.nowhere(),
            inputs: ast::ParameterList(vec![]),
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            body: None,
            type_params: vec![],
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut id_tracker = ExprIdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(&input, &mut symtab, &mut id_tracker);

        assert_eq!(
            result,
            Err(Error::MissingPipelineClock {
                at_loc: ().nowhere()
            })
        );
    }
}
