use std::collections::HashSet;

use spade_ast as ast;
use spade_common::{
    id_tracker::IdTracker,
    location_info::{Loc, WithLocation},
    name::{NameID, Path},
};
use spade_hir as hir;

use crate::{
    error::{Error, Result},
    symbol_table::SymbolTableExt,
};
use crate::{symbol_table::SymbolTable, visit_type_spec, LocExt};

#[derive(Debug, Clone)]
pub struct PipelineState {
    pub return_expr: Option<Loc<hir::Expression>>,
    pub stage_count: usize,
    // List of pipeline registers
    pub regs: HashSet<NameID>,
}

impl PipelineState {
    pub fn new() -> Self {
        Self {
            stage_count: 0,
            regs: HashSet::new(),
            return_expr: None,
        }
    }

    pub fn is_reg(&self, name: &NameID) -> bool {
        self.regs.contains(name)
    }

    pub fn add_reg(&mut self, name: NameID) {
        self.regs.insert(name);
    }
}

pub fn pipeline_head(input: &ast::Pipeline, symtab: &mut SymbolTable) -> Result<hir::PipelineHead> {
    let depth = input.depth.map(|u| u as usize);

    let inputs = input
        .inputs
        .iter()
        .map(|(name, ty)| {
            Ok((
                name.clone(),
                ty.try_map_ref(|ty| super::visit_type_spec(ty, symtab))?,
            ))
        })
        .collect::<Result<Vec<_>>>()?;

    let output_type = if let Some(output_type) = &input.output_type {
        Some(output_type.try_map_ref(|ty| super::visit_type_spec(ty, symtab))?)
    } else {
        None
    };

    Ok(hir::PipelineHead {
        depth,
        inputs: hir::ParameterList(inputs),
        output_type,
    })
}

pub fn visit_pipeline_binding(
    binding: &ast::PipelineBinding,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
    pipeline_state: &mut PipelineState,
) -> Result<hir::PipelineBinding> {
    let ast::PipelineBinding {
        name,
        modifier,
        type_spec,
        value,
    } = &binding;

    let value = value.try_visit(super::visit_expression, symtab, idtracker)?;

    let type_spec = if let Some(type_spec) = type_spec {
        Some(type_spec.try_map_ref(|s| super::visit_type_spec(&s, symtab))?)
    } else {
        None
    };

    let name = if let Some(ast::PipelineBindModifier::Reg) = modifier.as_ref().map(|m| &m.inner) {
        let name = symtab.add_local_variable_at_offset(1, name.clone());
        pipeline_state.add_reg(name.clone());
        name
    } else {
        symtab.add_local_variable(name.clone())
    }
    .at_loc(name);

    Ok(hir::PipelineBinding {
        name,
        type_spec,
        value,
    })
}

pub fn visit_stage(
    stage: &ast::PipelineStage,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
    pipeline_state: &mut PipelineState,
) -> Result<hir::PipelineStage> {
    let ast::PipelineStage { bindings, result } = stage;

    symtab.new_scope();

    let bindings = bindings
        .iter()
        .map(|binding| {
            binding.try_map_ref(|b| visit_pipeline_binding(b, symtab, idtracker, pipeline_state))
        })
        .collect::<Result<Vec<_>>>()?;

    if let Some(result) = result {
        pipeline_state.return_expr =
            Some(result.try_visit(super::visit_expression, symtab, idtracker)?)
    }

    symtab.close_scope();

    Ok(hir::PipelineStage { bindings })
}

pub fn visit_pipeline(
    pipeline: &Loc<ast::Pipeline>,
    namespace: &Path,
    symtab: &mut SymbolTable,
    idtracker: &mut IdTracker,
) -> Result<Loc<hir::Pipeline>> {
    let ast::Pipeline {
        depth,
        name: _,
        inputs: _,
        output_type,
        stages,
    } = pipeline.inner.clone();

    symtab.new_scope();

    // TODO: We should probably unify this code with the entity code at some point
    let path = namespace.push_ident(pipeline.name.clone());
    let (id, head) = symtab
        .lookup_pipeline(&path.at_loc(&pipeline.name))
        .expect("Attempting to lower a pipeline that has not been added to the symtab previously");
    let head = head.clone(); // An offering to the borrow checker. May ferris have mercy on us all

    if head.inputs.0.is_empty() {
        return Err(Error::MissingPipelineClock { at_loc: head.loc() });
    }

    // Add the inputs to the symtab
    let inputs = head
        .inputs
        .0
        .iter()
        .map(|(ident, ty)| (symtab.add_local_variable(ident.clone()), ty.clone()))
        .collect();

    if stages.is_empty() {
        return Err(Error::NoPipelineStages {
            pipeline: pipeline.clone(),
        });
    }

    let mut state = PipelineState::new();
    let mut body = vec![];
    for (i, stage) in stages.iter().enumerate() {
        let stage = stage.try_map_ref(|s| visit_stage(s, symtab, idtracker, &mut state))?;

        // Check if we found an early return
        if let Some(expression) = &state.return_expr {
            if i != stages.len() - 1 {
                return Err(Error::EarlyPipelineReturn {
                    expression: expression.clone(),
                });
            }
        }

        body.push(stage);
    }

    if body.len() as u128 != depth.inner {
        return Err(Error::IncorrectStageCount {
            got: body.len(),
            expected: depth,
            pipeline: pipeline.clone(),
        });
    }

    let result = if let Some(result) = state.return_expr {
        result
    } else {
        return Err(Error::MissingPipelineReturn {
            in_stage: body.pop().unwrap(),
        });
    };

    let output_type = if let Some(t) = output_type {
        t.try_map_ref(|t| visit_type_spec(t, symtab))?
    } else {
        panic!("Pipelines returning unit type are unsupported")
    };

    symtab.close_scope();

    Ok(hir::Pipeline {
        depth,
        name: id.at_loc(&pipeline.name),
        output_type,
        inputs,
        body,
        result,
    }
    .at_loc(pipeline))
}

#[cfg(test)]
mod binding_visiting {
    use super::*;

    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;
    use spade_types::BaseType;

    #[test]
    fn local_pipeline_binding_visiting_works() {
        let input = ast::PipelineBinding {
            name: ast_ident("a"),
            modifier: None,
            type_spec: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            value: ast::Expression::Identifier(ast_path("b")).nowhere(),
        };

        let expected = hir::PipelineBinding {
            name: name_id(1, "a"),
            type_spec: Some(hir::TypeSpec::Unit(().nowhere()).nowhere()),
            value: hir::Expression::ident(0, 0, "b").nowhere(),
        };

        let mut symtab = SymbolTable::new();

        symtab.add_local_variable(ast_ident("b"));

        // Scope for the pipeline-visible items
        symtab.new_scope();
        // Scope for the local bindings
        symtab.new_scope();

        let mut id_tracker = IdTracker::new();
        let mut pipeline_state = PipelineState::new();

        let result =
            visit_pipeline_binding(&input, &mut symtab, &mut id_tracker, &mut pipeline_state);

        assert_eq!(result, Ok(expected));

        assert!(
            symtab.has_symbol(ast_path("a").inner),
            "Local name was not added correctly"
        );
        // Ensure that the binding was added to the corect scope
        symtab.close_scope();
        assert!(
            !symtab.has_symbol(ast_path("a").inner),
            "Local name was added to the wrong scope"
        );
        assert!(!pipeline_state.is_reg(&name_id(1, "a").inner))
    }

    #[test]
    fn reg_pipeline_binding_visiting_works() {
        let input = ast::PipelineBinding {
            name: ast_ident("a"),
            modifier: Some(ast::PipelineBindModifier::Reg.nowhere()),
            type_spec: None,
            value: ast::Expression::Identifier(ast_path("b")).nowhere(),
        };

        let expected = hir::PipelineBinding {
            name: name_id(1, "a"),
            type_spec: None,
            value: hir::Expression::ident(0, 0, "b").nowhere(),
        };

        let mut symtab = SymbolTable::new();

        symtab.add_local_variable(ast_ident("b"));

        // Scope for the pipeline-visible items
        symtab.new_scope();
        // Scope for the local bindings
        symtab.new_scope();

        let mut id_tracker = IdTracker::new();
        let mut pipeline_state = PipelineState::new();

        let result =
            visit_pipeline_binding(&input, &mut symtab, &mut id_tracker, &mut pipeline_state);

        assert_eq!(result, Ok(expected));

        // Ensure that the binding was added to the corect scope
        symtab.close_scope();
        assert!(
            symtab.has_symbol(ast_path("a").inner),
            "Reg name was not added correctly"
        );
        // Ensure that the variable is marked as a pipeline variable
        assert!(pipeline_state.is_reg(&name_id(1, "a").inner))
    }
}

#[cfg(test)]
mod stage_visiting {
    use super::*;

    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    #[test]
    fn stage_visiting_works() {
        let input = ast::PipelineStage {
            bindings: vec![
                ast::PipelineBinding {
                    name: ast_ident("a"),
                    modifier: Some(ast::PipelineBindModifier::Reg.nowhere()),
                    type_spec: None,
                    value: ast::Expression::IntLiteral(0).nowhere(),
                }
                .nowhere(),
                ast::PipelineBinding {
                    name: ast_ident("b"),
                    modifier: None,
                    type_spec: None,
                    value: ast::Expression::IntLiteral(0).nowhere(),
                }
                .nowhere(),
            ],
            result: Some(ast::Expression::Identifier(ast_path("b")).nowhere()),
        };

        let expected = hir::PipelineStage {
            bindings: vec![
                hir::PipelineBinding {
                    name: name_id(0, "a"),
                    type_spec: None,
                    value: hir::ExprKind::IntLiteral(0).with_id(0).nowhere(),
                }
                .nowhere(),
                hir::PipelineBinding {
                    name: name_id(1, "b"),
                    type_spec: None,
                    value: hir::ExprKind::IntLiteral(0).with_id(1).nowhere(),
                }
                .nowhere(),
            ],
        };

        let mut symtab = SymbolTable::new();

        // Scope for the pipeline-visible items
        symtab.new_scope();

        let mut id_tracker = IdTracker::new();
        let mut pipeline_state = PipelineState::new();

        let result = visit_stage(&input, &mut symtab, &mut id_tracker, &mut pipeline_state);

        assert_eq!(result, Ok(expected));

        // Ensure that the binding was added to the corect scope
        assert!(
            symtab.has_symbol(ast_path("a").inner),
            "Reg name was not added correctly"
        );
        // And that local names are not visible
        assert!(
            !symtab.has_symbol(ast_path("b").inner),
            "Local reg was incorrectly visible to the outside world"
        );

        // And that the return value of the pipeline state was updated
        assert_eq!(
            pipeline_state.return_expr,
            Some(hir::Expression::ident(2, 1, "b").nowhere())
        );
    }
}

#[cfg(test)]
mod pipeline_visiting {
    use super::*;

    use spade_ast::testutil::{ast_ident, ast_path};
    use spade_common::location_info::WithLocation;
    use spade_common::name::testutil::name_id;

    use pretty_assertions::assert_eq;

    #[test]
    fn correct_pipeline_works() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 2.nowhere(),
            inputs: vec![
                (
                    ast_ident("clk"),
                    ast::TypeSpec::Unit(().nowhere()).nowhere(),
                ),
                (ast_ident("in"), ast::TypeSpec::Unit(().nowhere()).nowhere()),
            ],
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            stages: vec![
                ast::PipelineStage {
                    bindings: vec![ast::PipelineBinding {
                        name: ast_ident("a"),
                        modifier: Some(ast::PipelineBindModifier::Reg.nowhere()),
                        type_spec: None,
                        value: ast::Expression::IntLiteral(0).nowhere(),
                    }
                    .nowhere()],
                    result: None,
                }
                .nowhere(),
                ast::PipelineStage {
                    bindings: vec![],
                    result: Some(ast::Expression::Identifier(ast_path("a")).nowhere()),
                }
                .nowhere(),
            ],
        }
        .nowhere();

        let expected = hir::Pipeline {
            name: name_id(0, "pipe"),
            inputs: vec![
                (name_id(1, "clk").inner, hir::TypeSpec::unit().nowhere()),
                (name_id(2, "in").inner, hir::TypeSpec::unit().nowhere()),
            ],
            body: vec![
                hir::PipelineStage {
                    bindings: vec![hir::PipelineBinding {
                        name: name_id(3, "a"),
                        type_spec: None,
                        value: hir::ExprKind::IntLiteral(0).with_id(0).nowhere(),
                    }
                    .nowhere()],
                }
                .nowhere(),
                hir::PipelineStage { bindings: vec![] }.nowhere(),
            ],
            output_type: hir::TypeSpec::unit().nowhere(),
            result: hir::Expression::ident(0, 3, "a").nowhere(),
            depth: 2.nowhere(),
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut id_tracker = IdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &Path(vec![]), &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(&input, &Path(vec![]), &mut symtab, &mut id_tracker);

        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn incorrect_stage_count_causes_error() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 3.nowhere(),
            inputs: vec![(
                ast_ident("clk"),
                ast::TypeSpec::Unit(().nowhere()).nowhere(),
            )],
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            stages: vec![
                ast::PipelineStage {
                    bindings: vec![],
                    result: None,
                }
                .nowhere(),
                ast::PipelineStage {
                    bindings: vec![],
                    result: Some(ast::Expression::IntLiteral(0).nowhere()),
                }
                .nowhere(),
            ],
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut id_tracker = IdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &Path(vec![]), &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(&input, &Path(vec![]), &mut symtab, &mut id_tracker);

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
    fn early_return_causes_error() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 2.nowhere(),
            inputs: vec![(
                ast_ident("clk"),
                ast::TypeSpec::Unit(().nowhere()).nowhere(),
            )],
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            stages: vec![
                ast::PipelineStage {
                    bindings: vec![],
                    result: Some(ast::Expression::IntLiteral(0).nowhere()),
                }
                .nowhere(),
                ast::PipelineStage {
                    bindings: vec![],
                    result: Some(ast::Expression::IntLiteral(1).nowhere()),
                }
                .nowhere(),
            ],
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut id_tracker = IdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &Path(vec![]), &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(&input, &Path(vec![]), &mut symtab, &mut id_tracker);

        assert_eq!(
            result,
            Err(Error::EarlyPipelineReturn {
                expression: hir::ExprKind::IntLiteral(0).with_id(0).nowhere()
            })
        );
    }

    #[test]
    fn pipeline_without_stages_is_invalid() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 0.nowhere(),
            inputs: vec![(
                ast_ident("clk"),
                ast::TypeSpec::Unit(().nowhere()).nowhere(),
            )],
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            stages: vec![],
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut id_tracker = IdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &Path(vec![]), &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(&input, &Path(vec![]), &mut symtab, &mut id_tracker);

        assert_eq!(result, Err(Error::NoPipelineStages { pipeline: input }));
    }

    #[test]
    fn pipeline_without_clock_is_an_error() {
        let input = ast::Pipeline {
            name: ast_ident("pipe"),
            depth: 2.nowhere(),
            inputs: vec![],
            output_type: Some(ast::TypeSpec::Unit(().nowhere()).nowhere()),
            stages: vec![
                ast::PipelineStage {
                    bindings: vec![],
                    result: None,
                }
                .nowhere(),
                ast::PipelineStage {
                    bindings: vec![],
                    result: Some(ast::Expression::IntLiteral(0).nowhere()),
                }
                .nowhere(),
            ],
        }
        .nowhere();

        let mut symtab = SymbolTable::new();
        let mut id_tracker = IdTracker::new();

        crate::global_symbols::visit_pipeline(&input, &Path(vec![]), &mut symtab)
            .expect("Failed to add pipeline to symtab");

        let result = visit_pipeline(&input, &Path(vec![]), &mut symtab, &mut id_tracker);

        assert_eq!(
            result,
            Err(Error::MissingPipelineClock {
                at_loc: ().nowhere()
            })
        );
    }
}
