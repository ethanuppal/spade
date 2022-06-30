use codespan_reporting::term::termcolor::Buffer;
use color_eyre::eyre::anyhow;
use logos::Logos;
use pyo3::prelude::*;

use spade::{lexer, CompilerState};
use spade_ast_lowering::id_tracker::ExprIdTracker;
use spade_common::{
    error_reporting::{CodeBundle, CompilationError},
    location_info::WithLocation,
};
use spade_hir::{symbol_table::FrozenSymtab, ItemList};
use spade_hir_lowering::{expr_to_mir, monomorphisation::MonoState, substitution::Substitutions};
use spade_parser::Parser;
use spade_typeinference::{GenericListSource, TypeState};

trait Reportable {
    type Inner;
    fn report_and_convert(
        self,
        error_buffer: &mut Buffer,
        code: &CodeBundle,
    ) -> PyResult<Self::Inner>;
}

impl<T, E> Reportable for Result<T, E>
where
    E: CompilationError,
{
    type Inner = T;
    fn report_and_convert(
        self,
        error_buffer: &mut Buffer,
        code: &CodeBundle,
    ) -> PyResult<Self::Inner> {
        match self {
            Ok(val) => Ok(val),
            Err(e) => {
                e.report(error_buffer, code);
                if !error_buffer.is_empty() {
                    println!("{}", String::from_utf8_lossy(error_buffer.as_slice()));
                }
                Err(anyhow!("Failed to compile spade").into())
            }
        }
    }
}

/// State which we need to modify later. Stored in an Option so we can
/// take ownership of temporarily
struct OwnedState {
    symtab: FrozenSymtab,
    idtracker: ExprIdTracker,
}

#[pyclass]
struct Spade {
    // state: CompilerState,
    code: CodeBundle,
    error_buffer: Buffer,
    owned: Option<OwnedState>,
    item_list: ItemList,
}

#[pymethods]
impl Spade {
    #[new]
    pub fn new(state_path: String) -> PyResult<Self> {
        let state_str = std::fs::read_to_string(state_path)?;
        let state = ron::from_str::<CompilerState>(&state_str)
            .map_err(|e| anyhow!("Failed to deserialize compiler state {e}"))?;

        Ok(Self {
            code: CodeBundle::from_files(&state.code),
            error_buffer: Buffer::ansi(),
            item_list: state.item_list,
            owned: Some(OwnedState {
                symtab: state.symtab,
                idtracker: state.idtracker,
            }),
        })
    }

    /// Compiles a spade constant expression into a bit vector
    pub fn e(&mut self, expr: String) -> PyResult<String> {
        let file_id = self.code.add_file("py".to_string(), expr.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&expr), file_id);

        // Parse the expression
        let ast = parser
            .expression()
            .report_and_convert(&mut self.error_buffer, &self.code)?;

        let OwnedState { symtab, idtracker } = self
            .owned
            .take()
            .expect("attempting to re-take owned state");

        let symtab = symtab.unfreeze();

        let mut ast_ctx = spade_ast_lowering::Context {
            symtab,
            idtracker,
            pipeline_ctx: None,
        };
        let hir = spade_ast_lowering::visit_expression(&ast, &mut ast_ctx)
            .report_and_convert(&mut self.error_buffer, &self.code)?
            .at_loc(&ast);

        let mut symtab = ast_ctx.symtab.freeze();

        let mut type_state = TypeState::new();
        let generic_list = type_state.create_generic_list(GenericListSource::Anonymous, &vec![]);
        // NOTE: We need to actually have the type information about what we're assigning to here
        // available
        type_state
            .visit_expression(&hir, &symtab.symtab(), &generic_list)
            .report_and_convert(&mut self.error_buffer, &self.code)?;

        let mut hir_ctx = spade_hir_lowering::Context {
            symtab: &mut symtab,
            idtracker: &mut ast_ctx.idtracker,
            types: &type_state,
            item_list: &self.item_list,
            // TODO: This will fail spectacularly if we try to instantiate polymorphic
            // functions. We should probably handle that gracefully
            mono_state: &mut MonoState::new(),
            subs: &mut Substitutions::new(),
        };

        let mir = expr_to_mir(hir, &mut hir_ctx)
            .report_and_convert(&mut self.error_buffer, &self.code)?;

        self.owned = Some(OwnedState {
            symtab,
            idtracker: ast_ctx.idtracker,
        });

        for stmt in mir {
            println!("{stmt}")
        }

        Ok("<done>".to_string())
    }
}

/// A Python module implemented in Rust.
#[pymodule]
fn spade(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Spade>()?;
    Ok(())
}
