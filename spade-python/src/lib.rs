use std::collections::HashMap;

use codespan_reporting::term::termcolor::Buffer;
use color_eyre::eyre::{anyhow, Context};
use logos::Logos;
use pyo3::prelude::*;

use spade::{lexer, CompilerState};
use spade_ast_lowering::id_tracker::ExprIdTracker;
use spade_common::name::Path as SpadePath;
use spade_common::{
    error_reporting::{CodeBundle, CompilationError},
    location_info::{Loc, WithLocation},
};
use spade_hir::symbol_table::{LookupError, SymbolTable};
use spade_hir::TypeSpec;
use spade_hir::{symbol_table::FrozenSymtab, FunctionLike, ItemList};
use spade_hir_lowering::{expr_to_mir, monomorphisation::MonoState, substitution::Substitutions};
use spade_mir::codegen::mangle_input;
use spade_mir::eval::eval_statements;
use spade_parser::Parser;
use spade_typeinference::{GenericListSource, TypeState};
use spade_types::ConcreteType;
use vcd_translate::translation::{self, inner_translate_value};

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

#[pyclass]
#[derive(PartialEq, Eq, Clone)]
struct BitString(pub String);

#[pymethods]
impl BitString {
    fn inner(&self) -> &String {
        &self.0
    }
}

#[pyclass]
struct SpadeType(pub TypeSpec);

#[pyclass]
struct TypedValue {
    pub ty: TypeSpec,
    pub val: BitString,
}


/// State which we need to modify later. Stored in an Option so we can
/// take ownership of temporarily
struct OwnedState {
    symtab: FrozenSymtab,
    idtracker: ExprIdTracker,
}

#[pyclass]
struct ComparisonResult {
    #[pyo3(get)]
    pub expected_spade: String,
    #[pyo3(get)]
    pub expected_bits: BitString,
    #[pyo3(get)]
    pub got_spade: String,
    #[pyo3(get)]
    pub got_bits: BitString
}

#[pyclass(subclass)]
struct Spade {
    // state: CompilerState,
    code: CodeBundle,
    error_buffer: Buffer,
    owned: Option<OwnedState>,
    item_list: ItemList,
    uut: Loc<SpadePath>,
}

#[pymethods]
impl Spade {
    #[new]
    pub fn new(uut_name: String, state_path: String) -> PyResult<Self> {
        let state_str = std::fs::read_to_string(&state_path)
            .with_context(|| format!("Failed to read state file at {state_path}"))?;
        let state = ron::from_str::<CompilerState>(&state_str)
            .map_err(|e| anyhow!("Failed to deserialize compiler state {e}"))?;

        let mut code = CodeBundle::from_files(&state.code);
        let mut error_buffer = Buffer::ansi();

        let file_id = code.add_file("dut".to_string(), uut_name.clone());
        let mut parser = Parser::new(lexer::TokenKind::lexer(&uut_name), file_id);
        let uut = parser.path().report_and_convert(&mut error_buffer, &code)?;

        // TODO: Ensure that the uut name matches the DUT by looking at the name
        // property of the DUT

        Ok(Self {
            uut,
            code,
            error_buffer,
            item_list: state.item_list,
            owned: Some(OwnedState {
                symtab: state.symtab,
                idtracker: state.idtracker,
            }),
        })
    }

    /// Computes expr as a value for port. If the type of expr does not match the expected an error
    /// is returned. Likewise if uut does not have such a port.
    ///
    /// The returned value is the name of the port in the verilog, and the value
    fn port_value(&mut self, port: &str, expr: &str) -> PyResult<(String, BitString)> {
        let (port_name, port_ty) = self.get_port(port.into())?;

        let val = self.compile_expr(expr, port_ty)?;
        Ok((port_name, val))
    }

    fn compare_values(&mut self, val: &TypedValue, expr: &str) -> PyResult<ComparisonResult> {
        let spade_bits = self.compile_expr(expr, val.ty.clone())?;

        let concrete_ty = TypeState::type_spec_to_concrete(&val.ty, &self.item_list.types, &HashMap::new());

        Ok(ComparisonResult {
            expected_spade: expr.to_string(),
            expected_bits: spade_bits,
            got_spade: val_to_spade(&val.val, concrete_ty),
            got_bits: val.val.clone()
        })
    }

    /// Interprets `val` as the output value of DUT and returns the corresponding TypedValue
    fn output_value(&mut self, val: &str) -> PyResult<TypedValue> {
        let ty = self.output_type()?;
        Ok(TypedValue {
            ty,
            val: BitString(val.to_string())
        })
    }

    // /// Interprets the output value `val` as the output of `uut`, returning the
    // /// resulting spade value string
    // fn translate_value(&mut self, val: &TypedValue) -> PyResult<String> {
    //     Ok(val_to_spade(
    //         val,
    //         TypeState::type_spec_to_concrete(&ty, &self.item_list.types, &HashMap::new()),
    //     ))
    // }

    // /// 
    // pub fn value_as_output_type(&mut self, expr: &str) -> PyResult<TypedValue> {
    //     let ty = self.output_type()?;

    //     Ok(TypedValue {
    //         ty: TypeState::type_spec_to_concrete(&ty, &self.item_list.types, &HashMap::new()),
    //         val: self.compile_expr(expr, ty)?
    //     })
    // }
    // fn has_field()
}

impl Spade {
    fn lookup_function_like(
        name: &Loc<SpadePath>,
        symtab: &SymbolTable,
    ) -> Result<Box<dyn FunctionLike>, LookupError> {
        if let Ok(e) = symtab.lookup_entity(name) {
            Ok(Box::new(e.1.inner))
        } else if let Ok(f) = symtab.lookup_function(name) {
            Ok(Box::new(f.1.inner))
        } else {
            let p = symtab.lookup_pipeline(name)?;
            Ok(Box::new(p.1.inner))
        }
    }

    /// Tries to get the type and the name of the port in the generated verilog of the specified
    /// input port
    fn get_port(&mut self, port: String) -> PyResult<(String, TypeSpec)> {
        let owned = self.owned.as_ref().unwrap();
        let symtab = owned.symtab.symtab();
        let head = Self::lookup_function_like(&self.uut, &symtab)
            .report_and_convert(&mut self.error_buffer, &self.code)?;

        for (name, ty) in &head.inputs().0 {
            if port == name.0 {
                return Ok((mangle_input(&port), ty.inner.clone()));
            }
        }

        Err(anyhow!("{port} is not a port of {}", self.uut).into())
    }

    /// Evaluates the provided expression as the specified type and returns the result
    /// as a string of 01xz
    pub fn compile_expr(&mut self, expr: &str, type_spec: TypeSpec) -> PyResult<BitString> {
        let file_id = self.code.add_file("py".to_string(), expr.into());
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

        let ty = type_state.type_var_from_hir(&type_spec, &generic_list);
        type_state
            .unify_expression_generic_error(&hir, &ty, &symtab.symtab())
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

        Ok(BitString(eval_statements(&mir).as_string()))
    }

    /// Return the output type of uut
    fn output_type(&mut self) -> PyResult<TypeSpec> {
        let owned = self.owned.as_ref().unwrap();
        let symtab = owned.symtab.symtab();

        let ty = Self::lookup_function_like(&self.uut, symtab)
            .report_and_convert(&mut self.error_buffer, &self.code)?
            .output_type()
            .clone()
            .ok_or_else(|| anyhow!("{} does not have an output type", self.uut))?;

        Ok(ty.inner)
    }
}

// TODO: Move this into the symtab

fn val_to_spade(val: &BitString, ty: ConcreteType) -> String {
    let val_vcd = translation::value_from_str(&val.0);
    let mut result = String::new();
    inner_translate_value(&mut result, &val_vcd, &ty);
    result
}

/// A Python module implemented in Rust.
#[pymodule]
fn spade(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Spade>()?;
    m.add_class::<BitString>()?;
    m.add_class::<SpadeType>()?;
    m.add_class::<TypedValue>()?;
    m.add_class::<ComparisonResult>()?;
    Ok(())
}
