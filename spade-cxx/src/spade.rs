use std::ops::Deref;

use color_eyre::eyre::Context;
use color_eyre::eyre::Result;

struct CompilerState(pub spade::compiler_state::CompilerState);

impl CompilerState {
    fn list_names(&self) {
        for (from, to) in &self.name_source_map.inner {
            println!("{from} -> {to}")
        }
    }

    fn demangle_name(&self, name: &str) -> String {
        self.0
            .demangle_string(name)
            .unwrap_or(format!("(not demangled) {name}"))
    }
}

fn read_state(path: &str) -> Result<Box<CompilerState>> {
    let file = std::fs::read_to_string(path)
        .with_context(|| "Failed to read compiler state from {path}")?;

    let ron = ron::Options::default().without_recursion_limit();
    Ok(Box::new(CompilerState(
        ron.from_str(&file)
            .context("Failed to decode compiler state in {path}")?,
    )))
}

impl Deref for CompilerState {
    type Target = spade::compiler_state::CompilerState;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

struct SignalValue(pub spade_mir::eval::Value);

impl SignalValue {
    fn as_u64(&self) -> u64 {
        self.0.as_u64()
    }

    fn as_u32_chunks(&self) -> Vec<u32> {
        self.0.as_u32_chunks().to_u32_digits()
    }
}

struct SimulationExt(pub spade_simulation_ext::Spade);
struct BitString(spade_simulation_ext::BitString);
struct ComparisonResult(spade_simulation_ext::ComparisonResult);
struct FieldRef(spade_simulation_ext::FieldRef);

fn setup_spade(uut_name: String, state_path: String) -> Result<Box<SimulationExt>> {
    Ok(Box::new(SimulationExt(spade_simulation_ext::Spade::new(
        uut_name, state_path,
    )?)))
}

impl SimulationExt {
    pub fn port_value(&mut self, port: &str, expr: &str) -> Result<Box<SignalValue>> {
        self.0
            .port_value_raw(port, expr)
            .map(|(_, value)| Box::new(SignalValue(value)))
    }

    pub fn compare_field(
        &mut self,
        // The field to compare
        field: Box<FieldRef>,
        // The spade expression to compare against
        spade_expr: &str,
        // The bits of the whole output struct
        output_bits: &BitString,
    ) -> Result<Box<ComparisonResult>> {
        self.0
            .compare_field(field.0, spade_expr, &output_bits.0)
            .map(|o| Box::new(ComparisonResult(o)))
    }
}

#[cxx::bridge(namespace = "spade")]
mod ffi {

    extern "Rust" {
        type FieldRef;
        type BitString;
        type ComparisonResult;
    }

    extern "Rust" {
        type SignalValue;

        fn as_u64(&self) -> u64;
        fn as_u32_chunks(&self) -> Vec<u32>;
    }

    extern "Rust" {
        type CompilerState;

        fn read_state(path: &str) -> Result<Box<CompilerState>>;
        fn list_names(&self);
        fn demangle_name(&self, name: &str) -> String;
    }

    extern "Rust" {
        type SimulationExt;

        fn setup_spade(uut_name: String, state_path: String) -> Result<Box<SimulationExt>>;
        fn port_value(&mut self, port: &str, expr: &str) -> Result<Box<SignalValue>>;
        pub fn compare_field(
            &mut self,
            // The field to compare
            field: Box<FieldRef>,
            // The spade expression to compare against
            spade_expr: &str,
            // The bits of the whole output struct
            output_bits: &BitString,
        ) -> Result<Box<ComparisonResult>>;

    }
}
