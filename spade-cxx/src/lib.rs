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

impl Deref for CompilerState {
    type Target = spade::compiler_state::CompilerState;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cxx::bridge]
mod ffi {
    extern "Rust" {
        type CompilerState;

        fn read_state(path: &str) -> Result<Box<CompilerState>>;
        fn list_names(&self);
        fn demangle_name(&self, name: &str) -> String;
    }
}

fn read_state(path: &str) -> Result<Box<CompilerState>> {
    let file = std::fs::read_to_string(path)
        .with_context(|| "Failed to read compiler state from {path}")?;

    Ok(Box::new(CompilerState(
        ron::from_str(&file).context("Failed to decode compiler state in {path}")?,
    )))
}
