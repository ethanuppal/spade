use std::ops::Deref;

use color_eyre::eyre::Context;
use color_eyre::eyre::Result;

struct CompilerState(spade::CompilerState);

impl CompilerState {
    fn list_names(&self) {
        for (from, to) in &self.name_source_map.inner {
            println!("{from} -> {to}")
        }
    }
}

impl Deref for CompilerState {
    type Target = spade::CompilerState;

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
    }
}

fn read_state(path: &str) -> Result<Box<CompilerState>> {
    let file = std::fs::read_to_string(path)
        .with_context(|| "Failed to read compiler state from {path}")?;

    Ok(Box::new(CompilerState(
        ron::from_str(&file).context("Failed to decode compiler state in {path}")?,
    )))
}
