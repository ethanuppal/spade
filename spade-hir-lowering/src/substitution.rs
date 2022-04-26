use std::collections::HashMap;

use spade_common::{
    location_info::WithLocation,
    name::{Identifier, NameID},
};
use spade_hir::symbol_table::FrozenSymtab;

#[derive(Clone)]
pub enum Substitution {
    Undefined,
    /// The variable will not be available for another `n` cycles. When available,
    /// the variable name will be `NameID`
    Waiting(usize, NameID),
    /// The value is availalbe now and the true name is `NameID`
    Available(NameID),
}

pub struct SubRegister {
    pub original: NameID,
    pub previous: NameID,
    pub new: NameID,
}

/// List of substitutions for variables in pipelines. Contains substitutions for a
/// all variables present in the top scope of the pipeline
#[derive(Clone)]
pub struct Substitutions {
    /// A mapping of names to their corresponding registers at each pipeline
    /// stage.
    inner: Vec<HashMap<NameID, Substitution>>,
    live_vars: Vec<NameID>,

    /// The stage we are currently lowering
    pub current_stage: usize,
}

impl Substitutions {
    pub fn new() -> Self {
        Self {
            inner: vec![HashMap::new()],
            live_vars: vec![],
            current_stage: 0,
        }
    }

    /// Advance to tracking the next pipeline stage. Adds aliases for all variables in
    /// the current stage and returns a list of pipeline registers to insert
    pub fn next_stage(&mut self, symtab: &mut FrozenSymtab) -> Vec<SubRegister> {
        let stage_num = self.inner.len();
        let mut result = vec![];
        let mut new_subs = HashMap::new();
        for original in &self.live_vars {
            let sub = &self.inner.last().unwrap()[&original];
            let new_sub = match sub {
                Substitution::Undefined => {
                    unreachable!("Undefined substitutions should not be in the substitution map")
                }
                // The name of the value in the first stage at which it is avilable will
                // be the original name
                Substitution::Waiting(0, name) => Substitution::Available(name.clone()),
                Substitution::Waiting(time_left, name) => {
                    Substitution::Waiting(time_left - 1, name.clone())
                }
                Substitution::Available(previous) => {
                    let mut new_path = original.1.clone();
                    // Insert the stage marker before the final name to improve order
                    // of names in the vcd dump
                    // FIXME: instead of s{num}, replace it by label if a label
                    // is present
                    // spade#128
                    new_path.0.insert(
                        new_path.0.len() - 1,
                        Identifier(format!("s{}", stage_num)).nowhere(),
                    );
                    let new_name = symtab.new_name(new_path);
                    result.push(SubRegister {
                        original: original.clone(),
                        previous: previous.clone(),
                        new: new_name.clone(),
                    });
                    Substitution::Available(new_name)
                }
            };
            new_subs.insert(original.clone(), new_sub);
        }
        self.inner.push(new_subs);

        result
    }

    /// Mark the variable as available in the current pipeline stage under its
    /// own name
    pub fn set_available(&mut self, from: NameID) {
        self.live_vars.push(from.clone());
        self.inner
            .last_mut()
            .unwrap()
            .insert(from.clone(), Substitution::Available(from.clone()));
    }

    /// Return substituted name for `original` in the current pipeline stage
    /// if there is a substitution for it, otherwise return the name itself
    pub fn lookup(&self, original: &NameID) -> Substitution {
        self.inner[self.current_stage]
            .get(original)
            .cloned()
            .unwrap_or(Substitution::Available(original.clone()))
    }

    /// Look up a pipeline reference in an absolute stage. Returns
    /// Undefined if there is no such name in that stage.
    pub fn lookup_referenced(&self, in_stage: usize, original: &NameID) -> Substitution {
        self.inner[in_stage]
            .get(&original)
            .cloned()
            .unwrap_or(Substitution::Undefined)
    }
}
