use std::sync::RwLock;

use colored::*;
use itertools::Itertools;
use num::BigInt;

use crate::{
    equation::{TypeVar, TypedExpression},
    requirements::Requirement,
};

pub struct TraceStack {
    entries: RwLock<Vec<TraceStackEntry>>,
}

impl Default for TraceStack {
    fn default() -> Self {
        Self::new()
    }
}

impl TraceStack {
    pub fn new() -> Self {
        Self {
            entries: RwLock::new(vec![]),
        }
    }
    pub fn push(&self, entry: TraceStackEntry) {
        self.entries.write().unwrap().push(entry)
    }
}

pub enum TraceStackEntry {
    /// Entering the specified visitor
    Enter(String),
    /// Exited the most recent visitor and the node had the specified type
    Exit,
    TryingUnify(TypeVar, TypeVar),
    /// Unified .0 with .1 producing .2. .3 were replaced
    Unified(TypeVar, TypeVar, TypeVar, Vec<TypeVar>),
    AddingEquation(TypedExpression, TypeVar),
    AddRequirement(Requirement),
    ResolvedRequirement(Requirement),
    /// Inferring more from constraints
    InferringFromConstraints(TypeVar, BigInt),
    /// Arbitrary message
    Message(String),
}

pub fn format_trace_stack(stack: &TraceStack) -> String {
    let mut result = String::new();
    let mut indent_amount = 0;

    for entry in stack.entries.read().unwrap().iter() {
        let mut next_indent_amount = indent_amount;
        let message = match entry {
            TraceStackEntry::Enter(function) => {
                next_indent_amount += 1;
                format!("{} `{}`", "call".white(), function.blue())
            }
            TraceStackEntry::AddingEquation(expr, t) => {
                format!("{} {:?} <- {:?}", "eq".yellow(), expr, t)
            }
            TraceStackEntry::Unified(lhs, rhs, result, replaced) => {
                next_indent_amount -= 1;
                format!(
                    "{} {:?}, {:?} -> {:?} (replacing {})",
                    "unified".green(),
                    lhs,
                    rhs,
                    result,
                    replaced.iter().map(|t| format!("{t:?}")).join(",")
                )
            }
            TraceStackEntry::TryingUnify(lhs, rhs) => {
                next_indent_amount += 1;
                format!(
                    "{} of {:?} with {:?}",
                    "trying unification".cyan(),
                    lhs,
                    rhs
                )
            }
            TraceStackEntry::InferringFromConstraints(lhs, rhs) => {
                format!("{} {lhs} as {rhs} from constraints", "inferring".purple())
            }
            TraceStackEntry::Message(msg) => {
                format!("{}: {}", "m".purple(), msg)
            }
            TraceStackEntry::Exit => {
                next_indent_amount -= 1;
                String::new()
            }
            TraceStackEntry::AddRequirement(req) => format!("{} {req:?}", "added".yellow()),
            TraceStackEntry::ResolvedRequirement(req) => format!("{} {req:?}", "resolved".blue()),
        };
        if let TraceStackEntry::Exit = entry {
        } else {
            for _ in 0..indent_amount {
                result += "| ";
            }
            result += &message;
            result += "\n";
        }
        indent_amount = next_indent_amount;
    }
    result
}
