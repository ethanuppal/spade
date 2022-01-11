use std::sync::RwLock;

use colored::*;

use crate::equation::{FreeTypeVar, TypedExpression};

pub struct TraceStack {
    entries: RwLock<Vec<TraceStackEntry>>,
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
    TryingUnify(FreeTypeVar, FreeTypeVar),
    /// Unified .0 with .1 producing .2
    Unified(FreeTypeVar, FreeTypeVar, FreeTypeVar),
    AddingEquation(TypedExpression, FreeTypeVar),
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
                format!("{} {} <- {}", "eq".yellow(), expr, t)
            }
            TraceStackEntry::Unified(lhs, rhs, result) => {
                format!("{} {}, {} -> {}", "unified".green(), lhs, rhs, result)
            }
            TraceStackEntry::TryingUnify(lhs, rhs) => {
                format!("{} of {} with {}", "trying unification".cyan(), lhs, rhs)
            }
            TraceStackEntry::Message(msg) => {
                format!("{}: {}", "m".purple(), msg)
            }
            TraceStackEntry::Exit => {
                next_indent_amount -= 1;
                format!("")
            }
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
