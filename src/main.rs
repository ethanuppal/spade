pub mod binding;
pub mod codegen;
pub mod constant;
pub mod error;
pub mod expression;
pub mod grammar;
pub mod identifier;
pub mod lexer;
pub mod parser;
pub mod types;

mod testcode;

fn main() {
    println!("Hello, world!");
}

/*
Language structure:

The language is expression based, there are no statements (probably)

Registers provide persistent storage of expressions
*/
