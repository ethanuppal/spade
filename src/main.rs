pub mod binding;
pub mod codegen;
pub mod constant;
pub mod expression;
pub mod identifier;
pub mod types;
pub mod error;
pub mod grammar;
pub mod lexer;
pub mod parser;

mod testcode;

fn main() {
    println!("Hello, world!");
}

/*
Language structure:

The language is expression based, there are no statements (probably)

Registers provide persistent storage of expressions
*/
