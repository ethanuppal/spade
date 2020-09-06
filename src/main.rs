pub mod ast;
pub mod binding;
pub mod codegen;
pub mod constant;
pub mod error;
pub mod expression;
pub mod identifier;
pub mod lexer;
pub mod location_info;
pub mod parser;
pub mod types;

mod testcode;

fn main() {
    println!("Hello, world!");
}
