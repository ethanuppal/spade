use std::path::PathBuf;

use logos::Logos;
use spade_common::name::Path as SpadePath;
use spade_parser::{lexer, Parser};

#[derive(Clone, Debug)]
pub struct NamespacedFile {
    pub namespace: SpadePath,
    pub file: PathBuf,
}

/// Parses `a::b::c,test.spade` as `namespace: a::b::c, file: test.spade`
/// if no , is present, attempts to parse a path
/// if the part before the comma is present, attempts to parse it as a path using
/// the parser. If that fails an error is returned
pub fn namespaced_file(arg: &str) -> Result<NamespacedFile, String> {
    let parts = arg.split(",").collect::<Vec<_>>();

    match parts.len() {
        0 => Err(format!("Expected a string")),
        1 => Ok(NamespacedFile {
            file: arg.try_into().map_err(|e| format!("{e}"))?,
            namespace: SpadePath(vec![]),
        }),
        2 => {
            let mut parser = Parser::new(lexer::TokenKind::lexer(&parts[1]), 0);

            let namespace = parser.path().map_err(|e| format!("{e}"))?;

            Ok(NamespacedFile {
                file: arg.try_into().map_err(|e| format!("{e}"))?,
                namespace: namespace.inner,
            })
        }
        more => Err(format!(
            "Expected filename or path::to::module,filename. Got string with {more} commas"
        )),
    }
}
