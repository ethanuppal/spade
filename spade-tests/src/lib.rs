use codespan_reporting::term::termcolor::Buffer;
use std::io::Write;

use spade_common::error_reporting::{CodeBundle, CompilationError};

#[cfg(test)]
mod ast_lowering;
#[cfg(test)]
mod hir_lowering;
#[cfg(test)]
mod integration;
#[cfg(test)]
mod parser;
#[cfg(test)]
mod suggestions;
#[cfg(test)]
mod typeinference;
mod usefulness;

pub trait ResultExt<T> {
    fn report_failure(self, code: &str) -> T;
}
impl<T> ResultExt<T> for spade_hir_lowering::error::Result<T> {
    fn report_failure(self, code: &str) -> T {
        match self {
            Ok(t) => t,
            Err(e) => {
                let code_bundle = CodeBundle::new(code.to_string());
                let mut buffer = Buffer::no_color();
                e.report(&mut buffer, &code_bundle);
                std::io::stderr().write_all(buffer.as_slice()).unwrap();
                panic!("Compilation error")
            }
        }
    }
}

#[macro_export]
#[cfg(test)]
macro_rules! build_entity {
    ($code:expr) => {{
        match build_items($code).as_slice() {
            [] => panic!("Found no entities"),
            [e] => e.clone(),
            _ => panic!("Found more than one entity"),
        }
    }};
}

#[macro_export]
macro_rules! snapshot_error {
    ($fn:ident, $src:literal) => {
        #[test]
        fn $fn() {
            let source = unindent::unindent($src);
            let mut buffer = codespan_reporting::term::termcolor::Buffer::no_color();
            let opts = spade::Opt {
                error_buffer: &mut buffer,
                outfile: None,
                mir_output: None,
                type_dump_file: None,
                print_type_traceback: false,
                print_parse_traceback: false,
            };

            let _ = spade::compile(
                vec![(
                    spade::ModuleNamespace {
                        namespace: spade_common::name::Path(vec![]),
                        base_namespace: spade_common::name::Path(vec![]),
                    },
                    "testinput".to_string(),
                    source.to_string(),
                )],
                opts,
            );

            insta::assert_snapshot!(
                std::str::from_utf8(buffer.as_slice()).expect("error contains invalid utf-8")
            );
        }
    };
}

/// Builds mutliple items and types from a source string.
/// Panics if the compilation fails
/// Returns all MIR entities in unflattened format
#[cfg(test)]
fn build_items(code: &str) -> Vec<spade_mir::Entity> {
    let source = unindent::unindent(code);
    let mut buffer = codespan_reporting::term::termcolor::BufferWriter::stdout(
        codespan_reporting::term::termcolor::ColorChoice::Never,
    )
    .buffer();
    let opts = spade::Opt {
        error_buffer: &mut buffer,
        outfile: None,
        mir_output: None,
        type_dump_file: None,
        print_type_traceback: false,
        print_parse_traceback: false,
    };

    match spade::compile(
        vec![(
            spade::ModuleNamespace {
                namespace: spade_common::name::Path(vec![]),
                base_namespace: spade_common::name::Path(vec![]),
            },
            "testinput".to_string(),
            source,
        )],
        opts,
    ) {
        Ok(artefacts) => artefacts.bumpy_mir_entities,
        Err(()) => {
            // I'm not 100% sure why this is needed. The bufferwriter should output
            // to stdout and buffer.flush() should be enough. Unfortunatley, that does
            // not seem to be the case
            if !buffer.is_empty() {
                println!("{}", String::from_utf8_lossy(&buffer.into_inner()));
            }
            panic!("Compilation error")
        }
    }
}

/// Builds mutliple entities and types from a source string, then compares the resulting
/// entities. $expected should be a vector of mir entities. If any pipelines or other
/// non-entities or types are included in $code, this panics
#[macro_export]
macro_rules! build_and_compare_entities {
    ($code:expr, $expected:expr) => {
        let result = build_items($code);

        assert_eq!(
            $expected.len(),
            result.len(),
            "Expected {} entities, found {}",
            $expected.len(),
            result.len()
        );

        for (exp, res) in $expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    };
}
