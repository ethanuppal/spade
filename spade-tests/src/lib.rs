use std::io::Write;
#[cfg(test)]
use std::path::PathBuf;

use codespan_reporting::term::termcolor::Buffer;

#[cfg(test)]
use spade_common::name::Path;
use spade_diagnostics::emitter::CodespanEmitter;
use spade_diagnostics::{CodeBundle, CompilationError, DiagHandler};

#[cfg(test)]
mod ast_lowering;
#[cfg(test)]
mod hir_lowering;
#[cfg(test)]
mod integration;
#[cfg(test)]
mod linear_check;
#[cfg(test)]
mod parser;
#[cfg(test)]
mod ports_integration;
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
                let mut diag_handler = DiagHandler::new(Box::new(CodespanEmitter));
                e.report(&mut buffer, &code_bundle, &mut diag_handler);
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
            use tracing_subscriber::filter::{EnvFilter, LevelFilter};
            use tracing_subscriber::prelude::*;
            use tracing_tree::HierarchicalLayer;
            let env_filter = EnvFilter::builder()
                .with_default_directive(LevelFilter::OFF.into())
                .with_env_var("SPADE_LOG")
                .from_env_lossy();
            let layer = HierarchicalLayer::new(2)
                .with_targets(true)
                .with_writer(tracing_subscriber::fmt::TestWriter::new())
                .with_filter(env_filter);

            tracing_subscriber::registry().with(layer).try_init().ok();

            let source = unindent::unindent($src);
            let mut buffer = codespan_reporting::term::termcolor::Buffer::no_color();
            let opts = spade::Opt {
                error_buffer: &mut buffer,
                outfile: None,
                mir_output: None,
                type_dump_file: None,
                state_dump_file: None,
                item_list_file: None,
                print_type_traceback: false,
                print_parse_traceback: false,
            };

            let mut files = vec![(
                    spade::ModuleNamespace {
                        namespace: spade_common::name::Path(vec![]),
                        base_namespace: spade_common::name::Path(vec![]),
                    },
                    "testinput".to_string(),
                    source.to_string(),
                )];

            files.append(&mut crate::stdlib_files());

            let _ = spade::compile(
                files,
                opts,
                spade_diagnostics::DiagHandler::new(Box::new(
                    spade_diagnostics::emitter::CodespanEmitter,
                )),
            );

            insta::with_settings!({
                // FIXME: Why can't we set 'description => source' here?
                omit_expression => true,
            }, {
                insta::assert_snapshot!(format!(
                    "{}\n\n{}",
                    source,
                    std::str::from_utf8(buffer.as_slice()).expect("error contains invalid utf-8")
                ));
            });
        }
    };
}

#[cfg(test)]
fn stdlib_files() -> Vec<(spade::ModuleNamespace, String, String)> {
    let paths = PathBuf::from("../stdlib")
        .read_dir()
        .expect(&format!("Failed to read files in ./stdlib"))
        .map(|entry| entry.expect("Failed to read dir entry"))
        .collect::<Vec<_>>();

    let mut result = vec![];
    for path_utf8 in paths.iter() {
        let path = path_utf8.path();

        // If the file doesn't have a stem, it also won't have a `.spade` extension,
        // so we'll silently ignore it
        let file_stem = if let Some(stem) = path.file_stem() {
            stem
        } else {
            continue;
        };

        if path.is_dir() {
            panic!("Stdlib contained subdirectory")
        } else if path.extension().and_then(|s| s.to_str()) == Some("spade") {
            let file_content = std::fs::read_to_string(&path)
                .expect(&format!("Failed to read {}", path.to_string_lossy()));
            result.push((
                spade::ModuleNamespace {
                    namespace: Path::from_strs(&vec![
                        "std",
                        &file_stem.to_str().expect(&format!(
                            "{} did not have a utf-8 file stem",
                            path.to_string_lossy()
                        )),
                    ]),
                    base_namespace: Path::from_strs(&vec!["std"]),
                },
                path.to_string_lossy().to_string(),
                file_content,
            ))
        }
    }

    result
}

#[cfg(test)]
fn build_items(code: &str) -> Vec<spade_mir::Entity> {
    build_items_inner(code, false)
}

#[cfg(test)]
fn build_items_with_stdlib(code: &str) -> Vec<spade_mir::Entity> {
    build_items_inner(code, true)
        .into_iter()
        .filter(|f| match &f.name {
            spade_mir::UnitName::Unescaped(_) => true,
            spade_mir::UnitName::Escaped { name: _, path } => {
                !path.starts_with(&["std".to_string()])
            }
        })
        .collect()
}

/// Builds multiple items and types from a source string.
/// Panics if the compilation fails
/// Returns all MIR entities in unflattened format
#[cfg(test)]
fn build_items_inner(code: &str, with_stdlib: bool) -> Vec<spade_mir::Entity> {
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
        state_dump_file: None,
        item_list_file: None,
        print_type_traceback: false,
        print_parse_traceback: false,
    };

    let mut files = vec![(
        spade::ModuleNamespace {
            namespace: spade_common::name::Path(vec![]),
            base_namespace: spade_common::name::Path(vec![]),
        },
        "testinput".to_string(),
        source,
    )];
    if with_stdlib {
        files.append(&mut stdlib_files());
    }

    match spade::compile(
        files,
        opts,
        spade_diagnostics::DiagHandler::new(Box::new(spade_diagnostics::emitter::CodespanEmitter)),
    ) {
        Ok(artefacts) => artefacts.bumpy_mir_entities,
        Err(_) => {
            // I'm not 100% sure why this is needed. The bufferwriter should output
            // to stdout and buffer.flush() should be enough. Unfortunately, that does
            // not seem to be the case
            if !buffer.is_empty() {
                println!("{}", String::from_utf8_lossy(&buffer.into_inner()));
            }
            panic!("Compilation error")
        }
    }
}

/// Builds multiple entities and types from a source string, then compares the resulting
/// entities. $expected should be a vector of mir entities. If any pipelines or other
/// non-entities or types are included in $code, this panics
/// Sorts the entities by name to make deterministic
#[macro_export]
macro_rules! build_and_compare_entities {
    ($code:expr, $expected:expr) => {
        let mut result = build_items_with_stdlib($code);

        assert_eq!(
            $expected.len(),
            result.len(),
            "Expected {} entities, found {}",
            $expected.len(),
            result.len()
        );

        let mut expected = $expected.clone();
        expected.sort_by_key(|e| e.name.clone());
        result.sort_by_key(|e| e.name.clone());

        for (exp, res) in expected.into_iter().zip(result.into_iter()) {
            assert_same_mir!(&res, &exp);
        }
    };
}
