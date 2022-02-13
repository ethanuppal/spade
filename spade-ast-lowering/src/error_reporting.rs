use crate::Error;
use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{
    codespan_config, color_choice, AsLabel, CodeBundle, CompilationError,
};
use spade_hir::symbol_table::{DeclarationError, LookupError};

impl CompilationError for Error {
    fn report(self, code: &CodeBundle, no_color: bool) {
        let diag = match self {
            Error::DuplicateTypeVariable { found, previously } => Diagnostic::error()
                .with_message(format!("Duplicate typename: `{}`", found.inner))
                .with_labels(vec![
                    found.primary_label().with_message("Duplicate typename"),
                    previously
                        .secondary_label()
                        .with_message("Previously used here"),
                ]),
            Error::LookupError(LookupError::NoSuchSymbol(path)) => Diagnostic::error()
                .with_message(format!("Use of undeclared name {}", path))
                .with_labels(vec![path.primary_label().with_message("Undeclared name")]),
            Error::LookupError(LookupError::NotATypeSymbol(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a type", path))
                .with_labels(vec![
                    path.primary_label().with_message(format!("Expected type")),
                    got.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAVariable(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a variable", path))
                .with_labels(vec![
                    path.primary_label()
                        .with_message(format!("Expected variable")),
                    got.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAnEntity(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be an enity", path))
                .with_labels(vec![
                    path.primary_label()
                        .with_message(format!("Expected entity")),
                    got.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAPipeline(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a pipeline", path))
                .with_labels(vec![
                    path.primary_label()
                        .with_message(format!("Expected pipeline")),
                    got.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAPatternableType(path, got)) => Diagnostic::error()
                .with_message(format!(
                    "{} can not be used as a pattern",
                    got.kind_string()
                ))
                .with_labels(vec![
                    path.primary_label()
                        .with_message(format!("Expected pattern")),
                    got.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAFunction(path, got)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a function", path))
                .with_labels(vec![
                    path.primary_label()
                        .with_message(format!("Expected function")),
                    got.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        got.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAnEnumVariant(path, was)) => Diagnostic::error()
                .with_message(format!("Expected {} to be an enum variant", path))
                .with_labels(vec![
                    path.primary_label()
                        .with_message(format!("Expected enum variant")),
                    was.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        was.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAStruct(path, was)) => Diagnostic::error()
                .with_message(format!("Expected {} to be an struct", path))
                .with_labels(vec![
                    path.primary_label()
                        .with_message(format!("Expected struct")),
                    was.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        was.kind_string()
                    )),
                ]),
            Error::LookupError(LookupError::NotAValue(path, was)) => Diagnostic::error()
                .with_message(format!("Expected {} to be a value", path))
                .with_labels(vec![
                    path.primary_label().with_message(format!("Expected value")),
                    was.loc().secondary_label().with_message(format!(
                        "{} is a {}",
                        path,
                        was.kind_string()
                    )),
                ])
                .with_notes(vec![
                    "Expected value".to_string(),
                    format!("Found {}", was.kind_string().to_string()),
                ]),
            Error::LookupError(LookupError::IsAType(path)) => Diagnostic::error()
                .with_message(format!("Unexpected type {}", path))
                .with_labels(vec![path
                    .primary_label()
                    .with_message(format!("Unexpected type"))]),
            Error::DeclarationError(DeclarationError::DuplicateDeclaration { old, new }) => {
                Diagnostic::error()
                    .with_message(format!("A previous declaration of {} exists", new))
                    .with_labels(vec![
                        new.primary_label()
                            .with_message(format!("{} was declared more than once", new)),
                        old.primary_label()
                            .with_message(format!("Previously declared here")),
                    ])
            }
            Error::DuplicateArgument { new, prev } => Diagnostic::error()
                .with_message(format!("Multiple arguments called {}", new))
                .with_labels(vec![
                    new.primary_label()
                        .with_message(format!("{} is an argument more than once", new)),
                    prev.secondary_label()
                        .with_message(format!("Previously declared here")),
                ]),
            Error::DuplicateEnumOption { new, prev } => Diagnostic::error()
                .with_message(format!("Multiple options called {}", new))
                .with_labels(vec![
                    new.primary_label()
                        .with_message(format!("{} is an option more than once", new)),
                    prev.secondary_label()
                        .with_message(format!("Previously declared here")),
                ]),
            Error::ArgumentListLenghtMismatch { expected, got, at } => Diagnostic::error()
                .with_message(format!("Expected {} arguments, got {}", expected, got))
                .with_labels(vec![at
                    .primary_label()
                    .with_message(format!("Expected {} arguments", expected))]),
            Error::PatternListLengthMismatch { expected, got, at } => Diagnostic::error()
                .with_message(format!("Expected {} arguments, got {}", expected, got))
                .with_labels(vec![at
                    .primary_label()
                    .with_message(format!("Expected {} arguments", expected))]),
            Error::DuplicateNamedBindings { new, prev_loc } => Diagnostic::error()
                .with_message(format!("Multiple bindings to {}", new))
                .with_labels(vec![
                    new.primary_label().with_message("Previously bound"),
                    prev_loc
                        .secondary_label()
                        .with_message(format!("previously bound here")),
                ]),
            Error::NoSuchArgument { name } => Diagnostic::error()
                .with_message(format!("{}: No such argument to", name))
                .with_labels(vec![name
                    .primary_label()
                    .with_message(format!("No such argument"))]),
            Error::MissingArguments { missing, at } => {
                let plural = if missing.len() == 1 {
                    "argument"
                } else {
                    "arguments"
                };

                let arg_list = missing
                    .iter()
                    .map(|i| format!("{}", i))
                    .collect::<Vec<_>>()
                    .join(", ");

                Diagnostic::error()
                    .with_message(format!("Missing {}: {}", plural, arg_list))
                    .with_labels(vec![
                        at.primary_label()
                            .with_message(format!("Missing {}", plural)),
                        at.secondary_label()
                            .with_message(format!("Missing {}", arg_list)),
                    ])
            }
            Error::NoPipelineStages { pipeline } => Diagnostic::error()
                .with_message("Missing pipeline stages")
                .with_labels(vec![pipeline
                    .primary_label()
                    .with_message(format!("Pipelien must have at least one stage"))]),
            Error::IncorrectStageCount {
                got,
                expected,
                pipeline,
            } => Diagnostic::error()
                .with_message(format!("Expected {} pipeline stages", expected))
                .with_labels(vec![
                    pipeline
                        .primary_label()
                        .with_message(format!("Found {} stages", got)),
                    expected
                        .secondary_label()
                        .with_message(format!("{} specified here", expected)),
                ]),
            Error::EarlyPipelineReturn { expression } => Diagnostic::error()
                .with_message(format!("Unexpected return expression"))
                .with_labels(vec![expression
                    .primary_label()
                    .with_message(format!("Did not expect an value in this stage"))])
                .with_notes(vec![format!(
                    "Only the last stage of a pipeline can return values"
                )]),
            Error::PipelineDepthMissmatch { expected, got } => Diagnostic::error()
                .with_message(format!(
                    "Pipeline depth mismatch. Expected {} got {}",
                    expected, got
                ))
                .with_labels(vec![got
                    .primary_label()
                    .with_message(format!("Expected {}", expected))]),
            Error::MissingPipelineClock { at_loc } => Diagnostic::error()
                .with_message(format!("Missing clock argument."))
                .with_labels(vec![at_loc
                    .primary_label()
                    .with_message(format!("Expected clock argument"))])
                .with_notes(vec![format!("All pipelines take a clock as an argument")]),
            Error::GenericsGivenForGeneric { at_loc, for_type } => Diagnostic::error()
                .with_message("Generic arguments given for a generic type")
                .with_labels(vec![at_loc
                    .primary_label()
                    .with_message(format!("{} is a generic type", for_type))])
                .with_notes(vec![format!(
                    "A generic argument can not have generic types"
                )]),
            Error::DeclarationOfNonReg {
                at,
                declaration_location,
            } => Diagnostic::error()
                .with_message("Declared variables can only be defined by registers")
                .with_labels(vec![
                    at.primary_label().with_message(format!("Not a register")),
                    declaration_location
                        .secondary_label()
                        .with_message(format!("{} declared here", at)),
                ]),
            Error::RedefinitionOfDeclaration { at, previous } => Diagnostic::error()
                .with_message(format!("{} was already defined", at))
                .with_labels(vec![
                    at.primary_label()
                        .with_message(format!("{} was defined previously", at)),
                    previous
                        .secondary_label()
                        .with_message(format!("previous definition")),
                ])
                .with_notes(vec![format!("Declared variables can only be defined once")]),
        };

        let writer = StandardStream::stderr(color_choice(no_color));

        term::emit(&mut writer.lock(), &codespan_config(), &code.files, &diag).unwrap();
    }
}
