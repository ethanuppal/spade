use std::path::Path;

use crate::{symbol_table::Error as LookupError, Error};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{codespan_config, color_choice};

pub fn report_semantic_error(filename: &Path, file_content: &str, err: Error, no_color: bool) {
    let mut files = SimpleFiles::new();
    let file_id = files.add(filename.to_string_lossy(), file_content);
    let diag = match err {
        Error::DuplicateTypeVariable { found, previously } => Diagnostic::error()
            .with_message(format!("Duplicate typename: `{}`", found.inner))
            .with_labels(vec![
                Label::primary(file_id, found.span).with_message("Duplicate typename"),
                Label::secondary(file_id, previously.span).with_message("Previously used here"),
            ]),
        Error::LookupError(LookupError::NoSuchSymbol(path)) => Diagnostic::error()
            .with_message(format!("Use of undeclared name {}", path))
            .with_labels(vec![
                Label::primary(file_id, path.span).with_message("Undeclared name")
            ]),
        Error::LookupError(LookupError::NotATypeSymbol(path, got)) => Diagnostic::error()
            .with_message(format!("Expected {} to be a type", path))
            .with_labels(vec![
                Label::primary(file_id, path.span).with_message(format!("Expected type")),
                Label::secondary(file_id, got.loc().span).with_message(format!(
                    "{} is a {}",
                    path,
                    got.kind_string()
                )),
            ]),
        Error::LookupError(LookupError::NotAVariable(path, got)) => Diagnostic::error()
            .with_message(format!("Expected {} to be a variable", path))
            .with_labels(vec![
                Label::primary(file_id, path.span).with_message(format!("Expected variable")),
                Label::secondary(file_id, got.loc().span).with_message(format!(
                    "{} is a {}",
                    path,
                    got.kind_string()
                )),
            ]),
        Error::LookupError(LookupError::NotAnEntity(path, got)) => Diagnostic::error()
            .with_message(format!("Expected {} to be an enity", path))
            .with_labels(vec![
                Label::primary(file_id, path.span).with_message(format!("Expected entity")),
                Label::secondary(file_id, got.loc().span).with_message(format!(
                    "{} is a {}",
                    path,
                    got.kind_string()
                )),
            ]),
        Error::ArgumentListLenghtMissmatch {
            expected,
            got,
            at,
            for_entity,
        } => Diagnostic::error()
            .with_message(format!("Expected {} arguments, got {}", expected, got))
            .with_labels(vec![
                Label::primary(file_id, at.span)
                    .with_message(format!("Expected {} arguments", expected)),
                Label::secondary(file_id, for_entity.span)
                    .with_message(format!("When instanciating this entity",)),
            ]),
    };

    let writer = StandardStream::stderr(color_choice(no_color));

    term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
}
