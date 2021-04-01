use std::path::Path;

use crate::Error;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{codespan_config, color_choice, CompilationError};

impl CompilationError for Error {
    fn report(self, filename: &Path, file_content: &str, no_color: bool) {
        let mut files = SimpleFiles::new();
        let file_id = files.add(filename.to_string_lossy(), file_content);
        let diag = match self {
            Error::UsingGenericType { expr, t } => Diagnostic::error()
                .with_message(format!("Type of expression is not fully known"))
                .with_labels(vec![
                    Label::primary(file_id, expr.span).with_message(format!("Incomplete type"))
                ])
                .with_notes(vec![format!("Found incomplete type: {}", t)]),
        };

        let writer = StandardStream::stderr(color_choice(no_color));

        term::emit(&mut writer.lock(), &codespan_config(), &files, &diag).unwrap();
    }
}
