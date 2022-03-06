use crate::Error;
use codespan_reporting::diagnostic::Diagnostic;
use codespan_reporting::term::{self, termcolor::StandardStream};
use spade_common::error_reporting::{
    codespan_config, color_choice, AsLabel, CodeBundle, CompilationError,
};

impl CompilationError for Error {
    fn report(self, code: &CodeBundle, no_color: bool) {
        let diag = match self {
            Error::UsingGenericType { expr, t } => Diagnostic::error()
                .with_message(format!("Type of expression is not fully known"))
                .with_labels(vec![expr
                    .primary_label()
                    .with_message(format!("Incomplete type"))])
                .with_notes(vec![format!("Found incomplete type: {}", t)]),
            Error::CastToLarger { from, to } => Diagnostic::error()
                .with_message(format!("Truncating to a larger value"))
                .with_labels(vec![
                    from.primary_label()
                        .with_message(format!("This value isas {from} bytes")),
                    to.secondary_label()
                        .with_message(format!("But it is truncated to {to} bytes")),
                ])
                .with_notes(vec![format!("Truncation can only remove bits")]),
        };

        let writer = StandardStream::stderr(color_choice(no_color));

        term::emit(&mut writer.lock(), &codespan_config(), &code.files, &diag).unwrap();
    }
}
