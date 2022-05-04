use codespan_reporting::{
    diagnostic::Diagnostic,
    term::{self, termcolor::Buffer},
};
use spade_common::{
    error_reporting::{codespan_config, AsLabel, CodeBundle, CompilationError},
    location_info::Loc,
};

use crate::ValueName;

pub struct AssertedExpression(pub Loc<ValueName>);

impl CompilationError for AssertedExpression {
    fn report(self, buffer: &mut Buffer, code: &CodeBundle) {
        let diag = Diagnostic::error()
            .with_message("Assertion failed")
            .with_labels(vec![self
                .0
                .primary_label()
                .with_message("This expression is false")]);

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}
