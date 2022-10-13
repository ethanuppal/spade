use std::io::Write;

use codespan_reporting::files::{Files, SimpleFiles};
use codespan_reporting::term::termcolor::Buffer;

use spade_common::location_info::{AsLabel, Loc};

pub use diagnostic::Diagnostic;
pub use emitter::Emitter;

pub mod diagnostic;
pub mod emitter;

/// A bundle of all the source code included in the current compilation
#[derive(Clone)]
pub struct CodeBundle {
    pub files: SimpleFiles<String, String>,
}

impl CodeBundle {
    // Create a new code bundle adding the passed string as the 0th file
    pub fn new(string: String) -> Self {
        let mut files = SimpleFiles::new();
        files.add("<str>".to_string(), string);
        Self { files }
    }

    pub fn from_files(files: &[(String, String)]) -> Self {
        let mut result = Self {
            files: SimpleFiles::new(),
        };
        for (name, content) in files {
            result.add_file(name.clone(), content.clone());
        }
        result
    }

    pub fn add_file(&mut self, filename: String, content: String) -> usize {
        self.files.add(filename, content)
    }

    pub fn dump_files(&self) -> Vec<(String, String)> {
        let mut all_files = vec![];
        loop {
            match self.files.get(all_files.len()) {
                Ok(file) => all_files.push((file.name().clone(), file.source().clone())),
                Err(codespan_reporting::files::Error::FileMissing) => break,
                Err(e) => {
                    panic!("{e}")
                }
            };
        }
        all_files
    }

    pub fn source_loc<T>(&self, loc: &Loc<T>) -> String {
        let location = self
            .files
            .location(loc.file_id(), loc.span.start().to_usize())
            .expect("Loc was not in code bundle");
        format!(
            "{}:{},{}",
            self.files.get(loc.file_id()).unwrap().name(),
            location.line_number,
            location.column_number
        )
    }
}

pub trait CompilationError {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, diag_handler: &mut DiagHandler);
}

impl CompilationError for std::io::Error {
    fn report(&self, buffer: &mut Buffer, _code: &CodeBundle, _diag_handler: &mut DiagHandler) {
        if let Err(e) = buffer.write_all(self.to_string().as_bytes()) {
            eprintln!(
                "io error when writing io error to error buffer\noriginal error: {}\nnew error: {}",
                self, e
            );
        }
    }
}

pub struct DiagHandler {
    emitter: Box<dyn Emitter + Send>,
    // Here we can add more shared state for diagnostics. For example, rustc can
    // stash diagnostics that can be retrieved in later stages, indexed by (Span, StashKey).
}

impl DiagHandler {
    pub fn new(emitter: Box<dyn Emitter + Send>) -> Self {
        Self { emitter }
    }

    pub fn emit(&mut self, diagnostic: &Diagnostic, buffer: &mut Buffer, code: &CodeBundle) {
        self.emitter.emit_diagnostic(diagnostic, buffer, code);
    }
}

#[cfg(test)]
mod tests {
    use codespan_reporting::term::termcolor::Buffer;

    use crate::emitter::CodespanEmitter;
    use crate::{CodeBundle, Diagnostic, Emitter};

    #[test]
    fn bug_diagnostics_works() {
        let code = CodeBundle::new("hello goodbye".to_string());
        let sp = ((6..13).into(), 0);
        let mut buffer = Buffer::no_color();
        let mut emitter = CodespanEmitter;
        let diagnostic = Diagnostic::bug(sp, "oof");
        emitter.emit_diagnostic(&diagnostic, &mut buffer, &code);
        insta::assert_display_snapshot!(String::from_utf8(buffer.into_inner()).unwrap());
    }
}
