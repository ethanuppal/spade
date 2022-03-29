use codespan_reporting::diagnostic::Label;
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::termcolor::Buffer;
use codespan_reporting::term::termcolor::{Color, ColorChoice, ColorSpec};
use std::io::Write;

use crate::location_info::Loc;

pub fn color_choice(no_color: bool) -> ColorChoice {
    if no_color {
        ColorChoice::Never
    } else {
        ColorChoice::Auto
    }
}

pub fn codespan_config() -> codespan_reporting::term::Config {
    let mut primary_label_error = ColorSpec::new();
    primary_label_error
        .set_fg(Some(Color::Red))
        .set_intense(true);

    let style = codespan_reporting::term::Styles {
        primary_label_error,
        ..Default::default()
    };
    codespan_reporting::term::Config {
        styles: style,
        ..Default::default()
    }
}

/// A bundle of all the source code included in the current compilation
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

    pub fn add_file(&mut self, filename: String, content: String) -> usize {
        self.files.add(filename, content)
    }
}

pub trait CompilationError {
    fn report(self, buffer: &mut Buffer, code: &CodeBundle);
}

impl CompilationError for std::io::Error {
    fn report(self, buffer: &mut Buffer, _code: &CodeBundle) {
        if let Err(e) = buffer.write_all(self.to_string().as_bytes()) {
            eprintln!(
                "io error when writing io error to error buffer\noriginal error: {}\nnew error: {}",
                self.to_string(),
                e.to_string()
            );
        }
    }
}

pub fn primary_label<T>(loc: Loc<T>) -> Label<usize> {
    Label::primary(loc.file_id, loc)
}

pub trait AsLabel {
    fn file_id(&self) -> usize;
    fn span(&self) -> std::ops::Range<usize>;

    fn primary_label(&self) -> Label<usize> {
        Label::primary(self.file_id(), self.span())
    }
    fn secondary_label(&self) -> Label<usize> {
        Label::secondary(self.file_id(), self.span())
    }
}
