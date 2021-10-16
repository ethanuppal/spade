use std::path::PathBuf;

use codespan_reporting::diagnostic::Label;
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::termcolor::ColorChoice;
use codespan_reporting::term::termcolor::{Color, ColorSpec};

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

    pub fn add_file(&mut self, filename: PathBuf, content: String) -> usize {
        self.files
            .add(filename.to_string_lossy().to_string(), content)
    }
}

pub trait CompilationError {
    fn report(self, code: &CodeBundle, no_color: bool);
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
