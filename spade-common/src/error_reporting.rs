use std::path::Path;

use codespan_reporting::term::termcolor::ColorChoice;
use codespan_reporting::term::termcolor::{Color, ColorSpec};

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

pub trait CompilationError {
    fn report(self, filename: &Path, file_content: &str, no_color: bool);
}
