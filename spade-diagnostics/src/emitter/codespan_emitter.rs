use codespan_reporting::diagnostic::{
    Diagnostic as CodespanDiagnostic, Suggestion, SuggestionPart,
};
use codespan_reporting::term::termcolor::{Color, ColorChoice, ColorSpec};
use codespan_reporting::term::{self, termcolor::Buffer};

use spade_common::location_info::AsLabel;

use crate::diagnostic::Subdiagnostic;
use crate::{CodeBundle, Diagnostic, Emitter};

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

pub struct CodespanEmitter;

impl Emitter for CodespanEmitter {
    fn emit_diagnostic(&mut self, diag: &Diagnostic, buffer: &mut Buffer, code: &CodeBundle) {
        let severity = diag.level.severity();
        let message = diag.message.as_str();
        let primary_label = if let Some(primary_label_message) = diag.primary_label.as_ref() {
            diag.span
                .primary_label()
                .with_message(primary_label_message.as_str())
        } else {
            diag.span.primary_label()
        };
        let mut labels = vec![primary_label];
        labels.extend(
            diag.secondary
                .iter()
                .map(|(sp, msg)| sp.secondary_label().with_message(msg.as_str())),
        );
        let mut simple_notes = vec![];
        let mut suggestions = vec![];
        for subdiag in &diag.subdiagnostics {
            match subdiag {
                Subdiagnostic::Note { level, message } => {
                    simple_notes.push(format!("{}: {}", level.as_str(), message.as_str()))
                }
                Subdiagnostic::Suggestion { parts, message } => suggestions.push(Suggestion {
                    file_id: parts[0].0 .1,
                    message: message.as_str().to_string(),
                    parts: parts
                        .iter()
                        .map(|((sp, _), replacement)| SuggestionPart {
                            range: (*sp).into(),
                            replacement: replacement.to_string(),
                        })
                        .collect(),
                }),
            }
        }
        let diag = CodespanDiagnostic::new(severity)
            .with_message(message)
            .with_labels(labels)
            .with_notes(simple_notes)
            .with_suggestions(suggestions);

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}