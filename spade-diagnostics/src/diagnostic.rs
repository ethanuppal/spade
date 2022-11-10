use codespan::Span;
use codespan_reporting::diagnostic::Severity;

use spade_common::location_info::FullSpan;

const INTERNAL_BUG_NOTE: &str = r#"This is an internal bug in the compiler.
We would appreciate if you opened an issue in the repository:
https://gitlab.com/spade-lang/spade/-/issues/new?issuable_template=Internal%20bug"#;

#[derive(Debug, Clone, PartialEq)]
pub enum Message {
    Str(String),
    // FluentIdentifier(String) for translated messages.
}

impl Message {
    pub fn as_str(&self) -> &str {
        match self {
            Message::Str(s) => s,
        }
    }
}

impl From<String> for Message {
    fn from(other: String) -> Message {
        Message::Str(other)
    }
}

impl From<&str> for Message {
    fn from(other: &str) -> Message {
        Message::from(other.to_string())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DiagnosticLevel {
    /// An internal error in the compiler that shouldn't happen.
    Bug,
    Error,
    Warning,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SubdiagnosticLevel {
    Help,
    Note,
}

impl DiagnosticLevel {
    pub fn as_str(&self) -> &'static str {
        match self {
            DiagnosticLevel::Bug => "internal bug",
            DiagnosticLevel::Error => "error",
            DiagnosticLevel::Warning => "warning",
        }
    }

    pub fn severity(&self) -> Severity {
        match self {
            DiagnosticLevel::Bug => Severity::Bug,
            DiagnosticLevel::Error => Severity::Error,
            DiagnosticLevel::Warning => Severity::Warning,
        }
    }
}

impl SubdiagnosticLevel {
    pub fn as_str(&self) -> &'static str {
        match self {
            SubdiagnosticLevel::Help => "help",
            SubdiagnosticLevel::Note => "note",
        }
    }

    pub fn severity(&self) -> Severity {
        match self {
            SubdiagnosticLevel::Help => Severity::Help,
            SubdiagnosticLevel::Note => Severity::Note,
        }
    }
}

/// Something that is wrong in the code.
#[derive(Debug, Clone, PartialEq)]
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub message: Message,
    /// The "primary location" of this diagnostic.
    pub span: FullSpan,
    /// Optionally, the primary location can be labeled. If None, it is only underlined.
    pub primary_label: Option<Message>,
    /// Secondary locations that further explain the reasoning behind the diagnostic.
    pub secondary: Vec<(FullSpan, Message)>,
    /// Extra diagnostics that are shown after the main diagnostic.
    pub subdiagnostics: Vec<Subdiagnostic>,
}

/// An extra diagnostic that can further the main diagnostic in some way.
#[derive(Debug, Clone, PartialEq)]
pub enum Subdiagnostic {
    /// A simple note without a span.
    Note {
        level: SubdiagnosticLevel,
        message: Message,
    },
    /// A longer note with additional spans and labels.
    SpannedNote {
        level: SubdiagnosticLevel,
        message: Message,
        primary_label: (FullSpan, Message),
        secondary_labels: Vec<(FullSpan, Message)>,
    },
    /// A change suggestion, made up of one or more suggestion parts.
    Suggestion {
        /// The individual replacements that make up this suggestion.
        ///
        /// Additions, removals and replacements are encoded using the span and the suggested
        /// replacement according to the following table:
        ///
        ///```text
        /// +-----------+-------------+----------------+
        /// | Span      | Replacement | Interpretation |
        /// +-----------+-------------+----------------+
        /// | Non-empty | Non-empty   | Replacement    |
        /// | Non-empty | Empty       | Removal        |
        /// | Empty     | Non-empty   | Addition       |
        /// | Empty     | Empty       | Invalid        |
        /// +-----------+-------------+----------------+
        ///```
        parts: Vec<(FullSpan, String)>,
        message: Message,
    },
}

/// Builder for use with [Diagnostic::span_suggest_multipart].
pub struct SuggestionParts(Vec<(FullSpan, String)>);

impl SuggestionParts {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn part(mut self, span: impl Into<FullSpan>, code: impl Into<String>) -> Self {
        self.0.push((span.into(), code.into()));
        self
    }
}
impl Diagnostic {
    fn new(level: DiagnosticLevel, span: impl Into<FullSpan>, message: impl Into<Message>) -> Self {
        Self {
            level,
            message: message.into(),
            span: span.into(),
            primary_label: None,
            secondary: Vec::new(),
            subdiagnostics: Vec::new(),
        }
    }

    /// Report that something happened in the compiler that shouldn't be possible. This signifies
    /// that something is wrong with the compiler. It will include a large footer instructing the
    /// user to create an issue or otherwise get in touch.
    pub fn bug(span: impl Into<FullSpan>, message: impl Into<Message>) -> Self {
        Self::new(DiagnosticLevel::Bug, span, message).note(INTERNAL_BUG_NOTE)
    }

    /// Report that something is wrong with the supplied code.
    pub fn error(span: impl Into<FullSpan>, message: impl Into<Message>) -> Self {
        Self::new(DiagnosticLevel::Error, span, message)
    }

    /// Attach a message to the primary label of this error.
    pub fn primary_label(mut self, primary_label: impl Into<Message>) -> Self {
        self.primary_label = Some(primary_label.into());
        self
    }

    pub fn secondary_label(
        mut self,
        span: impl Into<FullSpan>,
        message: impl Into<Message>,
    ) -> Self {
        self.secondary.push((span.into(), message.into()));
        self
    }

    /// Attach a simple note to this diagnostic.
    pub fn note(mut self, message: impl Into<Message>) -> Self {
        self.subdiagnostics.push(Subdiagnostic::Note {
            level: SubdiagnosticLevel::Note,
            message: message.into(),
        });
        self
    }

    pub fn help(mut self, message: impl Into<Message>) -> Self {
        self.subdiagnostics.push(Subdiagnostic::Note {
            level: SubdiagnosticLevel::Help,
            message: message.into(),
        });
        self
    }

    pub fn span_suggest(
        mut self,
        message: impl Into<Message>,
        span: impl Into<FullSpan>,
        code: impl Into<String>,
    ) -> Self {
        self.subdiagnostics.push(Subdiagnostic::Suggestion {
            parts: vec![(span.into(), code.into())],
            message: message.into(),
        });
        self
    }

    /// Convenience method to suggest some code that can be inserted directly before some span.
    ///
    /// Note that this will be _after_ any preceding whitespace. Use
    /// [Diagnostic::span_suggest_insert_after] if you want the suggestion to insert before
    /// preceding whitespace.
    pub fn span_suggest_insert_before(
        self,
        message: impl Into<Message>,
        span: impl Into<FullSpan>,
        code: impl Into<String>,
    ) -> Self {
        let (span, file) = span.into();
        let code = code.into();

        assert!(!code.is_empty());

        self.span_suggest(message, (Span::new(span.start(), span.start()), file), code)
    }

    /// Convenience method to suggest some code that can be inserted directly after some span.
    ///
    /// Note that this will be _before_ any preceding whitespace. Use
    /// [Diagnostic::span_suggest_insert_before] if you want the suggestion to insert after
    /// preceding whitespace.
    pub fn span_suggest_insert_after(
        self,
        message: impl Into<Message>,
        span: impl Into<FullSpan>,
        code: impl Into<String>,
    ) -> Self {
        let (span, file) = span.into();
        let code = code.into();

        assert!(!code.is_empty());

        self.span_suggest(message, (Span::new(span.start(), span.start()), file), code)
    }

    /// Convenience method to suggest some code that can be replaced.
    pub fn span_suggest_replace(
        self,
        message: impl Into<Message>,
        span: impl Into<FullSpan>,
        code: impl Into<String>,
    ) -> Self {
        let (span, file) = span.into();
        let code = code.into();

        assert!(span.start() != span.end());
        assert!(!code.is_empty());

        self.span_suggest(message, (span, file), code)
    }

    /// Convenience method to suggest some code that can be removed.
    pub fn span_suggest_remove(
        self,
        message: impl Into<Message>,
        span: impl Into<FullSpan>,
    ) -> Self {
        let (span, file) = span.into();

        assert!(span.start() != span.end());

        self.span_suggest(message, (span, file), "")
    }

    pub fn span_suggest_multipart(
        mut self,
        message: impl Into<Message>,
        parts: SuggestionParts,
    ) -> Self {
        self.push_span_suggest_multipart(message, parts);
        self
    }

    pub fn push_span_suggest_multipart(
        &mut self,
        message: impl Into<Message>,
        SuggestionParts(parts): SuggestionParts,
    ) -> &mut Self {
        self.subdiagnostics.push(Subdiagnostic::Suggestion {
            parts,
            message: message.into(),
        });
        self
    }
}

// Assert that something holds, if it does not, return a Diagnostic::bug with the specified
// span
#[macro_export]
macro_rules! diag_assert {
    ($span:expr, $condition:expr) => {
        if !$condition {
            return Err(Diagnostic::bug(
                $span,
                format!("Assertion {} failed", stringify!($condition)),
            )
            .into());
        }
    };
}

// Like anyhow::anyhow but for diagnostics. Attaches the message to the specified expression
#[macro_export]
macro_rules! diag_anyhow {
    ($span:expr, $($arg:tt)*) => {
        Diagnostic::bug($span, format!($($arg)*))
    }
}

// Like anyhow::bail but for diagnostics. Attaches the message to the specified expression
#[macro_export]
macro_rules! diag_bail {
    ($span:expr, $($arg:tt)*) => {
        Err(spade_diagnostics::diag_anyhow!($span, $($arg)*).into())
    }
}
