/*

impl CompilationError for Error {
    fn report(&self, buffer: &mut Buffer, code: &CodeBundle, diag_handler: &mut DiagHandler) {
        // Errors which require special handling
        match self {
            Error::UnificationError(underlying) => {
                underlying.report(buffer, code, diag_handler);
                return;
            }
            _ => {}
        }

        let diag = match self {
            Error::UnificationError(_) => unreachable!(),
            Error::ConcatSizeMismatch {
                lhs,
                rhs,
                result,
                expected,
            } => {
                let lhs_plural = if lhs.inner == One::one() { "" } else { "s" };
                let rhs_plural = if rhs.inner == One::one() { "" } else { "s" };

                Diagnostic::bug()
                    .with_message(format!(
                        "Concatenation produces {result} bits, expected {expected}"
                    ))
                    .with_labels(vec![
                        result
                            .primary_label()
                            .with_message(format!("Expected {expected} bits")),
                        lhs.secondary_label()
                            .with_message(format!("This has {lhs} bit{lhs_plural}")),
                        rhs.secondary_label()
                            .with_message(format!("This has {rhs} bit{rhs_plural}")),
                    ])
            }
            Error::UndefinedVariable { name } => ,
            Error::UseBeforeReady {
                name,
                unavailable_for,
                referenced_at_stage,
            } => {
                let plural = if *unavailable_for == 1 { "" } else { "s" };

                Diagnostic::error()
                    .with_message(format!("Use of {name} before it is ready"))
                    .with_labels(vec![name.primary_label().with_message(format!(
                        "Is unavailable for another {unavailable_for} stage{plural}"
                    ))])
                    .with_notes(vec![
                        format!("Requesting {name} from stage {referenced_at_stage}"),
                        format!(
                            "But it will not be available until stage {}",
                            referenced_at_stage + unavailable_for
                        ),
                    ])
            }
            Error::AvailabilityMismatch { prev, new } => Diagnostic::error()
                .with_message("All subexpressions need the same pipeline delay")
                .with_labels(vec![
                    new.primary_label()
                        .with_message(format!("This has delay {new}")),
                    prev.secondary_label()
                        .with_message(format!("But this has delay {prev}")),
                ]),
            Error::InstantiatingGenericBuiltin { loc, head } => Diagnostic::error()
                .with_message("Generic builtins cannot be instantiated")
                .with_labels(vec![
                    loc.primary_label().with_message("Invalid instance"),
                    head.secondary_label()
                        .with_message("Because this is a generic __builtin__"),
                ]),
            Error::MissingPatterns {
                match_expr,
                useful_branches,
            } => {
                let witnesses = format_witnesses(useful_branches);
                Diagnostic::error()
                    .with_message(format!("Non-exhaustive match: {witnesses} not covered",))
                    .with_labels(vec![match_expr
                        .primary_label()
                        .with_message(format!("{witnesses} not covered"))])
            }
            Error::RefutablePattern {
                binding_kind,
                pattern,
                witnesses,
            } => {
                let witnesses = format_witnesses(witnesses);

                Diagnostic::error()
                    .with_message(format!("Refutable pattern in local binding: {witnesses} not covered"))
                    .with_labels(vec![
                        pattern.primary_label().with_message(format!("pattern {witnesses} not covered"))
                    ])
                    .with_notes(vec![
                        format!("{binding_kind} requires a pattern which matches all possible options, such as a variable, struct or enum with only 1 option."),
                        format!("hint: you might want to use match statement to handle different cases")
                    ])
            }
            Error::PortInRegister { loc, ty } => Diagnostic::error()
                .with_message("Ports cannot be put in a register")
                .with_labels(vec![loc.primary_label().with_message("This is a port")])
                .with_notes(vec![format!("{ty} is a port")]),
            Error::PortInGenericType { loc, param, actual } => Diagnostic::error()
                .with_message("Generic types cannot be ports")
                .with_labels(vec![loc.primary_label().with_message(format!(
                    "Parameter {param} is {actual} which is a port type"
                ))]),
            Error::SpadeDiagnostic(diag) => {
                return diag_handler.emit(diag, buffer, code);
            }
        };

        term::emit(buffer, &codespan_config(), &code.files, &diag).unwrap();
    }
}
*/
