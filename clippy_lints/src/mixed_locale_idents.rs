use clippy_utils::diagnostics::span_lint;
use rustc_data_structures::fx::FxHashMap;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::{Span, Symbol};
use unicode_script::{Script, UnicodeScript};
use unicode_security::is_potential_mixed_script_confusable_char;

declare_clippy_lint! {
    /// **What it does:** Checks for usage of mixed locales in a single identifier part
    /// with respect to the used case.
    ///
    /// **Why is this bad?** While it's OK for identifier to have different parts in different
    /// locales, it may be confusing if multiple locales are used in a single word.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    ///
    /// The following code compiles without any warnings:
    ///
    /// ```rust
    /// // In the `Block` identifier part, it's not a common latin `o` used, but rather Russian `о`.
    /// // It's hard to see visually and the `mixed_script_confusables` warning is not spawned
    /// // because of the `Блок` identifier part.
    /// struct BlоckБлок;
    ///
    /// fn main() {
    ///     let _block = Blоck ;
    /// }
    /// ```
    ///
    /// The same example, but with `Block` (english `o`) used instead of `Blоck` (russian `о`).
    /// It will not compile
    ///
    /// ```compile_fail
    /// struct BlоckБлок;
    ///
    /// fn main() {
    ///     let _block = BlockБлок;
    /// }
    ///
    /// // Compile output:
    /// //
    /// //  error[E0425]: cannot find value `BlockБлок` in this scope
    /// //   --> src/main.rs:4:18
    /// //    |
    /// //  1 | struct BlоckБлок;
    /// //    | ----------------- similarly named unit struct `BlоckБлок` defined here
    /// //  ...
    /// //  4 |     let _block = BlockБлок;
    /// //    |                  ^^^^^^^^^ help: a unit struct with a similar name exists: `BlоckБлок`
    /// ```
    pub MIXED_LOCALE_IDENTS,
    style,
    "multiple locales used in a single identifier part"
}

#[derive(Clone, Debug)]
pub struct MixedLocaleIdents;

impl_lint_pass!(MixedLocaleIdents => [MIXED_LOCALE_IDENTS]);

/// Cases that normally can be met in the Rust identifiers.
#[derive(Debug)]
enum Case {
    /// E.g. `SomeStruct`, delimiter is uppercase letter.
    Camel,
    /// E.g. `some_var` or `SOME_VAR, delimiter is `_`.
    Snake,
    /// E.g. `WHY_AmIWritingThisWay`, delimiters are both `_` and uppercase letter.
    Mixed,
}

fn detect_case(ident: &str) -> Case {
    let mut has_underscore = false;
    let mut has_upper = false;
    let mut has_lower = false;
    for c in ident.chars() {
        has_underscore |= c == '_';
        has_upper |= c.is_uppercase();
        has_lower |= c.is_lowercase();
    }

    if has_upper && has_lower && has_underscore {
        Case::Mixed
    } else if !has_upper || !has_lower {
        // Because of the statement above we are sure
        // that we can't have mixed case already.
        // If we have only one case, it's certainly snake case (either lowercase or uppercase).
        Case::Snake
    } else {
        // The only option left.
        Case::Camel
    }
}

/// Flag for having confusables in the identifier.
#[derive(Debug, Clone, Copy)]
enum ConfusablesState {
    /// Identifier part currently only has confusables.
    OnlyConfusables,
    /// Identifier part has not only confusables.
    NotConfusable,
}

impl ConfusablesState {
    fn from_char(c: char) -> Self {
        if is_potential_mixed_script_confusable_char(c) {
            Self::OnlyConfusables
        } else {
            Self::NotConfusable
        }
    }

    fn update(&mut self, c: char) {
        let is_confusable = is_potential_mixed_script_confusable_char(c);
        *self = match (*self, is_confusable) {
            (Self::OnlyConfusables, true) => Self::OnlyConfusables,
            _ => Self::NotConfusable,
        };
    }
}

fn warning_required(locales: &FxHashMap<Script, ConfusablesState>) -> bool {
    locales
        .iter()
        .any(|(_loc, state)| matches!(state, ConfusablesState::OnlyConfusables))
}

impl<'tcx> LateLintPass<'tcx> for MixedLocaleIdents {
    fn check_name(&mut self, cx: &LateContext<'tcx>, span: Span, ident: Symbol) {
        let ident_name = ident.to_string();

        // First pass just to check whether identifier is fully ASCII,
        // without any expensive actions.
        // Most of identifiers are *expected* to be ASCII to it's better
        // to return early if possible.
        if ident_name.is_ascii() {
            return;
        }

        // Iterate through identifier with respect to its case
        // and checks whether it contains mixed locales in a single identifier.
        let ident_case = detect_case(&ident_name);
        // Positions of the identifier part being checked.
        // Used in report to render only relevant part.
        let (mut ident_part_start, mut ident_part_end): (usize, usize) = (0, 0);
        // List of locales used in the *identifier part*
        let mut used_locales: FxHashMap<Script, ConfusablesState> = FxHashMap::default();
        for (id, symbol) in ident_name.chars().enumerate() {
            ident_part_end = id;

            // Check whether we've reached the next identifier part.
            let is_next_identifier = match ident_case {
                Case::Camel => symbol.is_uppercase(),
                Case::Snake => symbol == '_',
                Case::Mixed => symbol.is_uppercase() || symbol == '_',
            };

            if is_next_identifier {
                if warning_required(&used_locales) {
                    // We've found the part that has multiple locales,
                    // no further analysis is required.
                    break;
                } else {
                    // Clear everything and start checking the next identifier.
                    ident_part_start = id;
                    used_locales.clear();
                }
            }

            let script = symbol.script();
            if script != Script::Common && script != Script::Unknown {
                used_locales
                    .entry(script)
                    .and_modify(|e| e.update(symbol))
                    .or_insert_with(|| ConfusablesState::from_char(symbol));
            }
        }

        if warning_required(&used_locales) {
            let ident_part = &ident_name[ident_part_start..=ident_part_end];
            let locales: Vec<&'static str> = used_locales
                .iter()
                .filter_map(|(loc, state)| match state {
                    ConfusablesState::OnlyConfusables => Some(loc.full_name()),
                    ConfusablesState::NotConfusable => None,
                })
                .collect();

            assert!(
                !locales.is_empty(),
                "Warning is required; having no locales to report is a bug"
            );

            let message = format!(
                "identifier part `{}` contains confusables-only symbols from the following locales: {}",
                ident_part,
                locales.join(", "),
            );

            span_lint(cx, MIXED_LOCALE_IDENTS, span, &message);
        }
    }
}
