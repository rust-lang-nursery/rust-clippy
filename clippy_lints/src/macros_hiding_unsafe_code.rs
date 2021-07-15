use clippy_utils::{diagnostics::span_lint_and_sugg, in_macro, is_lint_allowed, source::snippet_with_applicability};
use rustc_errors::Applicability;
use rustc_hir::{intravisit::FnKind, Block, BlockCheckMode, Body, FnDecl, FnSig, HirId, UnsafeSource, Unsafety};
use rustc_lint::{
    builtin::{UNSAFE_OP_IN_UNSAFE_FN, UNUSED_UNSAFE},
    LateContext, LateLintPass, LintContext,
};
use rustc_middle::lint::in_external_macro;
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::Span;

declare_clippy_lint! {
    /// **What it does:** Checks for macro calls inside an `unsafe` function which expansion
    /// contains an `unsafe` block, while the macro call is not wrapped in an `unsafe` block
    /// itself. This lint only triggers in functions where the `unsafe_op_in_unsafe_fn` lint is
    /// enabled.
    ///
    /// **Why is this bad?** This hides an unsafe operation inside a macro call. This is against
    /// the intention of the `unsafe_op_in_unsafe_fn` lint, which is meant to make unsafe code more
    /// visible by requiring `unsafe` blocks also in `unsafe` functions.
    ///
    /// **Known problems:**
    /// - In some cases the intention of the macro is to actually hide the unsafety, because the
    /// macro itself ensures the safety of the `unsafe` operation.
    /// - For local macros, either an `#[allow(unused_unsafe)]` has to be added to the new unsafe
    /// block or the unsafe block inside the macro has to be removed.
    ///
    /// **Example:**
    ///
    /// ```rust
    /// macro_rules! unsafe_macro {
    ///     ($e:expr) => {
    ///         unsafe { $e };
    ///     };
    /// }
    ///
    /// #[warn(unsafe_op_in_unsafe_fn)]
    /// unsafe fn foo(x: *const usize) {
    ///     unsafe_macro!(std::ptr::read(x));
    /// }
    /// ```
    /// Use instead:
    /// ```rust
    /// # macro_rules! unsafe_macro {
    /// #     ($e:expr) => {
    /// #         unsafe { $e };
    /// #     };
    /// # }
    /// #[warn(unsafe_op_in_unsafe_fn)]
    /// unsafe fn foo(x: *const usize) {
    ///     #[allow(unused_unsafe)] unsafe { unsafe_macro!(std::ptr::read(x)) };
    /// }
    /// ```
    pub MACROS_HIDING_UNSAFE_CODE,
    restriction,
    "macros hiding unsafe code, while `unsafe_op_in_unsafe_fn` is enabled"
}

#[derive(Clone, Copy, Default)]
pub struct MacrosHidingUnsafeCode {
    in_unsafe_fn: bool,
    in_unsafe_block: usize,
}

impl_lint_pass!(MacrosHidingUnsafeCode => [MACROS_HIDING_UNSAFE_CODE]);

impl LateLintPass<'_> for MacrosHidingUnsafeCode {
    fn check_block(&mut self, cx: &LateContext<'_>, block: &Block<'_>) {
        if let BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided) = block.rules {
            if in_macro(block.span) {
                if self.in_unsafe_fn
                    && self.in_unsafe_block == 0
                    && !is_lint_allowed(cx, UNSAFE_OP_IN_UNSAFE_FN, block.hir_id)
                {
                    let macro_call_span = block.span.source_callsite();
                    let unused_unsafe_sugg = if !in_external_macro(cx.sess(), block.span)
                        && !is_lint_allowed(cx, UNUSED_UNSAFE, block.hir_id)
                    {
                        "#[allow(unused_unsafe)] "
                    } else {
                        ""
                    };
                    let mut applicability = Applicability::MaybeIncorrect;
                    span_lint_and_sugg(
                        cx,
                        MACROS_HIDING_UNSAFE_CODE,
                        macro_call_span,
                        "this macro call hides unsafe code",
                        "wrap it in an `unsafe` block",
                        format!(
                            "{}unsafe {{ {} }}",
                            unused_unsafe_sugg,
                            snippet_with_applicability(cx, macro_call_span, "...", &mut applicability),
                        ),
                        applicability,
                    );
                }
            } else {
                self.in_unsafe_block = self.in_unsafe_block.saturating_add(1);
            }
        }
    }

    fn check_block_post(&mut self, _: &LateContext<'_>, block: &Block<'_>) {
        if let BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided) = block.rules {
            if !in_macro(block.span) {
                self.in_unsafe_block = self.in_unsafe_block.saturating_sub(1);
            }
        }
    }

    fn check_fn(&mut self, _: &LateContext<'_>, fn_kind: FnKind<'_>, _: &FnDecl<'_>, _: &Body<'_>, _: Span, _: HirId) {
        if is_unsafe_fn(fn_kind) {
            self.in_unsafe_fn = true;
        }
    }

    fn check_fn_post(
        &mut self,
        _: &LateContext<'_>,
        fn_kind: FnKind<'_>,
        _: &FnDecl<'_>,
        _: &Body<'_>,
        _: Span,
        _: HirId,
    ) {
        if is_unsafe_fn(fn_kind) {
            self.in_unsafe_fn = false;
        }
    }
}

fn is_unsafe_fn(fn_kind: FnKind<'_>) -> bool {
    match fn_kind {
        FnKind::ItemFn(_, _, header, _) | FnKind::Method(_, &FnSig { header, .. }, _) => {
            matches!(header.unsafety, Unsafety::Unsafe)
        },
        FnKind::Closure => false,
    }
}
