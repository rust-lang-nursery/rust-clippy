use clippy_utils::diagnostics::span_lint_and_note;
use clippy_utils::source::snippet;
use clippy_utils::visitors::LocalUsedVisitor;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::Res;
use rustc_hir::hir_id::ItemLocalId;
use rustc_hir::{Block, Body, Expr, ExprKind, HirId, Node, Pat, PatKind, QPath, UnOp};
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::symbol::Symbol;

declare_clippy_lint! {
    /// **What it does:** Checks for bindings that shadow other bindings already in
    /// scope, while just changing reference level or mutability.
    ///
    /// **Why is this bad?** Not much, in fact it's a very common pattern in Rust
    /// code. Still, some may opt to avoid it in their code base, they can set this
    /// lint to `Warn`.
    ///
    /// **Known problems:** This lint, as the other shadowing related lints,
    /// currently only catches very simple patterns.
    ///
    /// **Example:**
    /// ```rust
    /// # let x = 1;
    /// // Bad
    /// let x = &x;
    ///
    /// // Good
    /// let y = &x; // use different variable name
    /// ```
    pub SHADOW_SAME,
    restriction,
    "rebinding a name to itself, e.g., `let mut x = &mut x`"
}

declare_clippy_lint! {
    /// **What it does:** Checks for bindings that shadow other bindings already in
    /// scope, while reusing the original value.
    ///
    /// **Why is this bad?** Not too much, in fact it's a common pattern in Rust
    /// code. Still, some argue that name shadowing like this hurts readability,
    /// because a value may be bound to different things depending on position in
    /// the code.
    ///
    /// **Known problems:** This lint, as the other shadowing related lints,
    /// currently only catches very simple patterns.
    ///
    /// **Example:**
    /// ```rust
    /// let x = 2;
    /// let x = x + 1;
    /// ```
    /// use different variable name:
    /// ```rust
    /// let x = 2;
    /// let y = x + 1;
    /// ```
    pub SHADOW_REUSE,
    restriction,
    "rebinding a name to an expression that re-uses the original value, e.g., `let x = x + 1`"
}

declare_clippy_lint! {
    /// **What it does:** Checks for bindings that shadow other bindings already in
    /// scope, either without a initialization or with one that does not even use
    /// the original value.
    ///
    /// **Why is this bad?** Name shadowing can hurt readability, especially in
    /// large code bases, because it is easy to lose track of the active binding at
    /// any place in the code. This can be alleviated by either giving more specific
    /// names to bindings or introducing more scopes to contain the bindings.
    ///
    /// **Known problems:** This lint, as the other shadowing related lints,
    /// currently only catches very simple patterns. Note that
    /// `allow`/`warn`/`deny`/`forbid` attributes only work on the function level
    /// for this lint.
    ///
    /// **Example:**
    /// ```rust
    /// # let y = 1;
    /// # let z = 2;
    /// let x = y;
    ///
    /// // Bad
    /// let x = z; // shadows the earlier binding
    ///
    /// // Good
    /// let w = z; // use different variable name
    /// ```
    pub SHADOW_UNRELATED,
    pedantic,
    "rebinding a name without even using the original value"
}

#[derive(Default)]
pub(crate) struct Shadow {
    bindings: Vec<FxHashMap<Symbol, Vec<ItemLocalId>>>,
}

impl_lint_pass!(Shadow => [SHADOW_SAME, SHADOW_REUSE, SHADOW_UNRELATED]);

impl<'tcx> LateLintPass<'tcx> for Shadow {
    fn check_pat(&mut self, cx: &LateContext<'tcx>, pat: &'tcx Pat<'_>) {
        // the pattern must be a binding
        let (HirId { owner, local_id }, name) = match pat.kind {
            PatKind::Binding(_, hir_id, ident, _) if !ident.span.from_expansion() => (hir_id, ident.name),
            _ => return,
        };

        // get (or insert) the list of items for this owner and symbol
        let data = self.bindings.last_mut().unwrap();
        let items_with_name = data.entry(name).or_default();

        // check other bindings with the same name, most recently seen first
        for &prev in items_with_name.iter().rev() {
            if prev == local_id {
                // repeated binding in an `Or` pattern
                return;
            }

            // check if the scope of the binding is a subscope of the previous binding
            let scope_tree = cx.tcx.region_scope_tree(owner.to_def_id());
            let prev_scope = scope_tree.var_scope(prev);
            let scope = scope_tree.var_scope(local_id);
            if scope_tree.is_subscope_of(scope, prev_scope) {
                // finally lint
                let prev_hir_id = HirId { owner, local_id: prev };
                lint_shadow(cx, pat, prev_hir_id);
                // only lint against the "nearest" shadowed binding
                break;
            }
        }
        // store the binding
        items_with_name.push(local_id);
    }

    fn check_body(&mut self, _: &LateContext<'_>, _: &Body<'_>) {
        // Start a fresh context in each (nested) body.
        // This means that shadowing inside a closure will not be linted.
        self.bindings.push(FxHashMap::default());
    }

    fn check_body_post(&mut self, _: &LateContext<'_>, _: &Body<'_>) {
        self.bindings.pop();
    }
}

fn lint_shadow(cx: &LateContext<'_>, pat: &Pat<'_>, shadowed: HirId) {
    let (lint, msg) = match find_init(cx, pat.hir_id) {
        Some(expr) if is_self_shadow(expr, shadowed) => {
            let msg = format!(
                "`{}` is shadowed by itself in `{}`",
                snippet(cx, pat.span, "_"),
                snippet(cx, expr.span, "..")
            );
            (SHADOW_SAME, msg)
        },
        Some(expr) if LocalUsedVisitor::new(cx, shadowed).check_expr(expr) => {
            let msg = format!(
                "`{}` is shadowed by `{}` which reuses the original value",
                snippet(cx, pat.span, "_"),
                snippet(cx, expr.span, "..")
            );
            (SHADOW_REUSE, msg)
        },
        _ => {
            let msg = format!("`{}` shadows a previous, unrelated binding", snippet(cx, pat.span, "_"));
            (SHADOW_UNRELATED, msg)
        },
    };
    span_lint_and_note(
        cx,
        lint,
        pat.span,
        &msg,
        Some(cx.tcx.hir().span(shadowed)),
        "previous binding is here",
    );
}

/// Returns true if the expression is a simple transformation of a local binding such as `&x`
fn is_self_shadow(mut expr: &Expr<'_>, hir_id: HirId) -> bool {
    loop {
        expr = match expr.kind {
            ExprKind::Box(e) | ExprKind::AddrOf(_, _, e) => e,
            #[rustfmt::skip]
            ExprKind::Block(Block { stmts: [], expr: Some(e), .. }, _) => e,
            ExprKind::Unary(UnOp::Deref, e) => e,
            ExprKind::Path(QPath::Resolved(None, path)) => break path.res == Res::Local(hir_id),
            _ => break false,
        }
    }
}

/// Finds the "init" expression for a pattern: `let <pat> = <init>;` or
/// `match <init> { .., <pat> => .., .. }`
fn find_init<'tcx>(cx: &LateContext<'tcx>, hir_id: HirId) -> Option<&'tcx Expr<'tcx>> {
    for (_, node) in cx.tcx.hir().parent_iter(hir_id) {
        let init = match node {
            Node::Arm(_) | Node::Pat(_) => continue,
            Node::Expr(expr) => match expr.kind {
                ExprKind::Match(e, _, _) => Some(e),
                _ => None,
            },
            Node::Local(local) => local.init,
            _ => None,
        };
        return init;
    }
    None
}
