use crate::utils;
use if_chain::if_chain;
use rustc_errors::Applicability;
use rustc_hir::{def, Arm, Expr, ExprKind, PatKind, QPath};
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::{declare_lint_pass, declare_tool_lint};

declare_clippy_lint! {
    /// **What it does:**
    /// Finds patterns that can be encoded more concisely with `Option::unwrap_or`.
    ///
    /// **Why is this bad?**
    /// Concise code helps focusing on behavior instead of boilerplate.
    ///
    /// **Known problems:** None.
    ///
    /// **Example:**
    /// ```rust
    /// match int_optional {
    ///     Some(v) => v,
    ///     None => 1,
    /// }
    /// ```
    ///
    /// Use instead:
    /// ```rust
    /// int_optional.unwrap_or(1)
    /// ```
    pub LESS_CONCISE_THAN_OPTION_UNWRAP_OR,
    pedantic,
    "finds patterns that can be encoded more concisely with `Option::unwrap_or`"
}

declare_lint_pass!(LessConciseThan => [LESS_CONCISE_THAN_OPTION_UNWRAP_OR]);

impl LateLintPass<'_> for LessConciseThan {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        if utils::in_macro(expr.span) {
            return;
        }
        if lint_option_unwrap_or_case(cx, expr) {
            return;
        }
    }
}

fn lint_option_unwrap_or_case<'tcx>(cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) -> bool {
    #[allow(clippy::needless_bool)]
    fn applicable_none_arm<'a>(arms: &'a [Arm<'a>]) -> Option<&'a Arm<'a>> {
        if_chain! {
            if arms.len() == 2;
            if arms.iter().all(|arm| arm.guard.is_none());
            if let Some((idx, none_arm)) = arms.iter().enumerate().find(|(_, arm)|
               if_chain! {
                    if let PatKind::Path(ref qpath) = arm.pat.kind;
                    if utils::match_qpath(qpath, &utils::paths::OPTION_NONE);
                    then { true }
                    else { false }
               }
            );
            let some_arm = &arms[1 - idx];
            if let PatKind::TupleStruct(ref some_qpath, &[some_binding], _) = some_arm.pat.kind;
            if utils::match_qpath(some_qpath, &utils::paths::OPTION_SOME);
            if let PatKind::Binding(_, binding_hir_id, ..) = some_binding.kind;
            if let ExprKind::Path(QPath::Resolved(_, body_path)) = some_arm.body.kind;
            if let def::Res::Local(body_path_hir_id) = body_path.res;
            if body_path_hir_id == binding_hir_id;
            then { Some(none_arm) }
            else { None }
        }
    }
    if_chain! {
      if !utils::usage::contains_return_break_continue_macro(expr);
      if let ExprKind::Match (match_expr, match_arms, _) = expr.kind;
      let ty = cx.typeck_results().expr_ty(match_expr);
      if utils::is_type_diagnostic_item(cx, ty, sym!(option_type));
      if let Some(none_arm) = applicable_none_arm(match_arms);
      if let Some(match_expr_snippet) = utils::snippet_opt(cx, match_expr.span);
      if let Some(none_body_snippet) = utils::snippet_opt(cx, none_arm.body.span);
      if let Some(indent) = utils::indent_of(cx, expr.span);
      then {
          let reindented_none_body =
              utils::reindent_multiline(none_body_snippet.into(), true, Some(indent));
          let eager_eval = utils::eager_or_lazy::is_eagerness_candidate(cx, none_arm.body);
          let method = if eager_eval {
              "unwrap_or"
          } else {
              "unwrap_or_else"
          };
          utils::span_lint_and_sugg(
              cx,
              LESS_CONCISE_THAN_OPTION_UNWRAP_OR, expr.span,
              "this pattern can be more concisely encoded with `Option::unwrap_or`",
              "replace with",
              format!(
                  "{}.{}({}{})",
                  match_expr_snippet,
                  method,
                  if eager_eval { ""} else { "|| " },
                  reindented_none_body
              ),
              Applicability::MachineApplicable,
          );
          true
      } else { false}
    }
}