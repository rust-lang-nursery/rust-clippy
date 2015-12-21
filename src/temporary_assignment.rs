use rustc::lint::{LateContext, LateLintPass, LintArray, LintPass};
use rustc_front::hir::{Expr, ExprAssign, ExprField, ExprStruct, ExprTup, ExprTupField};

use utils::is_adjusted;
use utils::span_lint;

/// **What it does:** This lint `Warn`s on creating a struct or tuple just to assign a value in it.
///
/// **Why is this bad?** Readability. If the struct is only created to be updated, why not write the struct you want in the first place?
///
/// **Known problems:** None.
///
/// **Example:** `(0, 0).0 = 1`
declare_lint! {
    pub TEMPORARY_ASSIGNMENT,
    Warn,
    "assignments to temporaries"
}

fn is_temporary(expr: &Expr) -> bool {
    match expr.node {
        ExprStruct(..) |
        ExprTup(..) => true,
        _ => false,
    }
}

#[derive(Copy, Clone)]
pub struct TemporaryAssignmentPass;

impl LintPass for TemporaryAssignmentPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(TEMPORARY_ASSIGNMENT)
    }
}

impl LateLintPass for TemporaryAssignmentPass {
    fn check_expr(&mut self, cx: &LateContext, expr: &Expr) {
        if let ExprAssign(ref target, _) = expr.node {
            match target.node {
                ExprField(ref base, _) | ExprTupField(ref base, _) => {
                    if is_temporary(base) && !is_adjusted(cx, base) {
                        span_lint(cx,
                                  TEMPORARY_ASSIGNMENT,
                                  expr.span,
                                  "assignment to temporary");
                    }
                }
                _ => (),
            }
        }
    }
}
