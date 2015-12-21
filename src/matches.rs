use rustc::lint::*;
use rustc_front::hir::*;
use rustc::middle::ty;
use syntax::ast::Lit_::LitBool;
use syntax::codemap::Span;

use utils::{snippet, span_lint, span_help_and_lint, in_external_macro, expr_block};

/// **What it does:** This lint checks for matches with a single arm where an `if let` will usually suffice. It is `Warn` by default.
///
/// **Why is this bad?** Just readability – `if let` nests less than a `match`.
///
/// **Known problems:** None
///
/// **Example:**
/// ```
/// match x {
///     Some(ref foo) -> bar(foo),
///     _ => ()
/// }
/// ```
declare_lint!(pub SINGLE_MATCH, Warn,
              "a match statement with a single nontrivial arm (i.e, where the other arm \
               is `_ => {}`) is used; recommends `if let` instead");
/// **What it does:** This lint checks for matches where all arms match a reference, suggesting to remove the reference and deref the matched expression instead. It is `Warn` by default.
///
/// **Why is this bad?** It just makes the code less readable. That reference destructuring adds nothing to the code.
///
/// **Known problems:** None
///
/// **Example:**
///
/// ```
/// match x {
///     &A(ref y) => foo(y),
///     &B => bar(),
///     _ => frob(&x),
/// }
/// ```
declare_lint!(pub MATCH_REF_PATS, Warn,
              "a match has all arms prefixed with `&`; the match expression can be \
               dereferenced instead");
/// **What it does:** This lint checks for matches where match expression is a `bool`. It suggests to replace the expression with an `if...else` block. It is `Warn` by default.
///
/// **Why is this bad?** It makes the code less readable.
///
/// **Known problems:** None
///
/// **Example:**
///
/// ```
/// let condition: bool = true;
/// match condition {
///     true => foo(),
///     false => bar(),
/// }
/// ```
declare_lint!(pub MATCH_BOOL, Warn,
              "a match on boolean expression; recommends `if..else` block instead");

#[allow(missing_copy_implementations)]
pub struct MatchPass;

impl LintPass for MatchPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(SINGLE_MATCH, MATCH_REF_PATS, MATCH_BOOL)
    }
}

impl LateLintPass for MatchPass {
    fn check_expr(&mut self, cx: &LateContext, expr: &Expr) {
        if in_external_macro(cx, expr.span) {
            return;
        }
        if let ExprMatch(ref ex, ref arms, MatchSource::Normal) = expr.node {
            // check preconditions for SINGLE_MATCH
            // only two arms
            if arms.len() == 2 && arms[0].pats.len() == 1 && arms[0].guard.is_none() &&
               arms[1].pats.len() == 1 && arms[1].guard.is_none() &&
               arms[1].pats[0].node == PatWild && is_unit_expr(&arms[1].body) &&
               (cx.tcx.expr_ty(ex).sty != ty::TyBool || cx.current_level(MATCH_BOOL) == Allow) {
                span_help_and_lint(cx,
                                   SINGLE_MATCH,
                                   expr.span,
                                   "you seem to be trying to use match for destructuring a \
                                    single pattern. Consider using `if let`",
                                   &format!("try\nif let {} = {} {}",
                                            snippet(cx, arms[0].pats[0].span, ".."),
                                            snippet(cx, ex.span, ".."),
                                            expr_block(cx, &arms[0].body, None, "..")));
            }

            // check preconditions for MATCH_BOOL
            // type of expression == bool
            if cx.tcx.expr_ty(ex).sty == ty::TyBool {
                if arms.len() == 2 && arms[0].pats.len() == 1 {
                    // no guards
                    let exprs = if let PatLit(ref arm_bool) = arms[0].pats[0].node {
                        if let ExprLit(ref lit) = arm_bool.node {
                            match lit.node {
                                LitBool(true) => Some((&*arms[0].body, &*arms[1].body)),
                                LitBool(false) => Some((&*arms[1].body, &*arms[0].body)),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    if let Some((ref true_expr, ref false_expr)) = exprs {
                        if !is_unit_expr(true_expr) {
                            if !is_unit_expr(false_expr) {
                                span_help_and_lint(cx,
                                                   MATCH_BOOL,
                                                   expr.span,
                                                   "you seem to be trying to match on a boolean \
                                                    expression. Consider using an if..else block:",
                                                   &format!("try\nif {} {} else {}",
                                                            snippet(cx, ex.span, "b"),
                                                            expr_block(cx, true_expr, None, ".."),
                                                            expr_block(cx,
                                                                       false_expr,
                                                                       None,
                                                                       "..")));
                            } else {
                                span_help_and_lint(cx,
                                                   MATCH_BOOL,
                                                   expr.span,
                                                   "you seem to be trying to match on a boolean \
                                                    expression. Consider using an if..else block:",
                                                   &format!("try\nif {} {}",
                                                            snippet(cx, ex.span, "b"),
                                                            expr_block(cx, true_expr, None, "..")));
                            }
                        } else if !is_unit_expr(false_expr) {
                            span_help_and_lint(cx,
                                               MATCH_BOOL,
                                               expr.span,
                                               "you seem to be trying to match on a boolean \
                                                expression. Consider using an if..else block:",
                                               &format!("try\nif !{} {}",
                                                        snippet(cx, ex.span, "b"),
                                                        expr_block(cx, false_expr, None, "..")));
                        } else {
                            span_lint(cx,
                                      MATCH_BOOL,
                                      expr.span,
                                      "you seem to be trying to match on a boolean expression. \
                                       Consider using an if..else block");
                        }
                    } else {
                        span_lint(cx,
                                  MATCH_BOOL,
                                  expr.span,
                                  "you seem to be trying to match on a boolean expression. \
                                   Consider using an if..else block");
                    }
                } else {
                    span_lint(cx,
                              MATCH_BOOL,
                              expr.span,
                              "you seem to be trying to match on a boolean expression. Consider \
                               using an if..else block");
                }
            }
        }
        if let ExprMatch(ref ex, ref arms, source) = expr.node {
            // check preconditions for MATCH_REF_PATS
            if has_only_ref_pats(arms) {
                if let ExprAddrOf(Mutability::MutImmutable, ref inner) = ex.node {
                    let template = match_template(cx, expr.span, source, "", inner);
                    span_lint(cx,
                              MATCH_REF_PATS,
                              expr.span,
                              &format!("you don't need to add `&` to both the expression and \
                                        the patterns: use `{}`",
                                       template));
                } else {
                    let template = match_template(cx, expr.span, source, "*", ex);
                    span_lint(cx,
                              MATCH_REF_PATS,
                              expr.span,
                              &format!("instead of prefixing all patterns with `&`, you can \
                                        dereference the expression: `{}`",
                                       template));
                }
            }
        }
    }
}

fn is_unit_expr(expr: &Expr) -> bool {
    match expr.node {
        ExprTup(ref v) if v.is_empty() => true,
        ExprBlock(ref b) if b.stmts.is_empty() && b.expr.is_none() => true,
        _ => false,
    }
}

fn has_only_ref_pats(arms: &[Arm]) -> bool {
    let mapped = arms.iter()
                     .flat_map(|a| &a.pats)
                     .map(|p| {
                         match p.node {
                             PatRegion(..) => Some(true),  // &-patterns
                             PatWild => Some(false),   // an "anything" wildcard is also fine
                             _ => None,                    // any other pattern is not fine
                         }
                     })
                     .collect::<Option<Vec<bool>>>();
    // look for Some(v) where there's at least one true element
    mapped.map_or(false, |v| v.iter().any(|el| *el))
}

fn match_template(cx: &LateContext,
                  span: Span,
                  source: MatchSource,
                  op: &str,
                  expr: &Expr)
                  -> String {
    let expr_snippet = snippet(cx, expr.span, "..");
    match source {
        MatchSource::Normal => format!("match {}{} {{ ...", op, expr_snippet),
        MatchSource::IfLetDesugar { .. } => format!("if let ... = {}{} {{", op, expr_snippet),
        MatchSource::WhileLetDesugar => format!("while let ... = {}{} {{", op, expr_snippet),
        MatchSource::ForLoopDesugar => {
            cx.sess().span_bug(span, "for loop desugared to match with &-patterns!")
        }
    }
}
