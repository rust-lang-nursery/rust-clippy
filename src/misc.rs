use syntax::ptr::P;
use syntax::ast;
use syntax::ast::*;
use syntax::ast_util::{is_comparison_binop, binop_to_string};
use syntax::visit::{FnKind};
use rustc::lint::{Context, LintPass, LintArray, Lint, Level};
use rustc::middle::ty;
use syntax::codemap::{Span, Spanned};

use utils::{match_path, snippet, snippet_block, span_lint, span_help_and_lint, walk_ptrs_ty};

/// Handles uncategorized lints
/// Currently handles linting of if-let-able matches
#[allow(missing_copy_implementations)]
pub struct MiscPass;


declare_lint!(pub SINGLE_MATCH, Warn,
              "a match statement with a single nontrivial arm (i.e, where the other arm \
               is `_ => {}`) is used; recommends `if let` instead");

impl LintPass for MiscPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(SINGLE_MATCH)
    }

    fn check_expr(&mut self, cx: &Context, expr: &Expr) {
        if let ExprMatch(ref ex, ref arms, ast::MatchSource::Normal) = expr.node {
            // check preconditions: only two arms
            if arms.len() == 2 &&
                // both of the arms have a single pattern and no guard
                arms[0].pats.len() == 1 && arms[0].guard.is_none() &&
                arms[1].pats.len() == 1 && arms[1].guard.is_none() &&
                // and the second pattern is a `_` wildcard: this is not strictly necessary,
                // since the exhaustiveness check will ensure the last one is a catch-all,
                // but in some cases, an explicit match is preferred to catch situations
                // when an enum is extended, so we don't consider these cases
                arms[1].pats[0].node == PatWild(PatWildSingle)
            {
                // check if we have content for an "else" block
                let has_else_content = match arms[1].body.node {
                    ExprTup(ref v) if v.is_empty() => false,
                    ExprBlock(ref b) if b.stmts.is_empty() && b.expr.is_none() => false,
                    _ => true,
                };
                let true_block = format_as_block(cx, &*arms[0].body, "");
                let else_clause = if has_else_content {
                    format_as_block(cx, &*arms[1].body, " else ")
                } else {
                    "".into()
                };
                span_help_and_lint(cx, SINGLE_MATCH, expr.span,
                      "you seem to be trying to use match for \
                      destructuring a single pattern. Did you mean to \
                      use `if let`?",
                      &*format!("try\nif let {} = {} {}{}",
                                snippet(cx, arms[0].pats[0].span, ".."),
                                snippet(cx, ex.span, ".."),
                                true_block, else_clause)
                );
            }
        }
    }
}

fn format_as_block(cx: &Context, expr: &Expr, prefix: &str) -> String {
    let code = snippet_block(cx, expr.span, "..");
    if let ExprBlock(_) = expr.node {
        format!("{}{}", prefix, code)
    } else {
        format!("{}{{ {} }}", prefix, code)
    }
}


declare_lint!(pub TOPLEVEL_REF_ARG, Warn,
              "a function argument is declared `ref` (i.e. `fn foo(ref x: u8)`, but not \
               `fn foo((ref x, ref y): (u8, u8))`)");

#[allow(missing_copy_implementations)]
pub struct TopLevelRefPass;

impl LintPass for TopLevelRefPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(TOPLEVEL_REF_ARG)
    }

    fn check_fn(&mut self, cx: &Context, _: FnKind, decl: &FnDecl, _: &Block, _: Span, _: NodeId) {
        for ref arg in &decl.inputs {
            if let PatIdent(BindByRef(_), _, _) = arg.pat.node {
                span_lint(cx,
                    TOPLEVEL_REF_ARG,
                    arg.pat.span,
                    "`ref` directly on a function argument is ignored. Consider using a reference type instead."
                );
            }
        }
    }
}

declare_lint!(pub CMP_NAN, Deny,
              "comparisons to NAN (which will always return false, which is probably not intended)");

#[derive(Copy,Clone)]
pub struct CmpNan;

impl LintPass for CmpNan {
    fn get_lints(&self) -> LintArray {
        lint_array!(CMP_NAN)
    }

    fn check_expr(&mut self, cx: &Context, expr: &Expr) {
        if let ExprBinary(ref cmp, ref left, ref right) = expr.node {
            if is_comparison_binop(cmp.node) {
                if let &ExprPath(_, ref path) = &left.node {
                    check_nan(cx, path, expr.span);
                }
                if let &ExprPath(_, ref path) = &right.node {
                    check_nan(cx, path, expr.span);
                }
            }
        }
    }
}

fn check_nan(cx: &Context, path: &Path, span: Span) {
    path.segments.last().map(|seg| if seg.identifier.name == "NAN" {
        span_lint(cx, CMP_NAN, span,
                  "doomed comparison with NAN, use `std::{f32,f64}::is_nan()` instead");
    });
}

declare_lint!(pub FLOAT_CMP, Warn,
              "using `==` or `!=` on float values (as floating-point operations \
               usually involve rounding errors, it is always better to check for approximate \
               equality within small bounds)");

#[derive(Copy,Clone)]
pub struct FloatCmp;

impl LintPass for FloatCmp {
    fn get_lints(&self) -> LintArray {
        lint_array!(FLOAT_CMP)
    }

    fn check_expr(&mut self, cx: &Context, expr: &Expr) {
        if let ExprBinary(ref cmp, ref left, ref right) = expr.node {
            let op = cmp.node;
            if (op == BiEq || op == BiNe) && (is_float(cx, left) || is_float(cx, right)) {
                span_lint(cx, FLOAT_CMP, expr.span, &format!(
                    "{}-comparison of f32 or f64 detected. Consider changing this to \
                     `abs({} - {}) < epsilon` for some suitable value of epsilon",
                    binop_to_string(op), snippet(cx, left.span, ".."),
                    snippet(cx, right.span, "..")));
            }
        }
    }
}

fn is_float(cx: &Context, expr: &Expr) -> bool {
    if let ty::TyFloat(_) = walk_ptrs_ty(cx.tcx.expr_ty(expr)).sty {
        true
    } else {
        false
    }
}

declare_lint!(pub PRECEDENCE, Warn,
              "expressions where precedence may trip up the unwary reader of the source; \
               suggests adding parentheses, e.g. `x << 2 + y` will be parsed as `x << (2 + y)`");

#[derive(Copy,Clone)]
pub struct Precedence;

impl LintPass for Precedence {
    fn get_lints(&self) -> LintArray {
        lint_array!(PRECEDENCE)
    }

    fn check_expr(&mut self, cx: &Context, expr: &Expr) {
        if let ExprBinary(Spanned { node: op, ..}, ref left, ref right) = expr.node {
            if is_bit_op(op) && (is_arith_expr(left) || is_arith_expr(right)) {
                span_lint(cx, PRECEDENCE, expr.span,
                    "operator precedence can trip the unwary. Consider adding parentheses \
                     to the subexpression");
            }
        }
    }
}

fn is_arith_expr(expr : &Expr) -> bool {
    match expr.node {
        ExprBinary(Spanned { node: op, ..}, _, _) => is_arith_op(op),
        _ => false
    }
}

fn is_bit_op(op : BinOp_) -> bool {
    match op {
        BiBitXor | BiBitAnd | BiBitOr | BiShl | BiShr => true,
        _ => false
    }
}

fn is_arith_op(op : BinOp_) -> bool {
    match op {
        BiAdd | BiSub | BiMul | BiDiv | BiRem => true,
        _ => false
    }
}

declare_lint!(pub CMP_OWNED, Warn,
              "creating owned instances for comparing with others, e.g. `x == \"foo\".to_string()`");

#[derive(Copy,Clone)]
pub struct CmpOwned;

impl LintPass for CmpOwned {
    fn get_lints(&self) -> LintArray {
        lint_array!(CMP_OWNED)
    }

    fn check_expr(&mut self, cx: &Context, expr: &Expr) {
        if let ExprBinary(ref cmp, ref left, ref right) = expr.node {
            if is_comparison_binop(cmp.node) {
                check_to_owned(cx, left, right.span);
                check_to_owned(cx, right, left.span)
            }
        }
    }
}

fn check_to_owned(cx: &Context, expr: &Expr, other_span: Span) {
    match &expr.node {
        &ExprMethodCall(Spanned{node: ref ident, ..}, _, ref args) => {
            let name = ident.name;
            if name == "to_string" ||
                name == "to_owned" && is_str_arg(cx, args) {
                    span_lint(cx, CMP_OWNED, expr.span, &format!(
                        "this creates an owned instance just for comparison. \
                         Consider using `{}.as_slice()` to compare without allocation",
                        snippet(cx, other_span, "..")))
                }
        },
        &ExprCall(ref path, _) => {
            if let &ExprPath(None, ref path) = &path.node {
                if match_path(path, &["String", "from_str"]) ||
                    match_path(path, &["String", "from"]) {
                        span_lint(cx, CMP_OWNED, expr.span, &format!(
                            "this creates an owned instance just for comparison. \
                             Consider using `{}.as_slice()` to compare without allocation",
                            snippet(cx, other_span, "..")))
                    }
            }
        },
        _ => ()
    }
}

fn is_str_arg(cx: &Context, args: &[P<Expr>]) -> bool {
    args.len() == 1 && if let ty::TyStr =
        walk_ptrs_ty(cx.tcx.expr_ty(&*args[0])).sty { true } else { false }
}

declare_lint!(pub MODULO_ONE, Warn, "taking a number modulo 1, which always returns 0");

#[derive(Copy,Clone)]
pub struct ModuloOne;

impl LintPass for ModuloOne {
    fn get_lints(&self) -> LintArray {
        lint_array!(MODULO_ONE)
    }

    fn check_expr(&mut self, cx: &Context, expr: &Expr) {
        if let ExprBinary(ref cmp, _, ref right) = expr.node {
            if let &Spanned {node: BinOp_::BiRem, ..} = cmp {
                if is_lit_one(right) {
                    cx.span_lint(MODULO_ONE, expr.span, "any number modulo 1 will be 0");
                }
            }
        }
    }
}

fn is_lit_one(expr: &Expr) -> bool {
    if let ExprLit(ref spanned) = expr.node {
        if let LitInt(1, _) = spanned.node {
            return true;
        }
    }
    false
}
