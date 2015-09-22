use rustc::lint::*;
use rustc_front::hir::*;
use reexport::*;
use syntax::codemap::{Span, Spanned};
use rustc_front::visit::FnKind;

use utils::{span_lint, snippet, match_path, in_external_macro};

declare_lint!(pub NEEDLESS_RETURN, Warn,
              "using a return statement like `return expr;` where an expression would suffice");
declare_lint!(pub LET_AND_RETURN, Warn,
              "creating a let-binding and then immediately returning it like `let x = expr; x` at \
               the end of a block");

#[derive(Copy, Clone)]
pub struct ReturnPass;

impl ReturnPass {
    // Check the final stmt or expr in a block for unnecessary return.
    fn check_block_return(&mut self, cx: &LateContext, block: &Block) {
        if let Some(ref expr) = block.expr {
            self.check_final_expr(cx, expr);
        } else if let Some(stmt) = block.stmts.last() {
            if let StmtSemi(ref expr, _) = stmt.node {
                if let ExprRet(Some(ref inner)) = expr.node {
                    self.emit_return_lint(cx, (expr.span, inner.span));
                }
            }
        }
    }

    // Check a the final expression in a block if it's a return.
    fn check_final_expr(&mut self, cx: &LateContext, expr: &Expr) {
        match expr.node {
            // simple return is always "bad"
            ExprRet(Some(ref inner)) => {
                self.emit_return_lint(cx, (expr.span, inner.span));
            }
            // a whole block? check it!
            ExprBlock(ref block) => {
                self.check_block_return(cx, block);
            }
            // an if/if let expr, check both exprs
            // note, if without else is going to be a type checking error anyways
            // (except for unit type functions) so we don't match it
            ExprIf(_, ref ifblock, Some(ref elsexpr)) => {
                self.check_block_return(cx, ifblock);
                self.check_final_expr(cx, elsexpr);
            }
            // a match expr, check all arms
            ExprMatch(_, ref arms, _) => {
                for arm in arms {
                    self.check_final_expr(cx, &arm.body);
                }
            }
            _ => {
            }
        }
    }

    fn emit_return_lint(&mut self, cx: &LateContext, spans: (Span, Span)) {
        if in_external_macro(cx, spans.1) {
            return;
        }
        span_lint(cx,
                  NEEDLESS_RETURN,
                  spans.0,
                  &format!(
            "unneeded return statement. Consider using `{}` \
             without the return and trailing semicolon",
            snippet(cx, spans.1, "..")))
    }

    // Check for "let x = EXPR; x"
    fn check_let_return(&mut self, cx: &LateContext, block: &Block) {
        // we need both a let-binding stmt and an expr
        if_let_chain! {
            [
                let Some(stmt) = block.stmts.last(),
                let Some(ref retexpr) = block.expr,
                let StmtDecl(ref decl, _) = stmt.node,
                let DeclLocal(ref local) = decl.node,
                let Some(ref initexpr) = local.init,
                let PatIdent(_, Spanned { node: id, .. }, _) = local.pat.node,
                let ExprPath(_, ref path) = retexpr.node,
                match_path(path, &[&id.name.as_str()])
            ], {
                self.emit_let_lint(cx, retexpr.span, initexpr.span);
            }
        }
    }

    fn emit_let_lint(&mut self, cx: &LateContext, lint_span: Span, note_span: Span) {
        if in_external_macro(cx, note_span) {
            return;
        }
        span_lint(cx,
                  LET_AND_RETURN,
                  lint_span,
                  "returning the result of a let binding from a block. Consider returning the \
                   expression directly.");
        if cx.current_level(LET_AND_RETURN) != Level::Allow {
            cx.sess().span_note(note_span, "this expression can be directly returned");
        }
    }
}

impl LintPass for ReturnPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(NEEDLESS_RETURN, LET_AND_RETURN)
    }
}

impl LateLintPass for ReturnPass {
    fn check_fn(&mut self,
                cx: &LateContext,
                _: FnKind,
                _: &FnDecl,
                block: &Block,
                _: Span,
                _: NodeId) {
        self.check_block_return(cx, block);
    }

    fn check_block(&mut self, cx: &LateContext, block: &Block) {
        self.check_let_return(cx, block);
    }
}
