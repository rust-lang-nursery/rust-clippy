//! checks for attributes

use rustc::lint::*;
use rustc_front::hir::*;
use reexport::*;
use syntax::codemap::Span;
use syntax::attr::*;
use syntax::ast::{Attribute, MetaList, MetaWord};
use utils::{in_macro, match_path, span_lint};

declare_lint! { pub INLINE_ALWAYS, Warn,
    "`#[inline(always)]` is a bad idea in most cases" }


#[derive(Copy,Clone)]
pub struct AttrPass;

impl LintPass for AttrPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(INLINE_ALWAYS)
    }
}

impl LateLintPass for AttrPass {
    fn check_item(&mut self, cx: &LateContext, item: &Item) {
        if is_relevant_item(item) {
            check_attrs(cx, item.span, &item.ident, &item.attrs)
        }
    }

    fn check_impl_item(&mut self, cx: &LateContext, item: &ImplItem) {
        if is_relevant_impl(item) {
            check_attrs(cx, item.span, &item.ident, &item.attrs)
        }
    }

    fn check_trait_item(&mut self, cx: &LateContext, item: &TraitItem) {
        if is_relevant_trait(item) {
            check_attrs(cx, item.span, &item.ident, &item.attrs)
        }
    }
}

fn is_relevant_item(item: &Item) -> bool {
    if let &ItemFn(_, _, _, _, _, ref block) = &item.node {
        is_relevant_block(block)
    } else {
        false
    }
}

fn is_relevant_impl(item: &ImplItem) -> bool {
    match item.node {
        MethodImplItem(_, ref block) => is_relevant_block(block),
        _ => false,
    }
}

fn is_relevant_trait(item: &TraitItem) -> bool {
    match item.node {
        MethodTraitItem(_, None) => true,
        MethodTraitItem(_, Some(ref block)) => is_relevant_block(block),
        _ => false,
    }
}

fn is_relevant_block(block: &Block) -> bool {
    for stmt in &block.stmts {
        match stmt.node {
            StmtDecl(_, _) => return true,
            StmtExpr(ref expr, _) | StmtSemi(ref expr, _) => {
                return is_relevant_expr(expr);
            }
        }
    }
    block.expr.as_ref().map_or(false, |e| is_relevant_expr(e))
}

fn is_relevant_expr(expr: &Expr) -> bool {
    match expr.node {
        ExprBlock(ref block) => is_relevant_block(block),
        ExprRet(Some(ref e)) => is_relevant_expr(e),
        ExprRet(None) | ExprBreak(_) => false,
        ExprCall(ref path_expr, _) => {
            if let ExprPath(_, ref path) = path_expr.node {
                !match_path(path, &["std", "rt", "begin_unwind"])
            } else {
                true
            }
        }
        _ => true,
    }
}

fn check_attrs(cx: &LateContext, span: Span, ident: &Ident, attrs: &[Attribute]) {
    if in_macro(cx, span) {
        return;
    }

    for attr in attrs {
        if let MetaList(ref inline, ref values) = attr.node.value.node {
            if values.len() != 1 || inline != &"inline" {
                continue;
            }
            if let MetaWord(ref always) = values[0].node {
                if always != &"always" {
                    continue;
                }
                span_lint(cx,
                          INLINE_ALWAYS,
                          attr.span,
                          &format!(
                    "you have declared `#[inline(always)]` on `{}`. This \
                     is usually a bad idea. Are you sure?",
                    ident.name));
            }
        }
    }
}
