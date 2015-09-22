//! Checks for usage of &Vec[_] and &String
//!
//! This lint is **warn** by default

use rustc::lint::*;
use rustc_front::hir::*;
use rustc::middle::ty;

use utils::{span_lint, match_type};
use utils::{STRING_PATH, VEC_PATH};

declare_lint! {
    pub PTR_ARG,
    Allow,
    "fn arguments of the type `&Vec<...>` or `&String`, suggesting to use `&[...]` or `&str` \
     instead, respectively"
}

#[derive(Copy,Clone)]
pub struct PtrArg;

impl LintPass for PtrArg {
    fn get_lints(&self) -> LintArray {
        lint_array!(PTR_ARG)
    }
}

impl LateLintPass for PtrArg {
    fn check_item(&mut self, cx: &LateContext, item: &Item) {
        if let &ItemFn(ref decl, _, _, _, _, _) = &item.node {
            check_fn(cx, decl);
        }
    }

    fn check_impl_item(&mut self, cx: &LateContext, item: &ImplItem) {
        if let &MethodImplItem(ref sig, _) = &item.node {
            check_fn(cx, &sig.decl);
        }
    }

    fn check_trait_item(&mut self, cx: &LateContext, item: &TraitItem) {
        if let &MethodTraitItem(ref sig, _) = &item.node {
            check_fn(cx, &sig.decl);
        }
    }
}

fn check_fn(cx: &LateContext, decl: &FnDecl) {
    for arg in &decl.inputs {
        if let Some(pat_ty) = cx.tcx.pat_ty_opt(&arg.pat) {
            if let ty::TyRef(_, ty::TypeAndMut { ty, mutbl: MutImmutable }) = pat_ty.sty {
                if match_type(cx, ty, &VEC_PATH) {
                    span_lint(cx,
                              PTR_ARG,
                              arg.ty.span,
                              "writing `&Vec<_>` instead of `&[_]` involves one more reference \
                               and cannot be used with non-Vec-based slices. Consider changing \
                               the type to `&[...]`");
                } else if match_type(cx, ty, &STRING_PATH) {
                    span_lint(cx,
                              PTR_ARG,
                              arg.ty.span,
                              "writing `&String` instead of `&str` involves a new object where a \
                               slice will do. Consider changing the type to `&str`");
                }
            }
        }
    }
}
