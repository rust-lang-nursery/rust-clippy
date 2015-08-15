use syntax::ptr::P;
use syntax::ast;
use syntax::ast::*;
use rustc::middle::ty;
use rustc::lint::{Context, LintPass, LintArray, Lint, Level};
use syntax::codemap::{ExpnInfo, Span};

use utils::{in_macro, snippet, span_lint, span_help_and_lint};

/// Handles all the linting of funky types
#[allow(missing_copy_implementations)]
pub struct TypePass;

declare_lint!(pub BOX_VEC, Warn,
              "usage of `Box<Vec<T>>`, vector elements are already on the heap");
declare_lint!(pub LINKEDLIST, Warn,
              "usage of LinkedList, usually a vector is faster, or a more specialized data \
               structure like a RingBuf");

/// Matches a type with a provided string, and returns its type parameters if successful
pub fn match_ty_unwrap<'a>(ty: &'a Ty, segments: &[&str]) -> Option<&'a [P<Ty>]> {
    if let TyPath(_, Path {segments: ref seg, ..}) = ty.node {
        // So ast::Path isn't the full path, just the tokens that were provided.
        // I could muck around with the maps and find the full path
        // however the more efficient way is to simply reverse the iterators and zip them
        // which will compare them in reverse until one of them runs out of segments
        if seg.iter().rev().zip(segments.iter().rev()).all(|(a,b)| a.identifier.name == b) {
            if let Some(&PathSegment {parameters: AngleBracketedParameters(ref a), ..}) = seg[..].last() {
                Some(&a.types[..])
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}

impl LintPass for TypePass {
    fn get_lints(&self) -> LintArray {
        lint_array!(BOX_VEC, LINKEDLIST)
    }

    fn check_ty(&mut self, cx: &Context, ty: &ast::Ty) {
        {
            // In case stuff gets moved around
            use std::boxed::Box;
            use std::vec::Vec;
        }
        match_ty_unwrap(ty, &["std", "boxed", "Box"]).and_then(|t| t.first())
          .and_then(|t| match_ty_unwrap(&**t, &["std", "vec", "Vec"]))
          .map(|_| {
            span_help_and_lint(cx, BOX_VEC, ty.span,
                              "you seem to be trying to use `Box<Vec<T>>`. Did you mean to use `Vec<T>`?",
                              "`Vec<T>` is already on the heap, `Box<Vec<T>>` makes an extra allocation");
          });
        {
            // In case stuff gets moved around
            use collections::linked_list::LinkedList as DL1;
            use std::collections::linked_list::LinkedList as DL2;
            use std::collections::linked_list::LinkedList as DL3;
        }
        let dlists = [vec!["std","collections","linked_list","LinkedList"],
                      vec!["std","collections","linked_list","LinkedList"],
                      vec!["collections","linked_list","LinkedList"]];
        for path in &dlists {
            if match_ty_unwrap(ty, &path[..]).is_some() {
                span_help_and_lint(cx, LINKEDLIST, ty.span,
                                   "I see you're using a LinkedList! Perhaps you meant some other data structure?",
                                   "a RingBuf might work");
                return;
            }
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct LetPass;

declare_lint!(pub LET_UNIT_VALUE, Warn,
              "creating a let binding to a value of unit type, which usually can't be used afterwards");


fn check_let_unit(cx: &Context, decl: &Decl, info: Option<&ExpnInfo>) {
    if in_macro(cx, info) { return; }
    if let DeclLocal(ref local) = decl.node {
        let bindtype = &cx.tcx.pat_ty(&*local.pat).sty;
        if *bindtype == ty::TyTuple(vec![]) {
            span_lint(cx, LET_UNIT_VALUE, decl.span, &format!(
                "this let-binding has unit value. Consider omitting `let {} =`",
                snippet(cx, local.pat.span, "..")));
        }
    }
}

impl LintPass for LetPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(LET_UNIT_VALUE)
    }

    fn check_decl(&mut self, cx: &Context, decl: &Decl) {
        cx.sess().codemap().with_expn_info(
            decl.span.expn_id,
            |info| check_let_unit(cx, decl, info));
    }
}
