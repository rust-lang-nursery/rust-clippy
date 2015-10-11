use rustc::lint::*;
use rustc_front::hir::*;
use reexport::*;
use syntax::codemap::{ExpnInfo, Span, ExpnFormat};
use rustc::front::map::Node::*;
use rustc::middle::def_id::DefId;
use rustc::middle::ty;
use std::borrow::Cow;
use syntax::ast::Lit_::*;

// module DefPaths for certain structs/enums we check for
pub const OPTION_PATH: [&'static str; 3] = ["core", "option", "Option"];
pub const RESULT_PATH: [&'static str; 3] = ["core", "result", "Result"];
pub const STRING_PATH: [&'static str; 3] = ["collections", "string", "String"];
pub const VEC_PATH:    [&'static str; 3] = ["collections", "vec", "Vec"];
pub const LL_PATH:     [&'static str; 3] = ["collections", "linked_list", "LinkedList"];

/// returns true this expn_info was expanded by any macro
pub fn in_macro(cx: &LateContext, span: Span) -> bool {
    cx.sess().codemap().with_expn_info(span.expn_id,
            |info| info.map_or(false, |_| true))
}

/// returns true if the macro that expanded the crate was outside of
/// the current crate or was a compiler plugin
pub fn in_external_macro<T: LintContext>(cx: &T, span: Span) -> bool {
    /// invokes in_macro with the expansion info of the given span
    /// slightly heavy, try to use this after other checks have already happened
    fn in_macro_ext<T: LintContext>(cx: &T, opt_info: Option<&ExpnInfo>) -> bool {
        // no ExpnInfo = no macro
        opt_info.map_or(false, |info| {
            match info.callee.format {
                ExpnFormat::MacroAttribute(..) => {
                    // these are all plugins
                    return true;
                },
                _ => (),
            }
            // no span for the callee = external macro
            info.callee.span.map_or(true, |span| {
                // no snippet = external macro or compiler-builtin expansion
                cx.sess().codemap().span_to_snippet(span).ok().map_or(true, |code|
                    // macro doesn't start with "macro_rules"
                    // = compiler plugin
                    !code.starts_with("macro_rules")
                )
            })
        })
    }

    cx.sess().codemap().with_expn_info(span.expn_id,
            |info| in_macro_ext(cx, info))
}

/// check if a DefId's path matches the given absolute type path
/// usage e.g. with
/// `match_def_path(cx, id, &["core", "option", "Option"])`
pub fn match_def_path(cx: &LateContext, def_id: DefId, path: &[&str]) -> bool {
    cx.tcx.with_path(def_id, |iter| iter.zip(path)
                                        .all(|(nm, p)| nm.name().as_str() == *p))
}

/// check if type is struct or enum type with given def path
pub fn match_type(cx: &LateContext, ty: ty::Ty, path: &[&str]) -> bool {
    match ty.sty {
        ty::TyEnum(ref adt, _) | ty::TyStruct(ref adt, _) => {
            match_def_path(cx, adt.did, path)
        }
        _ => {
            false
        }
    }
}

/// check if method call given in "expr" belongs to given trait
pub fn match_trait_method(cx: &LateContext, expr: &Expr, path: &[&str]) -> bool {
    let method_call = ty::MethodCall::expr(expr.id);
    let trt_id = cx.tcx.tables
                       .borrow().method_map.get(&method_call)
                       .and_then(|callee| cx.tcx.trait_of_item(callee.def_id));
    if let Some(trt_id) = trt_id {
        match_def_path(cx, trt_id, path)
    } else {
        false
    }
}

/// match a Path against a slice of segment string literals, e.g.
/// `match_path(path, &["std", "rt", "begin_unwind"])`
pub fn match_path(path: &Path, segments: &[&str]) -> bool {
    path.segments.iter().rev().zip(segments.iter().rev()).all(
        |(a, b)| a.identifier.name.as_str() == *b)
}

/// get the name of the item the expression is in, if available
pub fn get_item_name(cx: &LateContext, expr: &Expr) -> Option<Name> {
    let parent_id = cx.tcx.map.get_parent(expr.id);
    match cx.tcx.map.find(parent_id) {
        Some(NodeItem(&Item{ ref name, .. })) |
        Some(NodeTraitItem(&TraitItem{ id: _, ref name, .. })) |
        Some(NodeImplItem(&ImplItem{ id: _, ref name, .. })) => {
            Some(*name)
        },
        _ => None,
    }
}

/// convert a span to a code snippet if available, otherwise use default, e.g.
/// `snippet(cx, expr.span, "..")`
pub fn snippet<'a, T: LintContext>(cx: &T, span: Span, default: &'a str) -> Cow<'a, str> {
    cx.sess().codemap().span_to_snippet(span).map(From::from).unwrap_or(Cow::Borrowed(default))
}

/// convert a span (from a block) to a code snippet if available, otherwise use default, e.g.
/// `snippet(cx, expr.span, "..")`
/// This trims the code of indentation, except for the first line
/// Use it for blocks or block-like things which need to be printed as such
pub fn snippet_block<'a, T: LintContext>(cx: &T, span: Span, default: &'a str) -> Cow<'a, str> {
    let snip = snippet(cx, span, default);
    trim_multiline(snip, true)
}

/// Like snippet_block, but add braces if the expr is not an ExprBlock
/// Also takes an Option<String> which can be put inside the braces
pub fn expr_block<'a, T: LintContext>(cx: &T, expr: &Expr,
                                      option: Option<String>,
                                      default: &'a str) -> Cow<'a, str> {
    let code = snippet_block(cx, expr.span, default);
    let string = option.map_or("".to_owned(), |s| s);
    if let ExprBlock(_) = expr.node {
        Cow::Owned(format!("{}{}", code, string))
    } else if string.is_empty() {
        Cow::Owned(format!("{{ {} }}", code))
    } else {
        Cow::Owned(format!("{{\n{};\n{}\n}}", code, string))
    }
}

/// Trim indentation from a multiline string
/// with possibility of ignoring the first line
pub fn trim_multiline(s: Cow<str>, ignore_first: bool) -> Cow<str> {
    let s_space = trim_multiline_inner(s, ignore_first, ' ');
    let s_tab = trim_multiline_inner(s_space, ignore_first, '\t');
    trim_multiline_inner(s_tab, ignore_first, ' ')
}

fn trim_multiline_inner(s: Cow<str>, ignore_first: bool, ch: char) -> Cow<str> {
    let x = s.lines().skip(ignore_first as usize)
             .filter_map(|l| { if l.len() > 0 { // ignore empty lines
                                Some(l.char_indices()
                                      .find(|&(_,x)| x != ch)
                                      .unwrap_or((l.len(), ch)).0)
                               } else {None}})
             .min().unwrap_or(0);
    if x > 0 {
        Cow::Owned(s.lines().enumerate().map(|(i,l)| if (ignore_first && i == 0) ||
                                                         l.len() == 0 {
                                                        l
                                                     } else {
                                                        l.split_at(x).1
                                                     }).collect::<Vec<_>>()
                                       .join("\n"))
    } else {
        s
    }
}

/// get a parent expr if any – this is useful to constrain a lint
pub fn get_parent_expr<'c>(cx: &'c LateContext, e: &Expr) -> Option<&'c Expr> {
    let map = &cx.tcx.map;
    let node_id : NodeId = e.id;
    let parent_id : NodeId = map.get_parent_node(node_id);
    if node_id == parent_id { return None; }
    map.find(parent_id).and_then(|node|
        if let NodeExpr(parent) = node { Some(parent) } else { None } )
}

#[cfg(not(feature="structured_logging"))]
pub fn span_lint<T: LintContext>(cx: &T, lint: &'static Lint, sp: Span, msg: &str) {
    cx.span_lint(lint, sp, msg);
    if cx.current_level(lint) != Level::Allow {
        cx.sess().fileline_help(sp, &format!("for further information visit \
            https://github.com/Manishearth/rust-clippy/wiki#{}",
            lint.name_lower()))
    }
}

#[cfg(feature="structured_logging")]
pub fn span_lint<T: LintContext>(cx: &T, lint: &'static Lint, sp: Span, msg: &str) {
    // lint.name / lint.desc is can give details of the lint
    // cx.sess().codemap() has all these nice functions for line/column/snippet details
    // http://doc.rust-lang.org/syntax/codemap/struct.CodeMap.html#method.span_to_string
    cx.span_lint(lint, sp, msg);
    if cx.current_level(lint) != Level::Allow {
        cx.sess().fileline_help(sp, &format!("for further information visit \
            https://github.com/Manishearth/rust-clippy/wiki#{}",
            lint.name_lower()))
    }
}

pub fn span_help_and_lint<T: LintContext>(cx: &T, lint: &'static Lint, span: Span,
        msg: &str, help: &str) {
    cx.span_lint(lint, span, msg);
    if cx.current_level(lint) != Level::Allow {
        cx.sess().fileline_help(span, &format!("{}\nfor further information \
            visit https://github.com/Manishearth/rust-clippy/wiki#{}",
            help, lint.name_lower()))
    }
}

pub fn span_note_and_lint<T: LintContext>(cx: &T, lint: &'static Lint, span: Span,
        msg: &str, note_span: Span, note: &str) {
    cx.span_lint(lint, span, msg);
    if cx.current_level(lint) != Level::Allow {
        if note_span == span {
            cx.sess().fileline_note(note_span, note)
        } else {
            cx.sess().span_note(note_span, note)
        }
        cx.sess().fileline_help(span, &format!("for further information visit \
            https://github.com/Manishearth/rust-clippy/wiki#{}",
            lint.name_lower()))
    }
}

/// return the base type for references and raw pointers
pub fn walk_ptrs_ty(ty: ty::Ty) -> ty::Ty {
    match ty.sty {
        ty::TyRef(_, ref tm) | ty::TyRawPtr(ref tm) => walk_ptrs_ty(tm.ty),
        _ => ty
    }
}

/// return the base type for references and raw pointers, and count reference depth
pub fn walk_ptrs_ty_depth(ty: ty::Ty) -> (ty::Ty, usize) {
    fn inner(ty: ty::Ty, depth: usize) -> (ty::Ty, usize) {
        match ty.sty {
            ty::TyRef(_, ref tm) | ty::TyRawPtr(ref tm) => inner(tm.ty, depth + 1),
            _ => (ty, depth)
        }
    }
    inner(ty, 0)
}

pub fn is_integer_literal(expr: &Expr, value: u64) -> bool
{
    // FIXME: use constant folding
    if let ExprLit(ref spanned) = expr.node {
        if let LitInt(v, _) = spanned.node {
            return v == value;
        }
    }
    false
}

/// Produce a nested chain of if-lets and ifs from the patterns:
///
///     if_let_chain! {
///         [
///             Some(y) = x,
///             y.len() == 2,
///             Some(z) = y,
///         ],
///         {
///             block
///         }
///     }
///
/// becomes
///
///     if let Some(y) = x {
///         if y.len() == 2 {
///             if let Some(z) = y {
///                 block
///             }
///         }
///     }
#[macro_export]
macro_rules! if_let_chain {
    ([let $pat:pat = $expr:expr, $($tt:tt)+], $block:block) => {
        if let $pat = $expr {
           if_let_chain!{ [$($tt)+], $block }
        }
    };
    ([let $pat:pat = $expr:expr], $block:block) => {
        if let $pat = $expr {
           $block
        }
    };
    ([$expr:expr, $($tt:tt)+], $block:block) => {
        if $expr {
           if_let_chain!{ [$($tt)+], $block }
        }
    };
    ([$expr:expr], $block:block) => {
        if $expr {
           $block
        }
    };
}
