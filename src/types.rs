use rustc::lint::*;
use rustc_front::hir::*;
use reexport::*;
use rustc_front::util::{is_comparison_binop, binop_to_string};
use syntax::codemap::Span;
use rustc_front::intravisit::{FnKind, Visitor, walk_ty};
use rustc::middle::ty;
use syntax::ast::IntTy::*;
use syntax::ast::UintTy::*;
use syntax::ast::FloatTy::*;

use utils::{match_type, snippet, span_lint, span_help_and_lint};
use utils::{is_from_for_desugar, in_macro, in_external_macro};
use utils::{LL_PATH, VEC_PATH};

/// Handles all the linting of funky types
#[allow(missing_copy_implementations)]
pub struct TypePass;

/// **What it does:** This lint checks for use of `Box<Vec<_>>` anywhere in the code.
///
/// **Why is this bad?** `Vec` already keeps its contents in a separate area on the heap. So if you `Box` it, you just add another level of indirection without any benefit whatsoever.
///
/// **Known problems:** None
///
/// **Example:** `struct X { values: Box<Vec<Foo>> }`
declare_lint!(pub BOX_VEC, Warn,
              "usage of `Box<Vec<T>>`, vector elements are already on the heap");
/// **What it does:** This lint checks for usage of any `LinkedList`, suggesting to use a `Vec` or a `VecDeque` (formerly called `RingBuf`).
///
/// **Why is this bad?** Gankro says:
///
/// >The TL;DR of `LinkedList` is that it's built on a massive amount of pointers and indirection. It wastes memory, it has terrible cache locality, and is all-around slow. `RingBuf`, while "only" amortized for push/pop, should be faster in the general case for almost every possible workload, and isn't even amortized at all if you can predict the capacity you need.
/// >
/// > `LinkedList`s are only really good if you're doing a lot of merging or splitting of lists. This is because they can just mangle some pointers instead of actually copying the data. Even if you're doing a lot of insertion in the middle of the list, `RingBuf` can still be better because of how expensive it is to seek to the middle of a `LinkedList`.
///
/// **Known problems:** False positives – the instances where using a `LinkedList` makes sense are few and far between, but they can still happen.
///
/// **Example:** `let x = LinkedList::new();`
declare_lint!(pub LINKEDLIST, Warn,
              "usage of LinkedList, usually a vector is faster, or a more specialized data \
               structure like a VecDeque");

impl LintPass for TypePass {
    fn get_lints(&self) -> LintArray {
        lint_array!(BOX_VEC, LINKEDLIST)
    }
}

impl LateLintPass for TypePass {
    fn check_ty(&mut self, cx: &LateContext, ast_ty: &Ty) {
        if let Some(ty) = cx.tcx.ast_ty_to_ty_cache.borrow().get(&ast_ty.id) {
            if let ty::TyBox(ref inner) = ty.sty {
                if match_type(cx, inner, &VEC_PATH) {
                    span_help_and_lint(cx,
                                       BOX_VEC,
                                       ast_ty.span,
                                       "you seem to be trying to use `Box<Vec<T>>`. Consider \
                                        using just `Vec<T>`",
                                       "`Vec<T>` is already on the heap, `Box<Vec<T>>` makes an \
                                        extra allocation.");
                }
            } else if match_type(cx, ty, &LL_PATH) {
                span_help_and_lint(cx,
                                   LINKEDLIST,
                                   ast_ty.span,
                                   "I see you're using a LinkedList! Perhaps you meant some \
                                    other data structure?",
                                   "a VecDeque might work");
            }
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct LetPass;

/// **What it does:** This lint checks for binding a unit value. It is `Warn` by default.
///
/// **Why is this bad?** A unit value cannot usefully be used anywhere. So binding one is kind of pointless.
///
/// **Known problems:** None
///
/// **Example:** `let x = { 1; };`
declare_lint!(pub LET_UNIT_VALUE, Warn,
              "creating a let binding to a value of unit type, which usually can't be used afterwards");

fn check_let_unit(cx: &LateContext, decl: &Decl) {
    if let DeclLocal(ref local) = decl.node {
        let bindtype = &cx.tcx.pat_ty(&local.pat).sty;
        if *bindtype == ty::TyTuple(vec![]) {
            if in_external_macro(cx, decl.span) || in_macro(cx, local.pat.span) {
                return;
            }
            if is_from_for_desugar(decl) {
                return;
            }
            span_lint(cx,
                      LET_UNIT_VALUE,
                      decl.span,
                      &format!("this let-binding has unit value. Consider omitting `let {} =`",
                               snippet(cx, local.pat.span, "..")));
        }
    }
}

impl LintPass for LetPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(LET_UNIT_VALUE)
    }
}

impl LateLintPass for LetPass {
    fn check_decl(&mut self, cx: &LateContext, decl: &Decl) {
        check_let_unit(cx, decl)
    }
}

/// **What it does:** This lint checks for comparisons to unit. It is `Warn` by default.
///
/// **Why is this bad?** Unit is always equal to itself, and thus is just a clumsily written constant. Mostly this happens when someone accidentally adds semicolons at the end of the operands.
///
/// **Known problems:** None
///
/// **Example:** `if { foo(); } == { bar(); } { baz(); }` is equal to `{ foo(); bar(); baz(); }`
declare_lint!(pub UNIT_CMP, Warn,
              "comparing unit values (which is always `true` or `false`, respectively)");

#[allow(missing_copy_implementations)]
pub struct UnitCmp;

impl LintPass for UnitCmp {
    fn get_lints(&self) -> LintArray {
        lint_array!(UNIT_CMP)
    }
}

impl LateLintPass for UnitCmp {
    fn check_expr(&mut self, cx: &LateContext, expr: &Expr) {
        if in_macro(cx, expr.span) {
            return;
        }
        if let ExprBinary(ref cmp, ref left, _) = expr.node {
            let op = cmp.node;
            let sty = &cx.tcx.expr_ty(left).sty;
            if *sty == ty::TyTuple(vec![]) && is_comparison_binop(op) {
                let result = match op {
                    BiEq | BiLe | BiGe => "true",
                    _ => "false",
                };
                span_lint(cx,
                          UNIT_CMP,
                          expr.span,
                          &format!("{}-comparison of unit values detected. This will always be \
                                    {}",
                                   binop_to_string(op),
                                   result));
            }
        }
    }
}

pub struct CastPass;

/// **What it does:** This lint checks for casts from any numerical to a float type where the receiving type cannot store all values from the original type without rounding errors. This possible rounding is to be expected, so this lint is `Allow` by default.
///
/// Basically, this warns on casting any integer with 32 or more bits to `f32` or any 64-bit integer to `f64`.
///
/// **Why is this bad?** It's not bad at all. But in some applications it can be helpful to know where precision loss can take place. This lint can help find those places in the code.
///
/// **Known problems:** None
///
/// **Example:** `let x = u64::MAX; x as f64`
declare_lint!(pub CAST_PRECISION_LOSS, Allow,
              "casts that cause loss of precision, e.g `x as f32` where `x: u64`");
/// **What it does:** This lint checks for casts from a signed to an unsigned numerical type. In this case, negative values wrap around to large positive values, which can be quite surprising in practice. However, as the cast works as defined, this lint is `Allow` by default.
///
/// **Why is this bad?** Possibly surprising results. You can activate this lint as a one-time check to see where numerical wrapping can arise.
///
/// **Known problems:** None
///
/// **Example:** `let y : i8 = -1; y as u64` will return 18446744073709551615
declare_lint!(pub CAST_SIGN_LOSS, Allow,
              "casts from signed types to unsigned types, e.g `x as u32` where `x: i32`");
/// **What it does:** This lint checks for on casts between numerical types that may truncate large values. This is expected behavior, so the cast is `Allow` by default.
///
/// **Why is this bad?** In some problem domains, it is good practice to avoid truncation. This lint can be activated to help assess where additional checks could be beneficial.
///
/// **Known problems:** None
///
/// **Example:** `fn as_u8(x: u64) -> u8 { x as u8 }`
declare_lint!(pub CAST_POSSIBLE_TRUNCATION, Allow,
              "casts that may cause truncation of the value, e.g `x as u8` where `x: u32`, or `x as i32` where `x: f32`");
/// **What it does:** This lint checks for casts from an unsigned type to a signed type of the same size. Performing such a cast is a 'no-op' for the compiler, i.e. nothing is changed at the bit level, and the binary representation of the value is reinterpreted. This can cause wrapping if the value is too big for the target signed type. However, the cast works as defined, so this lint is `Allow` by default.
///
/// **Why is this bad?** While such a cast is not bad in itself, the results can be surprising when this is not the intended behavior, as demonstrated by the example below.
///
/// **Known problems:** None
///
/// **Example:** `u32::MAX as i32` will yield a value of `-1`.
declare_lint!(pub CAST_POSSIBLE_WRAP, Allow,
              "casts that may cause wrapping around the value, e.g `x as i32` where `x: u32` and `x > i32::MAX`");

/// Returns the size in bits of an integral type.
/// Will return 0 if the type is not an int or uint variant
fn int_ty_to_nbits(typ: &ty::TyS) -> usize {
    let n = match typ.sty {
        ty::TyInt(i) => 4 << (i as usize),
        ty::TyUint(u) => 4 << (u as usize),
        _ => 0,
    };
    // n == 4 is the usize/isize case
    if n == 4 {
        ::std::usize::BITS
    } else {
        n
    }
}

fn is_isize_or_usize(typ: &ty::TyS) -> bool {
    match typ.sty {
        ty::TyInt(TyIs) | ty::TyUint(TyUs) => true,
        _ => false,
    }
}

fn span_precision_loss_lint(cx: &LateContext,
                            expr: &Expr,
                            cast_from: &ty::TyS,
                            cast_to_f64: bool) {
    let mantissa_nbits = if cast_to_f64 {
        52
    } else {
        23
    };
    let arch_dependent = is_isize_or_usize(cast_from) && cast_to_f64;
    let arch_dependent_str = "on targets with 64-bit wide pointers ";
    let from_nbits_str = if arch_dependent {
        "64".to_owned()
    } else if is_isize_or_usize(cast_from) {
        "32 or 64".to_owned()
    } else {
        int_ty_to_nbits(cast_from).to_string()
    };
    span_lint(cx,
              CAST_PRECISION_LOSS,
              expr.span,
              &format!("casting {0} to {1} causes a loss of precision {2}({0} is {3} bits wide, \
                        but {1}'s mantissa is only {4} bits wide)",
                       cast_from,
                       if cast_to_f64 {
                           "f64"
                       } else {
                           "f32"
                       },
                       if arch_dependent {
                           arch_dependent_str
                       } else {
                           ""
                       },
                       from_nbits_str,
                       mantissa_nbits));
}

enum ArchSuffix {
    _32,
    _64,
    None,
}

fn check_truncation_and_wrapping(cx: &LateContext,
                                 expr: &Expr,
                                 cast_from: &ty::TyS,
                                 cast_to: &ty::TyS) {
    let arch_64_suffix = " on targets with 64-bit wide pointers";
    let arch_32_suffix = " on targets with 32-bit wide pointers";
    let cast_unsigned_to_signed = !cast_from.is_signed() && cast_to.is_signed();
    let (from_nbits, to_nbits) = (int_ty_to_nbits(cast_from), int_ty_to_nbits(cast_to));
    let (span_truncation, suffix_truncation, span_wrap, suffix_wrap) =
        match (is_isize_or_usize(cast_from), is_isize_or_usize(cast_to)) {
            (true, true) | (false, false) => {
                (to_nbits < from_nbits,
                 ArchSuffix::None,
                 to_nbits == from_nbits && cast_unsigned_to_signed,
                 ArchSuffix::None)
            }
            (true, false) => {
                (to_nbits <= 32,
                 if to_nbits == 32 {
                    ArchSuffix::_64
                } else {
                    ArchSuffix::None
                },
                 to_nbits <= 32 && cast_unsigned_to_signed,
                 ArchSuffix::_32)
            }
            (false, true) => {
                (from_nbits == 64,
                 ArchSuffix::_32,
                 cast_unsigned_to_signed,
                 if from_nbits == 64 {
                    ArchSuffix::_64
                } else {
                    ArchSuffix::_32
                })
            }
        };
    if span_truncation {
        span_lint(cx,
                  CAST_POSSIBLE_TRUNCATION,
                  expr.span,
                  &format!("casting {} to {} may truncate the value{}",
                           cast_from,
                           cast_to,
                           match suffix_truncation {
                               ArchSuffix::_32 => arch_32_suffix,
                               ArchSuffix::_64 => arch_64_suffix,
                               ArchSuffix::None => "",
                           }));
    }
    if span_wrap {
        span_lint(cx,
                  CAST_POSSIBLE_WRAP,
                  expr.span,
                  &format!("casting {} to {} may wrap around the value{}",
                           cast_from,
                           cast_to,
                           match suffix_wrap {
                               ArchSuffix::_32 => arch_32_suffix,
                               ArchSuffix::_64 => arch_64_suffix,
                               ArchSuffix::None => "",
                           }));
    }
}

impl LintPass for CastPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(CAST_PRECISION_LOSS,
                    CAST_SIGN_LOSS,
                    CAST_POSSIBLE_TRUNCATION,
                    CAST_POSSIBLE_WRAP)
    }
}

impl LateLintPass for CastPass {
    fn check_expr(&mut self, cx: &LateContext, expr: &Expr) {
        if let ExprCast(ref ex, _) = expr.node {
            let (cast_from, cast_to) = (cx.tcx.expr_ty(ex), cx.tcx.expr_ty(expr));
            if cast_from.is_numeric() && cast_to.is_numeric() && !in_external_macro(cx, expr.span) {
                match (cast_from.is_integral(), cast_to.is_integral()) {
                    (true, false) => {
                        let from_nbits = int_ty_to_nbits(cast_from);
                        let to_nbits = if let ty::TyFloat(TyF32) = cast_to.sty {
                            32
                        } else {
                            64
                        };
                        if is_isize_or_usize(cast_from) || from_nbits >= to_nbits {
                            span_precision_loss_lint(cx, expr, cast_from, to_nbits == 64);
                        }
                    }
                    (false, true) => {
                        span_lint(cx,
                                  CAST_POSSIBLE_TRUNCATION,
                                  expr.span,
                                  &format!("casting {} to {} may truncate the value",
                                           cast_from,
                                           cast_to));
                        if !cast_to.is_signed() {
                            span_lint(cx,
                                      CAST_SIGN_LOSS,
                                      expr.span,
                                      &format!("casting {} to {} may lose the sign of the value",
                                               cast_from,
                                               cast_to));
                        }
                    }
                    (true, true) => {
                        if cast_from.is_signed() && !cast_to.is_signed() {
                            span_lint(cx,
                                      CAST_SIGN_LOSS,
                                      expr.span,
                                      &format!("casting {} to {} may lose the sign of the value",
                                               cast_from,
                                               cast_to));
                        }
                        check_truncation_and_wrapping(cx, expr, cast_from, cast_to);
                    }
                    (false, false) => {
                        if let (&ty::TyFloat(TyF64), &ty::TyFloat(TyF32)) = (&cast_from.sty,
                                                                             &cast_to.sty) {
                            span_lint(cx,
                                      CAST_POSSIBLE_TRUNCATION,
                                      expr.span,
                                      "casting f64 to f32 may truncate the value");
                        }
                    }
                }
            }
        }
    }
}

/// **What it does:** This lint checks for types used in structs, parameters and `let` declarations above a certain complexity threshold. It is `Warn` by default.
///
/// **Why is this bad?** Too complex types make the code less readable. Consider using a `type` definition to simplify them.
///
/// **Known problems:** None
///
/// **Example:** `struct Foo { inner: Rc<Vec<Vec<Box<(u32, u32, u32, u32)>>>> }`
declare_lint!(pub TYPE_COMPLEXITY, Warn,
              "usage of very complex types; recommends factoring out parts into `type` definitions");

#[allow(missing_copy_implementations)]
pub struct TypeComplexityPass;

impl LintPass for TypeComplexityPass {
    fn get_lints(&self) -> LintArray {
        lint_array!(TYPE_COMPLEXITY)
    }
}

impl LateLintPass for TypeComplexityPass {
    fn check_fn(&mut self,
                cx: &LateContext,
                _: FnKind,
                decl: &FnDecl,
                _: &Block,
                _: Span,
                _: NodeId) {
        check_fndecl(cx, decl);
    }

    fn check_struct_field(&mut self, cx: &LateContext, field: &StructField) {
        // enum variants are also struct fields now
        check_type(cx, &field.node.ty);
    }

    fn check_item(&mut self, cx: &LateContext, item: &Item) {
        match item.node {
            ItemStatic(ref ty, _, _) |
            ItemConst(ref ty, _) => check_type(cx, ty),
            // functions, enums, structs, impls and traits are covered
            _ => (),
        }
    }

    fn check_trait_item(&mut self, cx: &LateContext, item: &TraitItem) {
        match item.node {
            ConstTraitItem(ref ty, _) |
            TypeTraitItem(_, Some(ref ty)) => check_type(cx, ty),
            MethodTraitItem(MethodSig { ref decl, .. }, None) => check_fndecl(cx, decl),
            // methods with default impl are covered by check_fn
            _ => (),
        }
    }

    fn check_impl_item(&mut self, cx: &LateContext, item: &ImplItem) {
        match item.node {
            ImplItemKind::Const(ref ty, _) |
            ImplItemKind::Type(ref ty) => check_type(cx, ty),
            // methods are covered by check_fn
            _ => (),
        }
    }

    fn check_local(&mut self, cx: &LateContext, local: &Local) {
        if let Some(ref ty) = local.ty {
            check_type(cx, ty);
        }
    }
}

fn check_fndecl(cx: &LateContext, decl: &FnDecl) {
    for arg in &decl.inputs {
        check_type(cx, &arg.ty);
    }
    if let Return(ref ty) = decl.output {
        check_type(cx, ty);
    }
}

fn check_type(cx: &LateContext, ty: &Ty) {
    if in_macro(cx, ty.span) {
        return;
    }
    let score = {
        let mut visitor = TypeComplexityVisitor {
            score: 0,
            nest: 1,
        };
        visitor.visit_ty(ty);
        visitor.score
    };
    // println!("{:?} --> {}", ty, score);
    if score > 250 {
        span_lint(cx,
                  TYPE_COMPLEXITY,
                  ty.span,
                  &format!("very complex type used. Consider factoring parts into `type` \
                            definitions"));
    }
}

/// Walks a type and assigns a complexity score to it.
struct TypeComplexityVisitor {
    /// total complexity score of the type
    score: u32,
    /// current nesting level
    nest: u32,
}

impl<'v> Visitor<'v> for TypeComplexityVisitor {
    fn visit_ty(&mut self, ty: &'v Ty) {
        let (add_score, sub_nest) = match ty.node {
            // _, &x and *x have only small overhead; don't mess with nesting level
            TyInfer |
            TyPtr(..) |
            TyRptr(..) => (1, 0),

            // the "normal" components of a type: named types, arrays/tuples
            TyPath(..) |
            TyVec(..) |
            TyTup(..) |
            TyFixedLengthVec(..) => (10 * self.nest, 1),

            // "Sum" of trait bounds
            TyObjectSum(..) => (20 * self.nest, 0),

            // function types and "for<...>" bring a lot of overhead
            TyBareFn(..) |
            TyPolyTraitRef(..) => (50 * self.nest, 1),

            _ => (0, 0),
        };
        self.score += add_score;
        self.nest += sub_nest;
        walk_ty(self, ty);
        self.nest -= sub_nest;
    }
}
