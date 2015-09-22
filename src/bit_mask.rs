use rustc::lint::*;
use rustc::middle::const_eval::lookup_const_by_id;
use rustc::middle::def::*;
use rustc_front::hir::*;
use rustc_front::util::is_comparison_binop;
use syntax::codemap::Span;
use syntax::ast::Lit_::*;

use utils::span_lint;

declare_lint! {
    pub BAD_BIT_MASK,
    Warn,
    "expressions of the form `_ & mask == select` that will only ever return `true` or `false` \
     (because in the example `select` containing bits that `mask` doesn't have)"
}

declare_lint! {
    pub INEFFECTIVE_BIT_MASK,
    Warn,
    "expressions where a bit mask will be rendered useless by a comparison, e.g. `(x | 1) > 2`"
}

/// Checks for incompatible bit masks in comparisons, e.g. `x & 1 == 2`.
/// This cannot work because the bit that makes up the value two was
/// zeroed out by the bit-and with 1. So the formula for detecting if an
/// expression of the type  `_ <bit_op> m <cmp_op> c` (where `<bit_op>`
/// is one of {`&`, '|'} and `<cmp_op>` is one of {`!=`, `>=`, `>` ,
/// `!=`, `>=`, `>`}) can be determined from the following table:
///
/// |Comparison  |Bit-Op|Example     |is always|Formula               |
/// |------------|------|------------|---------|----------------------|
/// |`==` or `!=`| `&`  |`x & 2 == 3`|`false`  |`c & m != c`          |
/// |`<`  or `>=`| `&`  |`x & 2 < 3` |`true`   |`m < c`               |
/// |`>`  or `<=`| `&`  |`x & 1 > 1` |`false`  |`m <= c`              |
/// |`==` or `!=`| `|`  |`x | 1 == 0`|`false`  |`c | m != c`          |
/// |`<`  or `>=`| `|`  |`x | 1 < 1` |`false`  |`m >= c`              |
/// |`<=` or `>` | `|`  |`x | 1 > 0` |`true`   |`m > c`               |
///
/// This lint is **deny** by default
///
/// There is also a lint that warns on ineffective masks that is *warn*
/// by default.
///
/// |Comparison|Bit-Op   |Example    |equals |Formula|
/// |`>` / `<=`|`|` / `^`|`x | 2 > 3`|`x > 3`|`¹ && m <= c`|
/// |`<` / `>=`|`|` / `^`|`x ^ 1 < 4`|`x < 4`|`¹ && m < c` |
///
/// `¹ power_of_two(c + 1)`
#[derive(Copy,Clone)]
pub struct BitMask;

impl LintPass for BitMask {
    fn get_lints(&self) -> LintArray {
        lint_array!(BAD_BIT_MASK, INEFFECTIVE_BIT_MASK)
    }
}

impl LateLintPass for BitMask {
    fn check_expr(&mut self, cx: &LateContext, e: &Expr) {
        if let ExprBinary(ref cmp, ref left, ref right) = e.node {
            if is_comparison_binop(cmp.node) {
                fetch_int_literal(cx, right)
                    .map_or_else(|| {
                                     fetch_int_literal(cx, left)
                                         .map_or((),
                                                 |cmp_val| {
                                                     check_compare(cx,
                                                                   right,
                                                                   invert_cmp(cmp.node),
                                                                   cmp_val,
                                                                   &e.span)
                                                 })
                                 },
                                 |cmp_opt| check_compare(cx, left, cmp.node, cmp_opt, &e.span))
            }
        }
    }
}

fn invert_cmp(cmp: BinOp_) -> BinOp_ {
    match cmp {
        BiEq => BiEq,
        BiNe => BiNe,
        BiLt => BiGt,
        BiGt => BiLt,
        BiLe => BiGe,
        BiGe => BiLe,
        _ => BiOr, // dummy
    }
}


fn check_compare(cx: &LateContext, bit_op: &Expr, cmp_op: BinOp_, cmp_value: u64, span: &Span) {
    if let ExprBinary(ref op, ref left, ref right) = bit_op.node {
        if op.node != BiBitAnd && op.node != BiBitOr {
            return;
        }
        fetch_int_literal(cx, right)
            .or_else(|| fetch_int_literal(cx, left))
            .map_or((), |mask| check_bit_mask(cx, op.node, cmp_op, mask, cmp_value, span))
    }
}

fn check_bit_mask(cx: &LateContext,
                  bit_op: BinOp_,
                  cmp_op: BinOp_,
                  mask_value: u64,
                  cmp_value: u64,
                  span: &Span) {
    match cmp_op {
        BiEq | BiNe => match bit_op {
            BiBitAnd => if mask_value & cmp_value != cmp_value {
                if cmp_value != 0 {
                    span_lint(cx,
                              BAD_BIT_MASK,
                              *span,
                              &format!(
                        "incompatible bit mask: `_ & {}` can never be equal to `{}`",
                        mask_value, cmp_value));
                }
            } else {
                if mask_value == 0 {
                    span_lint(cx, BAD_BIT_MASK, *span, "&-masking with zero");
                }
            },
            BiBitOr => if mask_value | cmp_value != cmp_value {
                span_lint(cx,
                          BAD_BIT_MASK,
                          *span,
                          &format!(
                    "incompatible bit mask: `_ | {}` can never be equal to `{}`",
                    mask_value, cmp_value));
            },
            _ => (),
        },
        BiLt | BiGe => match bit_op {
            BiBitAnd => if mask_value < cmp_value {
                span_lint(cx,
                          BAD_BIT_MASK,
                          *span,
                          &format!(
                    "incompatible bit mask: `_ & {}` will always be lower than `{}`",
                    mask_value, cmp_value));
            } else {
                if mask_value == 0 {
                    span_lint(cx, BAD_BIT_MASK, *span, "&-masking with zero");
                }
            },
            BiBitOr => if mask_value >= cmp_value {
                span_lint(cx,
                          BAD_BIT_MASK,
                          *span,
                          &format!(
                    "incompatible bit mask: `_ | {}` will never be lower than `{}`",
                    mask_value, cmp_value));
            } else {
                check_ineffective_lt(cx, *span, mask_value, cmp_value, "|");
            },
            BiBitXor => check_ineffective_lt(cx, *span, mask_value, cmp_value, "^"),
            _ => (),
        },
        BiLe | BiGt => match bit_op {
            BiBitAnd => if mask_value <= cmp_value {
                span_lint(cx,
                          BAD_BIT_MASK,
                          *span,
                          &format!(
                    "incompatible bit mask: `_ & {}` will never be higher than `{}`",
                    mask_value, cmp_value));
            } else {
                if mask_value == 0 {
                    span_lint(cx, BAD_BIT_MASK, *span, "&-masking with zero");
                }
            },
            BiBitOr => if mask_value > cmp_value {
                span_lint(cx,
                          BAD_BIT_MASK,
                          *span,
                          &format!(
                    "incompatible bit mask: `_ | {}` will always be higher than `{}`",
                    mask_value, cmp_value));
            } else {
                check_ineffective_gt(cx, *span, mask_value, cmp_value, "|");
            },
            BiBitXor => check_ineffective_gt(cx, *span, mask_value, cmp_value, "^"),
            _ => (),
        },
        _ => (),
    }
}

fn check_ineffective_lt(cx: &LateContext, span: Span, m: u64, c: u64, op: &str) {
    if c.is_power_of_two() && m < c {
        span_lint(cx, INEFFECTIVE_BIT_MASK, span, &format!(
            "ineffective bit mask: `x {} {}` compared to `{}`, is the same as x compared directly",
            op, m, c));
    }
}

fn check_ineffective_gt(cx: &LateContext, span: Span, m: u64, c: u64, op: &str) {
    if (c + 1).is_power_of_two() && m <= c {
        span_lint(cx, INEFFECTIVE_BIT_MASK, span, &format!(
            "ineffective bit mask: `x {} {}` compared to `{}`, is the same as x compared directly",
            op, m, c));
    }
}

fn fetch_int_literal(cx: &LateContext, lit: &Expr) -> Option<u64> {
    match lit.node {
        ExprLit(ref lit_ptr) => {
            if let &LitInt(value, _) = &lit_ptr.node {
                Option::Some(value) //TODO: Handle sign
            } else {
                Option::None
            }
        }
        ExprPath(_, _) => {
            // Important to let the borrow expire before the const lookup to avoid double
            // borrowing.
            let def_map = cx.tcx.def_map.borrow();
            match def_map.get(&lit.id) {
                Some(&PathResolution { base_def: DefConst(def_id), ..}) => Some(def_id),
                _ => None,
            }
        }
                              .and_then(|def_id| lookup_const_by_id(cx.tcx, def_id, Option::None))
                              .and_then(|l| fetch_int_literal(cx, l)),
        _ => Option::None,
    }
}
