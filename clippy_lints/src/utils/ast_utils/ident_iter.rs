use core::iter::{self, FusedIterator};
use rustc_ast::{
    AttrKind,
    Attribute,
    Expr,
    ExprKind,
    FnDecl,
    FnRetTy,
    GenericBound,
    GenericParam,
    GenericParamKind,
    Param,
    Pat,
    PatKind,
    Path,
    PolyTraitRef,
    MacCall,
    MutTy,
    Ty,
    TyKind,
};
use rustc_ast::ptr::P;
use rustc_span::symbol::Ident;

pub type IdentIter<'a> = Box<dyn Iterator<Item = Ident> + 'a>;

pub fn from_expr<'expr>(expr: &'expr Expr) -> IdentIter<'expr> {
    Box::new(ExprIdentIter::new(expr))
}

pub fn from_ty<'ty>(ty: &'ty Ty) -> IdentIter<'ty> {
    Box::new(TyIdentIter::new(ty))
}

struct ExprIdentIter<'expr> {
    expr: &'expr Expr,
    inner: Option<IdentIter<'expr>>,
    done: bool,
}

impl <'expr> ExprIdentIter<'expr> {
    fn new(expr: &'expr Expr) -> Self {
        Self {
            expr,
            inner: None,
            done: false,
        }
    }

    /// This is a convenience method to help with type inference.
    fn new_p(expr: &'expr P<Expr>) -> Self {
        Self::new(expr)
    }
}

impl <'expr> Iterator for ExprIdentIter<'expr> {
    type Item = Ident;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let inner_opt = &mut self.inner;

        if let Some(mut inner) = inner_opt.take() {
            let output = inner.next();

            if output.is_some() {
                *inner_opt = Some(inner);
                return output;
            }
        }

        macro_rules! set_and_call_next {
            ($iter: expr) => {{
                let mut p_iter = $iter;

                let next_item = p_iter.next();

                *inner_opt = Some(Box::new(p_iter));

                next_item
            }}
        }

        let output = match self.expr.kind {
            ExprKind::Lit(_)|ExprKind::Err => None,
            ExprKind::Path(_, ref path)
            | ExprKind::MacCall(MacCall{ ref path, ..}) => {
                set_and_call_next!(
                    path_iter(path)
                )
            },
            ExprKind::Box(ref expr)
            | ExprKind::Unary(_, ref expr) => {
                set_and_call_next!(
                    ExprIdentIter::new(expr)
                )
            },
            ExprKind::Array(ref exprs)|ExprKind::Tup(ref exprs) => {
                set_and_call_next!(
                    exprs.iter()
                        .flat_map(ExprIdentIter::new_p)
                )
            },
            ExprKind::Call(ref func, ref args) => {
                set_and_call_next!(
                    ExprIdentIter::new(func)
                        .chain(
                            args.iter()
                                .flat_map(ExprIdentIter::new_p)
                        )
                )
            },
            ExprKind::MethodCall(ref method_name, ref args, _) => {
                set_and_call_next!(
                    iter::once(method_name.ident)
                        .chain(
                            args.iter()
                                .flat_map(ExprIdentIter::new_p)
                        )
                )
            },
            ExprKind::Binary(_, ref left, ref right) => {
                set_and_call_next!(
                    ExprIdentIter::new(left)
                        .chain(
                            ExprIdentIter::new(right)
                        )
                )
            },
            ExprKind::Cast(ref expr, ref ty)
            | ExprKind::Type(ref expr, ref ty) => {
                set_and_call_next!(
                    ExprIdentIter::new(expr)
                        .chain(
                            TyIdentIter::new(ty)
                        )
                )
            },
            _ => todo!(),
        };

        if output.is_none() {
            self.done = true;
        }

        output
    }
}

impl <'expr> FusedIterator for ExprIdentIter<'expr> {}

struct TyIdentIter<'ty> {
    ty: &'ty Ty,
    inner: Option<IdentIter<'ty>>,
    done: bool,
}

impl <'ty> TyIdentIter<'ty> {
    fn new(ty: &'ty Ty) -> Self {
        Self {
            ty,
            inner: None,
            done: false,
        }
    }

    /// This is a convenience method to help with type inference.
    fn new_p(ty: &'ty P<Ty>) -> Self {
        Self::new(ty)
    }
}

impl <'ty> Iterator for TyIdentIter<'ty> {
    type Item = Ident;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let inner_opt = &mut self.inner;

        if let Some(mut inner) = inner_opt.take() {
            let output = inner.next();

            if output.is_some() {
                *inner_opt = Some(inner);
                return output;
            }
        }

        macro_rules! set_and_call_next {
            ($iter: expr) => {{
                let mut p_iter = $iter;

                let next_item = p_iter.next();

                *inner_opt = Some(Box::new(p_iter));

                next_item
            }}
        }

        let output = match self.ty.kind {
            TyKind::Never
            | TyKind::Infer
            | TyKind::Err
            | TyKind::CVarArgs
            | TyKind::ImplicitSelf => None,
            TyKind::Rptr(Some(ref lifetime), MutTy{ ref ty, .. }) => {
                set_and_call_next!(
                    iter::once(lifetime.ident)
                        .chain(
                            TyIdentIter::new(ty)
                        )
                )
            },
            TyKind::Slice(ref ty)
            | TyKind::Ptr(MutTy{ ref ty, .. })
            | TyKind::Rptr(None, MutTy{ ref ty, .. })
            | TyKind::Paren(ref ty) => {
                set_and_call_next!(
                    TyIdentIter::new(ty)
                )
            },
            TyKind::Array(ref ty, ref anon_const) => {
                set_and_call_next!(
                    TyIdentIter::new(ty)
                        .chain(ExprIdentIter::new(&anon_const.value))
                )
            },
            TyKind::Tup(ref ty_vec) => {
                set_and_call_next!(
                    ty_vec.iter()
                        .flat_map(TyIdentIter::new_p)
                )
            },
            TyKind::Typeof(ref anon_const) => {
                set_and_call_next!(
                    ExprIdentIter::new(&anon_const.value)
                )
            },
            TyKind::Path(_, ref path)
            | TyKind::MacCall(MacCall{ ref path, ..}) => {
                set_and_call_next!(
                    path_iter(path)
                )
            },
            TyKind::TraitObject(ref bounds, _)
            | TyKind::ImplTrait(_, ref bounds) => {
                set_and_call_next!(
                    bounds.iter()
                        .flat_map(GenericBoundIdentIter::new)
                )
            },
            TyKind::BareFn(ref bare_fn_ty) => {
                set_and_call_next!(
                    bare_fn_ty.generic_params.iter()
                        .flat_map(generic_param_iter)
                        .chain(
                            fn_decl_iter(&bare_fn_ty.decl)
                        )
                )
            },
        };

        if output.is_none() {
            self.done = true;
        }

        output
    }
}

impl <'ty> FusedIterator for TyIdentIter<'ty> {}

struct PatIdentIter<'pat> {
    pat: &'pat Pat,
    inner: Option<IdentIter<'pat>>,
    done: bool,
}

impl <'pat> PatIdentIter<'pat> {
    fn new(pat: &'pat Pat) -> Self {
        Self {
            pat,
            inner: None,
            done: false,
        }
    }
}

impl <'pat> Iterator for PatIdentIter<'pat> {
    type Item = Ident;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let inner_opt = &mut self.inner;

        if let Some(mut inner) = inner_opt.take() {
            let output = inner.next();

            if output.is_some() {
                *inner_opt = Some(inner);
                return output;
            }
        }

        macro_rules! set_and_call_next {
            ($iter: expr) => {{
                let mut p_iter = $iter;

                let next_item = p_iter.next();

                *inner_opt = Some(Box::new(p_iter));

                next_item
            }}
        }

        let output = match self.pat.kind {
            PatKind::Wild 
            | PatKind::Rest => None,
            PatKind::Ident(_, ident, None) => {
                self.done = true;
                Some(ident)
            }
            PatKind::Ident(_, ident, Some(ref pat)) => {
                set_and_call_next!(
                    iter::once(ident)
                        .chain(PatIdentIter::new(pat))
                )
            },
            _ => todo!(),
        };

        if output.is_none() {
            self.done = true;
        }

        output
    }
}

impl <'pat> FusedIterator for PatIdentIter<'pat> {}

struct GenericBoundIdentIter<'bound> {
    bound: &'bound GenericBound,
    inner: Option<IdentIter<'bound>>,
    done: bool,
}

impl <'bound> GenericBoundIdentIter<'bound> {
    fn new(bound: &'bound GenericBound) -> Self {
        Self {
            bound,
            inner: None,
            done: false,
        }
    }
}

impl <'bound> Iterator for GenericBoundIdentIter<'bound> {
    type Item = Ident;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let inner_opt = &mut self.inner;

        if let Some(mut inner) = inner_opt.take() {
            let output = inner.next();

            if output.is_some() {
                *inner_opt = Some(inner);
                return output;
            }
        }

        macro_rules! set_and_call_next {
            ($iter: expr) => {{
                let mut p_iter = $iter;

                let next_item = p_iter.next();

                *inner_opt = Some(Box::new(p_iter));

                next_item
            }}
        }

        let output = match self.bound {
            GenericBound::Outlives(ref lifetime) => {
                set_and_call_next!(
                    iter::once(lifetime.ident)
                )
            },
            GenericBound::Trait(
                PolyTraitRef{
                    ref bound_generic_params,
                    ref trait_ref,
                    span: _,
                },
                _
            ) => {
                set_and_call_next!(
                    bound_generic_params.iter()
                        .flat_map(generic_param_iter)
                        .chain(
                            path_iter(&trait_ref.path)
                        )
                )
            },
        };

        if output.is_none() {
            self.done = true;
        }

        output
    }
}

impl <'bound> FusedIterator for GenericBoundIdentIter<'bound> {}

fn generic_param_iter(param: &GenericParam) -> IdentIter<'_> {
    Box::new(
        param.attrs
            .iter()
            .flat_map(attribute_iter)
            .chain(iter::once(param.ident))
            .chain({
                let i_i: IdentIter<'_> = match param.kind {
                    GenericParamKind::Lifetime
                    | GenericParamKind::Type { default: None } => {
                        Box::new(iter::empty())
                    },
                    GenericParamKind::Type { default: Some(ref ty), }
                    | GenericParamKind::Const { ref ty, .. } => {
                        Box::new(TyIdentIter::new(ty))
                    },
                };

                i_i
            })
            .chain(
                param.bounds.iter()
                    .flat_map(GenericBoundIdentIter::new)
            )
    )
}

fn attribute_iter(attribute: &Attribute) -> IdentIter<'_> {
    match attribute.kind {
        AttrKind::Normal(ref attr_item) => Box::new(path_iter(&attr_item.path)),
        AttrKind::DocComment(_, _) => Box::new(iter::empty()),
    }
}

fn path_iter(path: &Path) -> impl Iterator<Item = Ident> + '_ {
    path.segments.iter()
        .map(|s| s.ident)
}

fn fn_decl_iter(fn_decl: &FnDecl) -> impl Iterator<Item = Ident> + '_ {
    fn_decl.inputs
        .iter()
        .flat_map(param_iter)
        .chain({
            let i_i: IdentIter<'_> = match fn_decl.output {
                FnRetTy::Default(_) => {
                    Box::new(iter::empty())
                },
                FnRetTy::Ty(ref ty) => {
                    Box::new(TyIdentIter::new(ty))
                }
            };

            i_i
        })
}

fn param_iter(param: &Param) -> impl Iterator<Item = Ident> + '_ {
    param.attrs.iter()
        .flat_map(attribute_iter)
        .chain(
            TyIdentIter::new(&param.ty)
        )
        .chain(
            PatIdentIter::new(&param.pat)
        )
}
