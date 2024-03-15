/// Lints to help dealing with unsoundness due to a compiler bug described here:
///
/// https://github.com/rust-lang/rustc-dev-guide/blob/478a77a902f64e5128e7164e4e8a3980cfe4b133/src/traits/implied-bounds.md .
///
/// For the following three cases the current compiler (1.76.0) gives a later error message when
/// manually adding a generic lifetime bound that is implied by a nested reference:
///
///     https://github.com/rust-lang/rust/issues/25860
///     Implied bounds on nested references + variance = soundness hole
///     https://github.com/rust-lang/rust/issues/25860#issue-82044592
///     
///     https://github.com/rust-lang/rust/issues/84591
///     HRTB on subtrait unsoundly provides HTRB on supertrait with weaker implied bounds
///     
///     https://github.com/rust-lang/rust/issues/100051
///     implied bounds from projections in impl header can be unsound
///     
/// The lints here suggest to manually add such lifetime bounds in the hope that
/// the unsoundness is avoided.
///
/// There are also reverse lints that suggest to remove lifetime bounds
/// that are implied by nested references. These lints are intended to be used only
/// after the compiler handles these lifetime bounds correctly.
///
/// All lints here are in the nursery category.
use std::cmp::Ordering;
use std::collections::BTreeSet;

use clippy_utils::diagnostics::span_lint;
use rustc_hir::intravisit::FnKind;
use rustc_hir::{GenericBound, Lifetime, Ty as HirTy, TyKind as HirTyKind, WherePredicate};
use rustc_hir_analysis::hir_ty_to_ty;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::ty::ty_kind::TyKind as MiddleTyKind;
use rustc_middle::ty::Ty as MiddleTy;
use rustc_session::impl_lint_pass;

declare_clippy_lint! {
    /// ### What it does
    /// Checks function arguments and return values that have a nested reference type with lifetimes,
    /// and suggests to add the implied generic lifetime bounds.
    /// Adding a lifetimes bound helps to avoid unsound code because this addition
    /// can lead to a compiler error in related source code, as observed in rustc 1.76.0.
    ///
    /// ### Why is this bad?
    /// This is described in: https://github.com/rust-lang/rust/issues/25860
    /// and as one case of unsoundness here:
    /// https://github.com/rust-lang/rustc-dev-guide/blob/478a77a902f64e5128e7164e4e8a3980cfe4b133/src/traits/implied-bounds.md .
    ///
    /// ### Known problems
    /// It is not known whether this covers all cases in issue 25860.
    ///
    /// ### Example, the val_a argument implies a lifetimes bound:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b, T>(val_a: &'a &'b (), val_b: &'b T) -> &'a T {...}
    /// ```
    /// Use instead:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b: 'a, T>(val_a: &'a &'b (), val_b: &'b T) -> &'a T {...}
    /// ```
    #[clippy::version = "1.78.0"]
    pub IMPLICIT_LIFETIMES_BOUND_NESTED_REF,
    nursery,
    "suggest to add generic lifetime bounds implied by nested references in function arguments and return value"
}

declare_clippy_lint! {
    /// ### What it does
    /// Checks function arguments and return values that have a nested reference type with lifetimes,
    /// and suggests to remove generic lifetime bounds that are implied.
    ///
    /// ### Why is this bad?
    /// Such generic lifetime bounds are redundant.
    ///
    /// ### Known problems
    /// Removing redundant lifetime bounds
    /// should only be done after the compiler
    /// has been fixed to deal correctly with implied lifetime bounds.
    ///
    /// ### Example, the val_a argument implies a lifetimes bound:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b: 'a, T>(val_a: &'a &'b (), val_b: &'b T) -> &'a T {...}
    /// ```
    /// Use instead:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b, T>(val_a: &'a &'b (), val_b: &'b T) -> &'a T {...}
    /// ```

    #[clippy::version = "1.78.0"]
    pub EXPLICIT_LIFETIMES_BOUND_NESTED_REF,
    nursery,
    "suggest to remove generic lifetime bounds implied by nested references in function arguments and return value"
}

pub struct LifetimesBoundNestedRef;

impl_lint_pass!(LifetimesBoundNestedRef => [
    IMPLICIT_LIFETIMES_BOUND_NESTED_REF,
    EXPLICIT_LIFETIMES_BOUND_NESTED_REF,
]);

#[derive(Debug)]
struct BoundLifetimePair<'a> {
    long_lifetime: &'a Lifetime,
    outlived_lifetime: &'a Lifetime,
}

impl<'a> BoundLifetimePair<'a> {
    fn as_bound_declaration(&'a self) -> String {
        format!(
            "{}: {}",
            self.long_lifetime.ident.name, self.outlived_lifetime.ident.name,
        )
    }
}

impl<'a> PartialEq for BoundLifetimePair<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.long_lifetime.ident.name.eq(&other.long_lifetime.ident.name)
            && self
                .outlived_lifetime
                .ident
                .name
                .eq(&other.outlived_lifetime.ident.name)
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl<'a> Eq for BoundLifetimePair<'a> {}

impl<'a> PartialOrd for BoundLifetimePair<'a> {
    fn partial_cmp(&self, other: &BoundLifetimePair<'a>) -> Option<Ordering> {
        self.long_lifetime
            .ident
            .name
            .partial_cmp(&other.long_lifetime.ident.name)
            .or(self
                .outlived_lifetime
                .ident
                .name
                .partial_cmp(&other.outlived_lifetime.ident.name))
    }
}

impl<'a> Ord for BoundLifetimePair<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.long_lifetime.ident.name.cmp(&other.long_lifetime.ident.name) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => self
                .outlived_lifetime
                .ident
                .name
                .cmp(&other.outlived_lifetime.ident.name),
        }
    }
}

impl<'tcx> LateLintPass<'tcx> for LifetimesBoundNestedRef {
    fn check_fn<'tcx2>(
        &mut self,
        ctx: &LateContext<'tcx2>,
        fn_kind: rustc_hir::intravisit::FnKind<'tcx2>,
        fn_decl: &'tcx2 rustc_hir::FnDecl<'tcx2>,
        _body: &'tcx2 rustc_hir::Body<'tcx2>,
        _span: rustc_span::Span,
        _local_def_id: rustc_span::def_id::LocalDefId,
    ) {
        let FnKind::ItemFn(_ident, generics, _fn_header) = fn_kind else {
            return;
        };
        if generics.predicates.is_empty() && fn_decl.inputs.is_empty() {
            return;
        }
        // collect declared predicate bounds on lifetime pairs
        let mut declared_bounds = BTreeSet::<BoundLifetimePair<'_>>::new();
        for where_predicate in generics.predicates {
            declared_bounds.append(&mut get_declared_bounds(where_predicate));
        }
        // collect bounds implied by nested references with lifetimes in arguments
        let mut implied_bounds = BTreeSet::<BoundLifetimePair<'_>>::new();
        for input_ty in fn_decl.inputs {
            // implied_bounds.append(&mut get_nested_ref_implied_bounds_hir(input_ty));
            implied_bounds.append(&mut get_nested_ref_implied_bounds_middle(&hir_ty_to_ty(
                ctx.tcx, input_ty,
            )));
        }
        // and for function return type
        if let rustc_hir::FnRetTy::Return(ret_ty) = fn_decl.output {
            // implied_bounds.append(&mut get_nested_ref_implied_bounds_hir(ret_ty));
            implied_bounds.append(&mut get_nested_ref_implied_bounds_middle(&hir_ty_to_ty(
                ctx.tcx, ret_ty,
            )));
        }

        // let fn_sig = ctx.tcx.fn_sig(local_def_id);
        // let inputs = fn_sig.skip_binder().inputs();
        // for input_ty in inputs.iter() {
        //     let input_ty = input_ty.skip_binder();
        //     implied_bounds.append(&mut get_nested_ref_implied_bounds_middle(input_ty.skip_binder()));
        // }
        // let output = fn_sig.skip_binder().output();
        // implied_bounds.append(&mut get_nested_ref_implied_bounds_middle(&output.skip_binder()));

        // dbg!(generics.params);
        // dbg!(fn_decl.output);

        let implied_bounds = implied_bounds;

        for implied_bound in &implied_bounds {
            if !declared_bounds.contains(implied_bound) {
                span_lint(
                    ctx,
                    IMPLICIT_LIFETIMES_BOUND_NESTED_REF,
                    generics.span,
                    &format!(
                        "missing lifetime bound declation: {}",
                        implied_bound.as_bound_declaration()
                    ),
                );
            }
        }

        for declared_bound in &declared_bounds {
            if implied_bounds.contains(declared_bound) {
                span_lint(
                    ctx,
                    EXPLICIT_LIFETIMES_BOUND_NESTED_REF,
                    generics.span,
                    &format!(
                        "declared lifetime bound is implied: {}",
                        declared_bound.as_bound_declaration()
                    ),
                );
            }
        }
    }

    // For issue 100051:
    // fn check_item_post<'tcx2>(&mut self, _ctx: &LateContext<'tcx2>, item: &'tcx2 Item<'tcx2>) {
    //     let ItemKind::Impl(impl_item) = item.kind else {
    //         return;
    //     };
    //     if !impl_item.generics.params.iter().any(|p| {
    //         if let GenericParamKind::Lifetime { .. } = p.kind {
    //             dbg!(p.kind);
    //             true
    //         } else {
    //             false
    //         }
    //     }) {
    //         return;
    //     }
    //     dbg!("impl_item with generic lifetime parameter", impl_item);
    // }
}

fn get_declared_bounds<'a>(where_predicate: &WherePredicate<'a>) -> BTreeSet<BoundLifetimePair<'a>> {
    let mut declared_bounds = BTreeSet::new();
    match where_predicate {
        WherePredicate::BoundPredicate(_) | WherePredicate::EqPredicate(_) => {},
        WherePredicate::RegionPredicate(where_region_predicate) => {
            for generic_bound in where_region_predicate.bounds {
                let GenericBound::Outlives(outlived_lifetime) = generic_bound else {
                    continue;
                };
                let declared_bound_lifetime_pair = BoundLifetimePair {
                    long_lifetime: where_region_predicate.lifetime,
                    outlived_lifetime: outlived_lifetime,
                };
                declared_bounds.insert(declared_bound_lifetime_pair);
            }
        },
    }
    declared_bounds
}

fn get_nested_ref_implied_bounds_hir<'a>(ty: &HirTy<'a>) -> BTreeSet<BoundLifetimePair<'a>> {
    let mut implied_bounds = BTreeSet::new();
    // collect only from top level reference
    let HirTyKind::Ref(mut lifetime, mut mut_ty) = ty.kind else {
        return implied_bounds;
    };
    while let HirTyKind::Ref(nested_lifetime, nested_mut_ty) = mut_ty.ty.kind {
        let implied_bound_lifetime_pair = BoundLifetimePair {
            long_lifetime: nested_lifetime,
            outlived_lifetime: lifetime,
        };
        implied_bounds.insert(implied_bound_lifetime_pair);

        mut_ty = nested_mut_ty;
        lifetime = nested_lifetime;
    }
    implied_bounds
}

#[allow(rustc::usage_of_ty_tykind)]
fn get_nested_ref_implied_bounds_middle<'a>(ty: &MiddleTy<'a>) -> BTreeSet<BoundLifetimePair<'a>> {
    let mut implied_bounds = BTreeSet::new();
    // scan ty for a reference with a declared lifetime.
    // use the variants with GenericArgs and/or subtypes.
    match *ty.kind() {
        MiddleTyKind::Adt(_adt_def, _generic_args) => {},
        MiddleTyKind::Bound(_debruijn_index, _bound_ty) => {},
        MiddleTyKind::Ref(_region, _ty, _mutability) => {
            // TODO: the reference may be outlived and/or outliving.
        },
        MiddleTyKind::FnDef(_def_id, _generic_args) => {},
        MiddleTyKind::Closure(_def_id, _generic_args) => {},
        MiddleTyKind::CoroutineClosure(_def_id, _generic_args) => {},
        MiddleTyKind::Coroutine(_def_id, _generic_args) => {},
        MiddleTyKind::CoroutineWitness(_def_id, _generic_args) => {},
        MiddleTyKind::Param(_param_ty) => {},
        MiddleTyKind::Tuple(_tys) => {
            // TODO: the subtypes may contain outliving references
        },
        _ => {},
    }
    implied_bounds
}
