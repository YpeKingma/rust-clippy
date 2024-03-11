/// Lints to help dealing with unsoundness due to a compiler bug as described here:
/// https://github.com/rust-lang/rustc-dev-guide/blob/478a77a902f64e5128e7164e4e8a3980cfe4b133/src/traits/implied-bounds.md .
///
/// For the following three cases the current compiler (1.76.0) gives a later error message when
/// manually adding generic lifetime bound that is implied by a nested reference:
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
/// after the above compiler bugs have been fixed.
///
/// All lints here are in the nursery category.
use clippy_utils::diagnostics::span_lint;
use rustc_hir::intravisit::FnKind;
use rustc_hir::{GenericBound, Lifetime, Ty, TyKind, WherePredicate};
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::impl_lint_pass;

declare_clippy_lint! {
    /// ### What it does
    /// Checks function arguments with a nested reference type with lifetimes,
    /// and suggests to add a generic bound on these lifetimes.
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
    pub ADD_REDUNDANT_LIFETIMES_BOUND_NESTED_REF_ARG,
    nursery,
    "suggest to add generic lifetime bounds for nested reference function arguments"
}

declare_clippy_lint! {
    /// ### What it does
    /// Checks function arguments with a nested reference type with lifetimes,
    /// and suggests to remove declared generic lifetime bounds implied
    /// by these argument lifetimes.
    /// This should only be done after the current rustc compiler version 1.76.0
    /// has been fixed to deal correctly with implied lifetime bounds.
    ///
    /// ### Why is this bad?
    /// Such generic lifetime bounds are superfluous.
    ///
    /// ### Known problems
    /// The suggested removals of generic lifetime bounds
    /// should only be done after the compiler is fixed.
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
    pub REMOVE_REDUNDANT_LIFETIMES_BOUND_NESTED_REF_ARG,
    nursery,
    "suggest to remove generic lifetime bounds implied by nested reference function arguments"
}

pub struct LifetimesBoundNestedRef;

impl_lint_pass!(LifetimesBoundNestedRef => [
    ADD_REDUNDANT_LIFETIMES_BOUND_NESTED_REF_ARG,
    REMOVE_REDUNDANT_LIFETIMES_BOUND_NESTED_REF_ARG,
]);

#[derive(Debug)]
struct BoundLifetimePair<'a> {
    long_lifetime: &'a Lifetime,
    outlived_lifetime: &'a Lifetime,
}

impl<'a> PartialEq for BoundLifetimePair<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.long_lifetime.res.eq(&other.long_lifetime.res)
            && self.outlived_lifetime.res.eq(&other.outlived_lifetime.res)
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl<'a> BoundLifetimePair<'a> {
    fn as_bound_declaration(&'a self) -> String {
        format!(
            "{}: {}",
            self.long_lifetime.ident.name, self.outlived_lifetime.ident.name,
        )
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
        let mut declared_bounds = Vec::<BoundLifetimePair<'_>>::new();
        for where_predicate in generics.predicates {
            declared_bounds.extend(get_declared_bounds(*where_predicate));
        }
        // collect bounds implied by nested references with lifetimes in arguments
        let mut implied_bounds = Vec::<BoundLifetimePair<'_>>::new();
        for input_ty in fn_decl.inputs {
            implied_bounds.extend(get_nested_ref_implied_bounds(input_ty));
        }
        // and for function return type
        if let rustc_hir::FnRetTy::Return(ret_ty) = fn_decl.output {
            implied_bounds.extend(get_nested_ref_implied_bounds(ret_ty));
        }

        let implied_bounds = implied_bounds;

        for implied_bound in &implied_bounds {
            if !declared_bounds.contains(implied_bound) {
                span_lint(
                    ctx,
                    ADD_REDUNDANT_LIFETIMES_BOUND_NESTED_REF_ARG,
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
                    REMOVE_REDUNDANT_LIFETIMES_BOUND_NESTED_REF_ARG,
                    generics.span,
                    &format!(
                        "declared lifetime bound is implied: {}",
                        declared_bound.as_bound_declaration()
                    ),
                );
            }
        }
    }
}

fn get_declared_bounds<'a>(where_predicate: WherePredicate<'a>) -> Vec<BoundLifetimePair<'a>> {
    let mut declared_bounds = Vec::new();
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
                declared_bounds.push(declared_bound_lifetime_pair);
            }
        },
    }
    declared_bounds
}

fn get_nested_ref_implied_bounds<'a>(ty: &Ty<'a>) -> Vec<BoundLifetimePair<'a>> {
    let mut implied_bounds = Vec::new();
    // collect only from top level reference
    let TyKind::Ref(mut lifetime, mut mut_ty) = ty.kind else {
        return implied_bounds;
    };
    while let TyKind::Ref(nested_lifetime, nested_mut_ty) = mut_ty.ty.kind {
        let implied_bound_lifetime_pair = BoundLifetimePair {
            long_lifetime: nested_lifetime,
            outlived_lifetime: lifetime,
        };
        implied_bounds.push(implied_bound_lifetime_pair);

        mut_ty = nested_mut_ty;
        lifetime = nested_lifetime;
    }
    implied_bounds
}
