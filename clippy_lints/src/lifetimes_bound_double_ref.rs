use clippy_utils::diagnostics::span_lint;
use rustc_hir::intravisit::FnKind;
use rustc_hir::{GenericBound, Lifetime, Ty, TyKind, WherePredicate};
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::impl_lint_pass;

declare_clippy_lint! {
    /// ### What it does
    /// Checks function arguments with a double reference type with lifetimes,
    /// and suggests to add a bound on these lifetimes.
    /// Adding a lifetimes bound helps to avoid unsound code because this addition
    /// can lead to a compiler error in related source code, as observed in rustc 1.76.0,
    /// thereby avoiding the unsoundness.
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
    pub ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG,
    nursery,
    "suggest to add lifetime bounds to double reference function arguments"
}

#[derive(Default)]
pub struct LifetimesBoundDoubleRef {}

impl_lint_pass!(LifetimesBoundDoubleRef => [ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG]);

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
    fn as_declared_bound(&'a self) -> String {
        let long_lft_name = self.long_lifetime.ident.name;
        let outlived_lft_name = self.outlived_lifetime.ident.name;
        format!("{long_lft_name}: {outlived_lft_name}")
    }
}

impl<'tcx> LateLintPass<'tcx> for LifetimesBoundDoubleRef {
    fn check_fn<'tcx2>(
        &mut self,
        ctx: &LateContext<'_>,
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
            declared_bounds.extend(collect_declared_bounds(*where_predicate));
        }
        // collect bounds implied by double references with lifetimes in arguments
        let mut implied_bounds = Vec::<BoundLifetimePair<'_>>::new();
        for input_ty in fn_decl.inputs {
            implied_bounds.extend(collect_double_ref_implied_bounds(input_ty));
        }
        // and for function return type
        if let rustc_hir::FnRetTy::Return(ret_ty) = fn_decl.output {
            implied_bounds.extend(collect_double_ref_implied_bounds(ret_ty));
        }

        let declared_bounds = declared_bounds;
        let implied_bounds = implied_bounds;

        for implied_bound in implied_bounds {
            if !declared_bounds.contains(&implied_bound) {
                let msg = format!(
                    "missing lifetime bound declation: {}",
                    implied_bound.as_declared_bound()
                );
                span_lint(ctx, ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG, generics.span, &msg);
            }
        }
    }
}

fn collect_declared_bounds<'a>(where_predicate: WherePredicate<'a>) -> Vec<BoundLifetimePair<'a>> {
    let mut declared_bounds = Vec::<BoundLifetimePair<'_>>::new();
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

fn collect_double_ref_implied_bounds<'a>(ty: &Ty<'a>) -> Vec<BoundLifetimePair<'a>> {
    let mut implied_bounds = Vec::new();
    // collect only from types with a top level reference
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
