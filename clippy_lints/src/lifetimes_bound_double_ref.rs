use clippy_utils::diagnostics::span_lint;
use rustc_hir::intravisit::FnKind;
use rustc_hir::{GenericBound, LifetimeName, Ty, TyKind, WherePredicate};
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::impl_lint_pass;
use rustc_span::Span;

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

#[derive(Debug, PartialEq)]
struct BoundLifetimePair {
    long_lifetime_name: LifetimeName,
    outlived_lifetime_name: LifetimeName,
}
impl LateLintPass<'_> for LifetimesBoundDoubleRef {
    fn check_fn<'tcx>(
        &mut self,
        ctx: &LateContext<'_>,
        fn_kind: rustc_hir::intravisit::FnKind<'tcx>,
        fn_decl: &'tcx rustc_hir::FnDecl<'tcx>,
        _body: &'tcx rustc_hir::Body<'tcx>,
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
        let mut declared_bounds = Vec::<BoundLifetimePair>::new();
        for where_predicate in generics.predicates {
            collect_declared_bounds(*where_predicate, &mut declared_bounds)
        }
        // collect bounds implied by double references with lifetimes in arguments
        let mut implied_bounds = Vec::<BoundLifetimePair>::new();
        for input_ty in fn_decl.inputs {
            collect_double_ref_implied_bounds(input_ty, &mut implied_bounds);
        }
        // and for function return type
        if let rustc_hir::FnRetTy::Return(ret_ty) = fn_decl.output {
            collect_double_ref_implied_bounds(ret_ty, &mut implied_bounds);
        }

        for implied_bound in implied_bounds {
            if !declared_bounds.contains(&implied_bound) {
                dbg!(&implied_bound);
                // get the span of the function declaration without the body.
                let sp = Span::default();
                let msg = "missing lifetime bound declation";
                span_lint(ctx, ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG, sp, msg);
            }
        }
    }
}

fn collect_declared_bounds(where_predicate: WherePredicate<'_>, declared_bounds: &mut Vec<BoundLifetimePair>) {
    match where_predicate {
        WherePredicate::BoundPredicate(_) | WherePredicate::EqPredicate(_) => {
            return;
        },
        WherePredicate::RegionPredicate(where_region_predicate) => {
            for generic_bound in where_region_predicate.bounds {
                let GenericBound::Outlives(outlived_lifetime) = generic_bound else {
                    continue;
                };
                let declared_bound_lifetime_pair = BoundLifetimePair {
                    long_lifetime_name: where_region_predicate.lifetime.res,
                    outlived_lifetime_name: outlived_lifetime.res,
                };
                declared_bounds.push(declared_bound_lifetime_pair);
            }
        },
    }
}

fn collect_double_ref_implied_bounds(ty: &Ty<'_>, implied_bounds: &mut Vec<BoundLifetimePair>) {
    // collect only from types with a top level reference
    let TyKind::Ref(mut lifetime, mut mut_ty) = ty.kind else {
        return;
    };
    while let TyKind::Ref(nested_lifetime, nested_mut_ty) = mut_ty.ty.kind {
        let implied_bound_lifetime_pair = BoundLifetimePair {
            long_lifetime_name: nested_lifetime.res,
            outlived_lifetime_name: lifetime.res,
        };
        implied_bounds.push(implied_bound_lifetime_pair);

        mut_ty = nested_mut_ty;
        lifetime = nested_lifetime;
    }
}
