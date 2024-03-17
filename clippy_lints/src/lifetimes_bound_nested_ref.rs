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
use rustc_hir::{GenericBound, WherePredicate};
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::ty::ty_kind::TyKind;
use rustc_middle::ty::{BoundRegionKind, RegionKind, Ty};
use rustc_session::impl_lint_pass;
use rustc_span::Symbol;

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
struct BoundLftPair {
    long_lft: String,
    outlived_lft: String,
}

impl BoundLftPair {
    fn new(long_lft_sym: &Symbol, outlived_lft_sym: &Symbol) -> Self {
        let res = BoundLftPair {
            long_lft: long_lft_sym.to_ident_string(),
            outlived_lft: outlived_lft_sym.to_ident_string(),
        };
        res
    }

    fn as_bound_declaration(&self) -> String {
        format!("{}: {}", self.long_lft, self.outlived_lft,)
    }
}

impl PartialEq for BoundLftPair {
    fn eq(&self, other: &Self) -> bool {
        self.long_lft.eq(&other.long_lft) && self.outlived_lft.eq(&other.outlived_lft)
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl Eq for BoundLftPair {}

impl PartialOrd for BoundLftPair {
    fn partial_cmp(&self, other: &BoundLftPair) -> Option<Ordering> {
        self.long_lft
            .partial_cmp(&other.long_lft)
            .or(self.outlived_lft.partial_cmp(&other.outlived_lft))
    }
}

impl Ord for BoundLftPair {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.long_lft.cmp(&other.long_lft) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => self.outlived_lft.cmp(&other.outlived_lft),
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
        local_def_id: rustc_span::def_id::LocalDefId,
    ) {
        let FnKind::ItemFn(_ident, generics, _fn_header) = fn_kind else {
            return;
        };
        if generics.predicates.is_empty() && fn_decl.inputs.is_empty() {
            return;
        }
        // collect declared predicate bounds on lifetime pairs
        let mut declared_bounds = BTreeSet::<BoundLftPair>::new();
        for where_predicate in generics.predicates {
            declared_bounds.append(&mut get_declared_bounds(where_predicate));
        }

        let bound_fn_sig = ctx.tcx.fn_sig(local_def_id);
        let fn_sig = bound_fn_sig.skip_binder().skip_binder();

        // collect bounds implied by nested references with lifetimes in input arguments
        let mut implied_bounds = BTreeSet::<BoundLftPair>::new();
        for input_ty in fn_sig.inputs() {
            implied_bounds.append(&mut get_nested_ref_implied_bounds(ctx, *input_ty, None));
        }

        // and for function return type
        let output_ty = fn_sig.output();
        implied_bounds.append(&mut get_nested_ref_implied_bounds(ctx, output_ty, None));

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
}

fn get_declared_bounds(where_predicate: &WherePredicate<'_>) -> BTreeSet<BoundLftPair> {
    let mut declared_bounds = BTreeSet::new();
    match where_predicate {
        WherePredicate::BoundPredicate(_) | WherePredicate::EqPredicate(_) => {},
        WherePredicate::RegionPredicate(where_region_predicate) => {
            for generic_bound in where_region_predicate.bounds {
                let GenericBound::Outlives(outlived_lifetime) = generic_bound else {
                    continue;
                };
                let declared_bound_lifetime_pair = BoundLftPair::new(
                    &where_region_predicate.lifetime.ident.name,
                    &outlived_lifetime.ident.name,
                );
                declared_bounds.insert(declared_bound_lifetime_pair);
            }
        },
    }
    declared_bounds
}

#[allow(rustc::usage_of_ty_tykind)]
fn get_nested_ref_implied_bounds<'tcx2, 'a>(
    ctx: &LateContext<'tcx2>,
    ty: Ty<'a>,
    outlived_lifetime_opt: Option<Symbol>,
) -> BTreeSet<BoundLftPair> {
    let mut implied_bounds = BTreeSet::new();
    // scan ty for a reference with a declared lifetime.
    // use the variants with GenericArgs and/or subtypes.
    match *ty.kind() {
        TyKind::Ref(region, referred_to_ty, _mutability) => {
            let mut ref_lifetime_opt: Option<Symbol> = None;
            match region.kind() {
                RegionKind::ReBound(_debruijn_index, bound_region) => {
                    if let BoundRegionKind::BrNamed(_def_id, ref_lifetime) = bound_region.kind {
                        ref_lifetime_opt = Some(ref_lifetime);
                    } else {
                        dbg!(bound_region.kind);
                    }
                },
                RegionKind::ReEarlyParam(early_param_region) => {
                    if early_param_region.has_name() {
                        let ref_lifetime = early_param_region.name;
                        ref_lifetime_opt = Some(ref_lifetime);
                    } else {
                        dbg!("early_param_region without name");
                    }
                },
                _ => {
                    dbg!(region.kind());
                },
            }
            if let Some(ref_lifetime) = ref_lifetime_opt {
                if let Some(outlived_lifetime) = outlived_lifetime_opt {
                    let bound_lifetime_pair = BoundLftPair::new(&ref_lifetime, &outlived_lifetime);
                    implied_bounds.insert(bound_lifetime_pair);
                }
                implied_bounds.append(&mut get_nested_ref_implied_bounds(
                    ctx,
                    referred_to_ty,
                    Some(ref_lifetime),
                ));
            }
        },
        TyKind::Tuple(tuple_part_tys) => {
            dbg!("tuple");
            for tuple_part_ty in tuple_part_tys {
                dbg!(tuple_part_ty);
                implied_bounds.append(&mut get_nested_ref_implied_bounds(
                    ctx,
                    tuple_part_ty,
                    outlived_lifetime_opt,
                ));
            }
        },
        _ => {
            // dbg!("unmatched", ty.kind());
        },
    }
    implied_bounds
}
