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
use rustc_hir::{GenericBound, Ty as HirTy, TyKind as HirTyKind, WherePredicate};
use rustc_hir_analysis::hir_ty_to_ty;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::ty::ty_kind::TyKind as MiddleTyKind;
use rustc_middle::ty::{BoundRegionKind, RegionKind, Ty};
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
struct BoundLifetimePair {
    long_lifetime_name: String,
    outlived_lifetime_name: String,
}

impl BoundLifetimePair {
    fn as_bound_declaration(&self) -> String {
        format!("{}: {}", self.long_lifetime_name, self.outlived_lifetime_name,)
    }
}

impl PartialEq for BoundLifetimePair {
    fn eq(&self, other: &Self) -> bool {
        self.long_lifetime_name.eq(&other.long_lifetime_name)
            && self.outlived_lifetime_name.eq(&other.outlived_lifetime_name)
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl Eq for BoundLifetimePair {}

impl PartialOrd for BoundLifetimePair {
    fn partial_cmp(&self, other: &BoundLifetimePair) -> Option<Ordering> {
        self.long_lifetime_name
            .partial_cmp(&other.long_lifetime_name)
            .or(self.outlived_lifetime_name.partial_cmp(&other.outlived_lifetime_name))
    }
}

impl Ord for BoundLifetimePair {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.long_lifetime_name.cmp(&other.long_lifetime_name) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => self.outlived_lifetime_name.cmp(&other.outlived_lifetime_name),
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
        let mut declared_bounds = BTreeSet::<BoundLifetimePair>::new();
        for where_predicate in generics.predicates {
            declared_bounds.append(&mut get_declared_bounds(where_predicate));
        }
        // collect bounds implied by nested references with lifetimes in arguments
        let mut implied_bounds = BTreeSet::<BoundLifetimePair>::new();
        for input_ty in fn_decl.inputs {
            eprintln!("input");
            implied_bounds.append(&mut get_nested_ref_implied_bounds_hir(input_ty));
            implied_bounds.append(&mut get_nested_ref_implied_bounds(
                hir_ty_to_ty(ctx.tcx, input_ty),
                None,
            ));
        }
        // and for function return type
        eprintln!("output");
        if let rustc_hir::FnRetTy::Return(ret_ty) = fn_decl.output {
            implied_bounds.append(&mut get_nested_ref_implied_bounds_hir(ret_ty));
            implied_bounds.append(&mut get_nested_ref_implied_bounds(hir_ty_to_ty(ctx.tcx, ret_ty), None));
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

fn get_declared_bounds(where_predicate: &WherePredicate<'_>) -> BTreeSet<BoundLifetimePair> {
    let mut declared_bounds = BTreeSet::new();
    match where_predicate {
        WherePredicate::BoundPredicate(_) | WherePredicate::EqPredicate(_) => {},
        WherePredicate::RegionPredicate(where_region_predicate) => {
            for generic_bound in where_region_predicate.bounds {
                let GenericBound::Outlives(outlived_lifetime) = generic_bound else {
                    continue;
                };
                let declared_bound_lifetime_pair = BoundLifetimePair {
                    long_lifetime_name: where_region_predicate.lifetime.ident.name.to_ident_string(),
                    outlived_lifetime_name: outlived_lifetime.ident.name.to_ident_string(),
                };
                declared_bounds.insert(declared_bound_lifetime_pair);
            }
        },
    }
    declared_bounds
}

fn get_nested_ref_implied_bounds_hir<'a>(ty: &HirTy<'a>) -> BTreeSet<BoundLifetimePair> {
    let mut implied_bounds = BTreeSet::new();
    // collect only from top level reference
    let HirTyKind::Ref(mut lifetime, mut mut_ty) = ty.kind else {
        return implied_bounds;
    };
    while let HirTyKind::Ref(nested_lifetime, nested_mut_ty) = mut_ty.ty.kind {
        let implied_bound_lifetime_pair = BoundLifetimePair {
            long_lifetime_name: nested_lifetime.ident.name.to_ident_string(),
            outlived_lifetime_name: lifetime.ident.name.to_ident_string(),
        };
        implied_bounds.insert(implied_bound_lifetime_pair);

        mut_ty = nested_mut_ty;
        lifetime = nested_lifetime;
    }
    implied_bounds
}

#[allow(rustc::usage_of_ty_tykind)]
fn get_nested_ref_implied_bounds<'a>(
    ty: Ty<'a>,
    shorter_lifetime_name_opt: Option<String>,
) -> BTreeSet<BoundLifetimePair> {
    let mut implied_bounds = BTreeSet::new();
    // scan ty for a reference with a declared lifetime.
    // use the variants with GenericArgs and/or subtypes.
    match *ty.kind() {
        MiddleTyKind::Adt(_adt_def, _generic_args) => {},
        MiddleTyKind::Bound(_debruijn_index, _bound_ty) => {},
        MiddleTyKind::Ref(region, ty, _mutability) => {
            // TODO: the reference may be outlived and/or outliving.
            dbg!(region);
            if let RegionKind::ReBound(_debruijn_index, bound_region) = region.kind() {
                if let BoundRegionKind::BrNamed(def_id, symbol) = bound_region.kind {
                    dbg!(def_id);
                    dbg!(symbol.as_str()); // has .as_str() use this to collect into BoundLifetimePair
                    if let Some(shorter_lifetime_name) = shorter_lifetime_name_opt {
                        let bound_lifetime_pair = BoundLifetimePair {
                            long_lifetime_name: symbol.to_ident_string(),
                            outlived_lifetime_name: shorter_lifetime_name.clone(),
                        };
                        implied_bounds.insert(bound_lifetime_pair);
                    }
                }
            }
            dbg!(ty); // contains the subtype
        },
        MiddleTyKind::FnDef(_def_id, _generic_args) => {},
        MiddleTyKind::Closure(_def_id, _generic_args) => {},
        MiddleTyKind::CoroutineClosure(_def_id, _generic_args) => {},
        MiddleTyKind::Coroutine(_def_id, _generic_args) => {},
        MiddleTyKind::CoroutineWitness(_def_id, _generic_args) => {},
        MiddleTyKind::Param(_param_ty) => {},
        MiddleTyKind::Tuple(tys) => {
            // TODO: the subtypes may contain outliving references
            for ty in tys {
                dbg!(ty);
            }
        },
        _ => {},
    }
    implied_bounds
}
