use rustc_hir::intravisit::FnKind;
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
    /// ### Example
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b, T>(_val_a: &'a &'b (), val_b: &'b T) -> &'a T {...}
    /// ```
    /// Use instead:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b: 'a, T>(_val_a: &'a &'b (), val_b: &'b T) -> &'a T {...}
    /// ```

    #[clippy::version = "1.78.0"]
    pub ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG,
    nursery,
    "suggest to add lifetime bounds to double reference function arguments"
}

#[derive(Default)]
pub struct LifetimesBoundDoubleRef {}

impl_lint_pass!(LifetimesBoundDoubleRef => [ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG]);

impl LateLintPass<'_> for LifetimesBoundDoubleRef {
    fn check_fn<'tcx>(
        &mut self,
        _ctx: &LateContext<'_>,
        fn_kind: rustc_hir::intravisit::FnKind<'tcx>,
        fn_decl: &'tcx rustc_hir::FnDecl<'tcx>,
        _body: &'tcx rustc_hir::Body<'tcx>,
        _span: rustc_span::Span,
        local_def_id: rustc_span::def_id::LocalDefId,
    ) {
        dbg!(local_def_id);
        dbg!(fn_kind); // includes generics
        let FnKind::ItemFn(ident, generics, _fn_header) = fn_kind else {
            return; // 
        };
        dbg!(ident);
        // collect predicate bounds on lifetime pairs
        for predicate in generics.predicates {
            // etc.
        }
        dbg!(fn_decl); // function argument types as inputs
    }
}
