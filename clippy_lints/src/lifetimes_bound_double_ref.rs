use rustc_lint::{EarlyLintPass, LateContext, LateLintPass};
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
pub struct LifetimesBoundDoubleRef {
    shown_generic: bool,
    shown_ty: bool,
}

impl_lint_pass!(LifetimesBoundDoubleRef => [ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG]);

impl EarlyLintPass for LifetimesBoundDoubleRef {}

impl LateLintPass<'_> for LifetimesBoundDoubleRef {
    fn check_generic_param(&mut self, _ctx: &LateContext<'_>, param: &rustc_hir::GenericParam<'_>) {
        if !self.shown_generic {
            dbg!(&param);
            dbg!(&param.hir_id.local_id);
            dbg!(&param.def_id);
            dbg!(&param.kind);
            self.shown_generic = true;
        }
    }

    fn check_ty(&mut self, _: &LateContext<'_>, ty: &'_ rustc_hir::Ty<'_>) {
        if !self.shown_ty {
            dbg!(&ty);
            self.shown_ty = true;
        }
    }
}
