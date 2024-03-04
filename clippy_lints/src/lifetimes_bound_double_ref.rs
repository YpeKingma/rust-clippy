use clippy_utils::diagnostics::span_lint_and_help;
use rustc_lint::{EarlyContext, EarlyLintPass, LateLintPass};
use rustc_session::impl_lint_pass;
use rustc_ast::ast::{GenericParam, GenericParamKind};


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

pub struct LifetimesBoundDoubleRef;

impl_lint_pass!(LifetimesBoundDoubleRef => [ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG]);

impl EarlyLintPass for LifetimesBoundDoubleRef {
    fn check_generic_param(&mut self, ctx: &EarlyContext<'_>, param: &GenericParam) {
        // CHECKME: it is probably ok to warn for this in an external macro.
        // if in_external_macro(ctx.sess(), param.ident.span) {
        //     return;
        // }

        if let GenericParamKind::Lifetime = param.kind {
            // FIXME: check for double reference with lifetimes.
            if !param.is_placeholder && param.ident.as_str().len() <= 2 {
                span_lint_and_help(
                    ctx,
                    ADD_REDUNDANT_LIFETIMES_BOUND_DOUBLE_REF_ARG,
                    param.ident.span,
                    "double reference argument with lifetimes but without lifetimes bound",
                    None,
                    "add a lifetimes bound for the lifetimes of the reference",
                );
            }
        }
    }
}

impl LateLintPass<'_> for LifetimesBoundDoubleRef {}
