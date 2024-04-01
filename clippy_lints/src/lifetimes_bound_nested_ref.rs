/// Lints to help dealing with unsoundness due to a compiler bug described here:
/// <https://github.com/rust-lang/rustc-dev-guide/blob/478a77a902f64e5128e7164e4e8a3980cfe4b133/src/traits/implied-bounds.md>.
///
/// For the following three cases the current compiler (1.76.0) gives a later error message when
/// manually adding a generic lifetime bound that is implied by a nested reference:
///
///     Issue 25860:
///     Implied bounds on nested references + variance = soundness hole
///     
///     Issue 84591:
///     HRTB on subtrait unsoundly provides HTRB on supertrait with weaker implied bounds
///     
///     Issue 100051:
///     implied bounds from projections in impl header can be unsound
///     
/// The lint here suggests to add such lifetime bounds in the hope that
/// the unsoundness is avoided.
///
/// There is also a reverse lint that suggest to remove lifetime bounds
/// that are implied by nested references. This reverse lint is intended to be used only
/// when the compiler has been fixed to handle these lifetime bounds correctly.
///
/// The lints here are in the nursery category.
use std::cmp::Ordering;
use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::ops::Deref;

use clippy_utils::diagnostics::{span_lint, span_lint_and_help, span_lint_and_then};
use rustc_ast::visit::FnKind;
use rustc_ast::{
    AngleBracketedArg, FnRetTy, GenericArg, GenericArgs, GenericBound, GenericParamKind, Generics, Item, ItemKind,
    NodeId, Path, Ty, TyKind, WherePredicate,
};
use rustc_errors::Applicability;
use rustc_lint::{EarlyContext, EarlyLintPass, Lint, LintContext};
use rustc_session::impl_lint_pass;
use rustc_span::symbol::Ident;
use rustc_span::{Span, Symbol};

extern crate rustc_hash;
use rustc_hash::FxHashMap;

declare_clippy_lint! {
    /// ### What it does
    /// For function arguments and return values and for implementation blocks
    /// this checks for nested references with generic lifetimes
    /// that imply a lifetimes bound because the inner reference must
    /// outlive the outer reference.
    /// This suggests to declare such implicit lifetime bounds.
    /// Adding such a bound helps to avoid unsound code because this addition
    /// can lead to a compiler error in related source code, as observed in rustc 1.76.0.
    ///
    /// ### Why is this bad?
    /// The unsoundness is described here:
    /// <https://github.com/rust-lang/rustc-dev-guide/blob/478a77a902f64e5128e7164e4e8a3980cfe4b133/src/traits/implied-bounds.md>.
    ///
    /// ### Known problems
    /// It is not known whether this covers all cases that might lead to unsoundness.
    ///
    /// ### Example, the `val_a` argument implies a lifetimes bound:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b, T>(val_a: &'a &'b (), val_b: &'b T) -> &'a T {
    ///     val_b
    /// }
    /// ```
    /// Use instead:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b: 'a, T>(val_a: &'a &'b (), val_b: &'b T) -> &'a T {
    ///     val_b
    /// }
    /// ```
    #[clippy::version = "1.79.0"]
    pub EXPLICIT_LIFETIMES_BOUND,
    nursery,
    "declare generic lifetime bounds implied by nested references"
}

declare_clippy_lint! {
    /// ### What it does
    /// For function arguments and return values and implementation blocks
    /// this checks for nested references with generic lifetimes
    /// that imply a lifetimes bound because the inner reference must
    /// outlive the outer reference.
    /// This suggests to remove such implicit lifetime bounds when
    /// they are declared.
    ///
    /// ### Why is this bad?
    /// The declared lifetime bounds are superfluous.
    ///
    /// ### Known problems
    /// Removing such explicitly declared lifetime bounds may lead to the unsoundness described here:
    /// <https://github.com/rust-lang/rustc-dev-guide/blob/478a77a902f64e5128e7164e4e8a3980cfe4b133/src/traits/implied-bounds.md>.
    /// Removing these redundant lifetime bounds should only be done after the compiler
    /// has been fixed to deal correctly with implied lifetime bounds.
    ///
    /// ### Example, the `val_a` argument implies a lifetimes bound:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b: 'a, T>(val_a: &'a &'b (), val_b: &'b T) -> &'a T {
    ///     val_b
    /// }
    /// ```
    /// Use instead:
    /// ```no_run
    /// pub const fn lifetime_translator<'a, 'b, T>(val_a: &'a &'b (), val_b: &'b T) -> &'a T {
    ///     val_b
    /// }
    /// ```

    #[clippy::version = "1.79.0"]
    pub IMPLICIT_LIFETIMES_BOUND,
    nursery,
    "remove declared generic lifetime bounds implied by nested references"
}

pub struct LifetimesBoundNestedRef;

impl_lint_pass!(LifetimesBoundNestedRef => [
    EXPLICIT_LIFETIMES_BOUND,
    IMPLICIT_LIFETIMES_BOUND,
]);

impl EarlyLintPass for LifetimesBoundNestedRef {
    /// For issue 25860
    fn check_fn(&mut self, early_context: &EarlyContext<'_>, fn_kind: FnKind<'_>, _fn_span: Span, _node_id: NodeId) {
        let FnKind::Fn(_fn_ctxt, _ident, fn_sig, _visibility, generics, _block_opt) = fn_kind else {
            return;
        };
        let declared_lifetimes_spans = get_declared_lifetimes_spans(generics);
        if declared_lifetimes_spans.len() <= 1 {
            return;
        }
        let mut linter = ImpliedBoundsLinter::new(declared_lifetimes_spans, generics);
        for param in &fn_sig.decl.inputs {
            linter.collect_implied_lifetime_bounds(&param.ty);
        }
        if let FnRetTy::Ty(ret_ty) = &fn_sig.decl.output {
            linter.collect_implied_lifetime_bounds(ret_ty);
        }
        linter.report_lints(early_context);
    }

    /// For issues 84591 and 100051
    fn check_item_post(&mut self, early_context: &EarlyContext<'_>, item: &Item) {
        let ItemKind::Impl(box_impl) = &item.kind else {
            return;
        };
        let Some(of_trait_ref) = &box_impl.of_trait else {
            return;
        };
        let declared_lifetimes = get_declared_lifetimes_spans(&box_impl.generics);
        if declared_lifetimes.len() <= 1 {
            return;
        }
        let mut linter = ImpliedBoundsLinter::new(declared_lifetimes, &box_impl.generics);
        linter.collect_implied_lifetime_bounds_path(&of_trait_ref.path);
        // issue 10051 for clause: impl ... for for_clause_ty
        let for_clause_ty = &box_impl.self_ty;
        linter.collect_implied_lifetime_bounds(for_clause_ty);
        linter.report_lints(early_context);
    }
}

#[derive(Debug)]
struct BoundLftPair {
    long_lft_sym: Symbol,
    outlived_lft_sym: Symbol,
}

impl BoundLftPair {
    fn new(long_lft_sym: Symbol, outlived_lft_sym: Symbol) -> Self {
        BoundLftPair {
            long_lft_sym,
            outlived_lft_sym,
        }
    }

    fn as_bound_declaration(&self) -> String {
        format!("{}: {}", self.long_lft_sym, self.outlived_lft_sym)
    }
}

impl PartialEq for BoundLftPair {
    fn eq(&self, other: &Self) -> bool {
        self.long_lft_sym.eq(&other.long_lft_sym) && self.outlived_lft_sym.eq(&other.outlived_lft_sym)
    }
}

impl Eq for BoundLftPair {}

impl PartialOrd for BoundLftPair {
    fn partial_cmp(&self, other: &BoundLftPair) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BoundLftPair {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.long_lft_sym.cmp(&other.long_lft_sym) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => self.outlived_lft_sym.cmp(&other.outlived_lft_sym),
        }
    }
}

fn get_declared_lifetimes_spans(generics: &Generics) -> FxHashMap<Symbol, Span> {
    generics
        .params
        .iter()
        .filter_map(|gp| {
            if let GenericParamKind::Lifetime = gp.kind {
                Some((gp.ident.name, gp.ident.span))
            } else {
                None
            }
        })
        .collect()
}

fn get_declared_bounds_spans(generics: &Generics) -> BTreeMap<BoundLftPair, Span> {
    let mut declared_bounds = BTreeMap::new();
    generics.params.iter().for_each(|gp| {
        if !gp.bounds.is_empty() {
            let long_lft_sym = gp.ident.name;
            gp.bounds.iter().for_each(|bound| {
                if let GenericBound::Outlives(outlived_lft) = bound {
                    let decl_span = if let Some(colon_span) = gp.colon_span {
                        spans_merge(colon_span, outlived_lft.ident.span)
                    } else {
                        outlived_lft.ident.span
                    };
                    declared_bounds.insert(BoundLftPair::new(long_lft_sym, outlived_lft.ident.name), decl_span);
                }
            });
        }
    });
    generics.where_clause.predicates.iter().for_each(|wp| {
        if let WherePredicate::RegionPredicate(wrp) = wp {
            let long_lft_sym = wrp.lifetime.ident.name;
            wrp.bounds.iter().for_each(|bound| {
                if let GenericBound::Outlives(outlived_lft) = bound {
                    // CHECKME: how to make a good span for the lifetimes bound declaration here?
                    declared_bounds.insert(BoundLftPair::new(long_lft_sym, outlived_lft.ident.name), wrp.span);
                }
            })
        }
    });
    declared_bounds
}

#[derive(Debug)]
struct ImpliedBoundsLinter {
    declared_lifetimes_spans: FxHashMap<Symbol, Span>,
    generics_span: Span,
    declared_bounds_spans: BTreeMap<BoundLftPair, Span>,
    implied_bounds_spans: BTreeMap<BoundLftPair, (Span, Span)>,
}

impl ImpliedBoundsLinter {
    fn new(declared_lifetimes_spans: FxHashMap<Symbol, Span>, generics: &Generics) -> Self {
        ImpliedBoundsLinter {
            declared_lifetimes_spans,
            declared_bounds_spans: get_declared_bounds_spans(generics),
            generics_span: generics.span,
            implied_bounds_spans: BTreeMap::new(),
        }
    }

    fn is_declared_lifetime_sym(&self, lft_sym: Symbol) -> bool {
        self.declared_lifetimes_spans.contains_key(&lft_sym)
    }

    fn collect_implied_lifetime_bounds_path(&mut self, path: &Path) {
        self.collect_nested_ref_bounds_path(path, None);
    }

    fn collect_nested_ref_bounds_path(&mut self, path: &Path, outlived_lft_ident_opt: Option<Ident>) {
        for path_segment in &path.segments {
            if let Some(generic_args) = &path_segment.args {
                if let GenericArgs::AngleBracketed(ab_args) = generic_args.deref() {
                    for ab_arg in &ab_args.args {
                        if let AngleBracketedArg::Arg(generic_arg) = ab_arg {
                            use GenericArg::*;
                            match generic_arg {
                                Lifetime(long_lft) => {
                                    if let Some(outlived_lft_ident) = outlived_lft_ident_opt {
                                        self.add_implied_bound_spans(long_lft.ident, outlived_lft_ident);
                                    }
                                },
                                Type(p_ty) => {
                                    self.collect_nested_ref_bounds(&p_ty, outlived_lft_ident_opt);
                                },
                                Const(_anon_const) => {},
                            }
                        }
                    }
                }
            }
        }
    }

    fn collect_implied_lifetime_bounds(&mut self, ty: &Ty) {
        self.collect_nested_ref_bounds(ty, None);
    }

    fn collect_nested_ref_bounds(&mut self, outliving_ty: &Ty, outlived_lft_ident_opt: Option<Ident>) {
        use TyKind::*;
        let mut outliving_tys = vec![outliving_ty];
        while let Some(ty) = outliving_tys.pop() {
            match &ty.kind {
                Ref(lifetime_opt, referred_to_mut_ty) => {
                    let referred_to_ty = &referred_to_mut_ty.ty;
                    if let Some(lifetime) = lifetime_opt
                        && self.is_declared_lifetime_sym(lifetime.ident.name)
                    {
                        if let Some(outlived_lft_ident) = outlived_lft_ident_opt {
                            self.add_implied_bound_spans(lifetime.ident, outlived_lft_ident);
                        }
                        self.collect_nested_ref_bounds(referred_to_ty, Some(lifetime.ident));
                    } else {
                        outliving_tys.push(referred_to_ty);
                    }
                },
                Slice(element_ty) => {
                    outliving_tys.push(element_ty);
                },
                Array(element_ty, _anon_const) => {
                    outliving_tys.push(element_ty);
                },
                Tup(tuple_tys) => {
                    for tuple_ty in tuple_tys {
                        outliving_tys.push(tuple_ty);
                    }
                },
                Path(q_self_opt, path) => {
                    if let Some(q_self) = q_self_opt {
                        outliving_tys.push(&q_self.ty);
                    }
                    self.collect_nested_ref_bounds_path(path, outlived_lft_ident_opt);
                },
                TraitObject(_generic_bounds, _trait_object_syntax) => {
                    // CHECKME: use the outlived lifetimes in the generic bounds?
                },
                ImplTrait(_node_id, _generic_bounds) => {
                    // CHECKME: use the generic bounds as for TraitObject?
                },
                AnonStruct(_node_id, _field_defs) | AnonUnion(_node_id, _field_defs) => {
                    // CHECKME: use the type in the field definitions?
                },
                BareFn(_bare_fn_ty) => {
                    // CHECKME: use the generic params and the function definition?
                },
                CVarArgs | Dummy | Err(..) | ImplicitSelf | Infer | MacCall(..) | Never | Paren(..) | Ptr(..)
                | Typeof(..) => {},
            }
        }
    }

    fn add_implied_bound_spans(&mut self, long_lft_ident: Ident, outlived_lft_ident: Ident) {
        if long_lft_ident.name != outlived_lft_ident.name {
            // only unequal symbols form a lifetime bound
            match self
                .implied_bounds_spans
                .entry(BoundLftPair::new(long_lft_ident.name, outlived_lft_ident.name))
            {
                Entry::Vacant(ve) => {
                    // in nested references the outlived lifetime occurs first
                    ve.insert((outlived_lft_ident.span, long_lft_ident.span));
                },
                Entry::Occupied(mut oe) => {
                    // keep the first occurrence of the nested reference
                    let prev_spans = oe.get_mut();
                    if span_is_before(outlived_lft_ident.span, prev_spans.0)
                        || (outlived_lft_ident.span == prev_spans.0
                            && span_is_before(long_lft_ident.span, prev_spans.1))
                    {
                        *prev_spans = (outlived_lft_ident.span, long_lft_ident.span);
                    }
                },
            }
        }
    }

    fn get_declared_lifetime_span(&self, lft_sym: Symbol) -> Option<Span> {
        self.declared_lifetimes_spans.get(&lft_sym).copied()
    }

    fn report_lints(self, cx: &EarlyContext<'_>) {
        let bound_implied_here_note = "this lifetimes bound is implied here:";
        for implied_bound_spans in &self.implied_bounds_spans {
            let (outlived_lft_span, long_lft_span) = implied_bound_spans.1;
            let nested_ref_span = spans_merge(*outlived_lft_span, *long_lft_span);
            if !self.declared_bounds_spans.contains_key(implied_bound_spans.0) {
                let declaration = implied_bound_spans.0.as_bound_declaration();
                let msg = &format!("missing lifetimes bound declaration: {declaration}");
                if let Some(long_lft_decl_span) = self.get_declared_lifetime_span(implied_bound_spans.0.long_lft_sym) {
                    span_lint_and_fix_sugg_and_note(
                        cx,
                        EXPLICIT_LIFETIMES_BOUND,
                        long_lft_decl_span,
                        msg,
                        "try",
                        declaration,
                        nested_ref_span,
                        bound_implied_here_note,
                    );
                } else {
                    span_lint(cx, EXPLICIT_LIFETIMES_BOUND, self.generics_span, msg);
                }
            }
        }

        for (declared_bound, decl_span) in self.declared_bounds_spans {
            if let Some((outlived_lft_span, long_lft_span)) = self.implied_bounds_spans.get(&declared_bound) {
                let nested_ref_span = spans_merge(*outlived_lft_span, *long_lft_span);
                span_lint_and_help(
                    cx,
                    IMPLICIT_LIFETIMES_BOUND,
                    decl_span,
                    &format!(
                        "declared lifetimes bound is redundant: {}",
                        declared_bound.as_bound_declaration(),
                    ),
                    Some(nested_ref_span),
                    bound_implied_here_note,
                );
            }
        }
    }
}

fn span_is_before(span1: Span, span2: Span) -> bool {
    let lo1 = span1.lo();
    let lo2 = span2.lo();
    use Ordering::*;
    match lo1.cmp(&lo2) {
        Less => true,
        Greater => false,
        Equal => span1.hi() < span2.hi(),
    }
}

fn spans_merge(span1: Span, span2: Span) -> Span {
    Span::new(
        span1.lo().min(span2.lo()),
        span1.hi().max(span2.hi()),
        span1.ctxt(),
        span1.parent(),
    )
}

/// Combine span_lint_and_sugg and span_lint_and_help:
/// give a lint error, a suggestion to fix, and a note on the cause of the lint in the code.
fn span_lint_and_fix_sugg_and_note<T: LintContext>(
    cx: &T,
    lint: &'static Lint,
    sp: Span,
    msg: &str,
    fix_help: &str,
    sugg: String,
    cause_span: Span,
    cause_note: &'static str,
) {
    span_lint_and_then(cx, lint, sp, msg, |diag| {
        diag.span_suggestion(sp, fix_help.to_string(), sugg, Applicability::MachineApplicable);
        diag.span_help(cause_span, cause_note);
    });
}
