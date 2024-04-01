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
use std::collections::BTreeMap;
use std::ops::Deref;

use clippy_utils::diagnostics::{span_lint, span_lint_and_help, span_lint_and_sugg};
use rustc_ast::{AngleBracketedArg, GenericArgs, GenericParamKind};
use rustc_errors::Applicability;
use rustc_lint::{EarlyLintPass, LintContext};
use rustc_session::impl_lint_pass;
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
    fn check_fn(
        &mut self,
        early_context: &rustc_lint::EarlyContext<'_>,
        fn_kind: rustc_ast::visit::FnKind<'_>,
        _fn_span: Span,
        _node_id: rustc_ast::NodeId,
    ) {
        let rustc_ast::visit::FnKind::Fn(_fn_ctxt, _ident, fn_sig, _visibility, generics, _block_opt) = fn_kind else {
            return;
        };
        let declared_lifetimes_ast = get_declared_lifetimes_spans_ast(generics);
        if declared_lifetimes_ast.len() <= 1 {
            return;
        }
        let mut linter = ImpliedBoundsLinter::new_ast(declared_lifetimes_ast, generics);
        for param in &fn_sig.decl.inputs {
            linter.collect_implied_lifetime_bounds_ast(&param.ty);
        }
        if let rustc_ast::ast::FnRetTy::Ty(ret_ty) = &fn_sig.decl.output {
            linter.collect_implied_lifetime_bounds_ast(ret_ty);
        }
        linter.report_lints(early_context);
    }

    /// For issues 84591 and 100051
    fn check_item_post(&mut self, early_context: &rustc_lint::EarlyContext<'_>, item: &rustc_ast::Item) {
        let rustc_ast::ItemKind::Impl(box_impl) = &item.kind else {
            return;
        };
        let Some(of_trait_ref) = &box_impl.of_trait else {
            return;
        };
        let declared_lifetimes = get_declared_lifetimes_spans_ast(&box_impl.generics);
        if declared_lifetimes.len() <= 1 {
            return;
        }
        let mut linter = ImpliedBoundsLinter::new_ast(declared_lifetimes, &box_impl.generics);
        linter.collect_nested_ref_bounds_ast_path(&of_trait_ref.path, None);
        // issue 10051 for clause: impl ... for for_clause_ty
        let for_clause_ty = &box_impl.self_ty;
        linter.collect_implied_lifetime_bounds_ast(for_clause_ty);
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

fn get_declared_lifetimes_spans_ast(generics: &rustc_ast::Generics) -> FxHashMap<Symbol, Span> {
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

fn get_declared_bounds_spans_ast(generics: &rustc_ast::Generics) -> BTreeMap<BoundLftPair, Span> {
    let mut declared_bounds = BTreeMap::new();
    generics.params.iter().for_each(|gp| {
        if !gp.bounds.is_empty() {
            let long_lft_sym = gp.ident.name;
            gp.bounds.iter().for_each(|bound| {
                if let rustc_ast::GenericBound::Outlives(outlived_lft) = bound {
                    declared_bounds.insert(BoundLftPair::new(long_lft_sym, outlived_lft.ident.name), gp.span());
                }
            });
        }
    });
    generics.where_clause.predicates.iter().for_each(|wp| {
        if let rustc_ast::WherePredicate::RegionPredicate(wrp) = wp {
            let long_lft_sym = wrp.lifetime.ident.name;
            wrp.bounds.iter().for_each(|bound| {
                if let rustc_ast::GenericBound::Outlives(outlived_lft) = bound {
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
    declared_bounds_spans: BTreeMap<BoundLftPair, Span>, // BTree for consistent reporting order
    // implied_bounds: BTreeSet<BoundLftPair>,              // BTree for consistent reporting order
    implied_bounds_spans: BTreeMap<BoundLftPair, (Span, Span)>, // BTree for consistent reporting order
}

impl ImpliedBoundsLinter {
    fn new_ast(declared_lifetimes_spans_ast: FxHashMap<Symbol, Span>, generics: &rustc_ast::Generics) -> Self {
        ImpliedBoundsLinter {
            declared_lifetimes_spans: declared_lifetimes_spans_ast,
            declared_bounds_spans: get_declared_bounds_spans_ast(generics),
            generics_span: generics.span,
            // implied_bounds: BTreeSet::new(),
            implied_bounds_spans: BTreeMap::new(),
        }
    }

    fn declared_lifetime_sym(&self, lft_sym_opt: Option<Symbol>) -> Option<Symbol> {
        lft_sym_opt.filter(|lft_sym| self.declared_lifetimes_spans.contains_key(lft_sym))
    }

    fn collect_nested_ref_bounds_ast_path(
        &mut self,
        path: &rustc_ast::ast::Path,
        outlived_lft_sym_span_opt: Option<(Symbol, Span)>,
    ) {
        for path_segment in &path.segments {
            if let Some(generic_args) = &path_segment.args {
                if let GenericArgs::AngleBracketed(ab_args) = generic_args.deref() {
                    for ab_arg in &ab_args.args {
                        if let AngleBracketedArg::Arg(generic_arg) = ab_arg {
                            use rustc_ast::ast::GenericArg::*;
                            match generic_arg {
                                Lifetime(long_lft) => {
                                    if let Some(outlived_lft_sym_span) = outlived_lft_sym_span_opt {
                                        self.add_implied_bound_spans(
                                            long_lft.ident.name,
                                            outlived_lft_sym_span.0,
                                            long_lft.ident.span,
                                            outlived_lft_sym_span.1,
                                        );
                                    }
                                },
                                Type(p_ty) => {
                                    self.collect_nested_ref_bounds_ast(&p_ty, outlived_lft_sym_span_opt);
                                },
                                Const(_anon_const) => {},
                            }
                        }
                    }
                }
            }
        }
    }

    fn collect_implied_lifetime_bounds_ast(&mut self, ty: &rustc_ast::ast::Ty) {
        self.collect_nested_ref_bounds_ast(ty, None);
    }

    fn collect_nested_ref_bounds_ast(
        &mut self,
        outliving_ty: &rustc_ast::ast::Ty,
        outlived_lft_sym_span_opt: Option<(Symbol, Span)>,
    ) {
        use rustc_ast::ast::TyKind::*;
        let mut outliving_tys = vec![outliving_ty];
        while let Some(ty) = outliving_tys.pop() {
            match &ty.kind {
                Ref(lifetime_opt, referred_to_mut_ty) => {
                    let referred_to_ty = &referred_to_mut_ty.ty;
                    if let Some(lifetime) = lifetime_opt
                        && let Some(declared_lifetime_sym) = self.declared_lifetime_sym(Some(lifetime.ident.name))
                    {
                        if let Some(outlived_lft_sym_span) = outlived_lft_sym_span_opt {
                            self.add_implied_bound_spans(
                                lifetime.ident.name,
                                outlived_lft_sym_span.0,
                                lifetime.ident.span,
                                outlived_lft_sym_span.1,
                            );
                        }
                        self.collect_nested_ref_bounds_ast(
                            referred_to_ty,
                            Some((declared_lifetime_sym, lifetime.ident.span)),
                        );
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
                    self.collect_nested_ref_bounds_ast_path(path, outlived_lft_sym_span_opt);
                },
                TraitObject(generic_bounds, _trait_object_syntax) => {
                    // FIXME: add self.collect_nested_ref_generic_bounds_ast(generic_bounds, outlived_lft_opt)
                    for generic_bound in generic_bounds {
                        use rustc_ast::ast::GenericBound::*;
                        match generic_bound {
                            Trait(_poly_trait_ref, _trait_bound_modifier) => {
                                dbg!(generic_bound);
                            },
                            Outlives(_lifetime) => {
                                dbg!(generic_bound);
                            },
                        }
                    }
                },
                ImplTrait(_node_id, _generic_bounds) => {
                    // FIXME: use collect_nested_ref_generic_bounds_ast
                    dbg!(&ty);
                },
                AnonStruct(..) | AnonUnion(..) | BareFn(..) | CVarArgs | Dummy | Err(..) | ImplicitSelf | Infer
                | MacCall(..) | Never | Paren(..) | Ptr(..) | Typeof(..) => {},
            }
        }
    }

    fn add_implied_bound_spans(
        &mut self,
        long_lft_sym: Symbol,
        outlived_lft_sym: Symbol,
        long_lft_span: Span,
        outlived_lft_span: Span,
    ) {
        if long_lft_sym != outlived_lft_sym {
            // only unequal symbols form a lifetime bound
            self.implied_bounds_spans.insert(
                BoundLftPair::new(long_lft_sym, outlived_lft_sym),
                (long_lft_span, outlived_lft_span),
            );
        }
    }

    fn get_declared_lifetime_span(&self, lft_sym: Symbol) -> Option<Span> {
        self.declared_lifetimes_spans.get(&lft_sym).copied()
    }

    fn report_lints<T: LintContext>(self, cx: &T) {
        for implied_bound_spans in &self.implied_bounds_spans {
            if !self.declared_bounds_spans.contains_key(implied_bound_spans.0) {
                let declaration = implied_bound_spans.0.as_bound_declaration();
                let msg = &format!("missing lifetimes bound declaration: {declaration}");
                if let Some(long_lft_decl_span) = self.get_declared_lifetime_span(implied_bound_spans.0.long_lft_sym) {
                    span_lint_and_sugg(
                        cx,
                        EXPLICIT_LIFETIMES_BOUND,
                        long_lft_decl_span,
                        msg,
                        "try",
                        declaration,
                        Applicability::MachineApplicable,
                    );
                } else {
                    span_lint(cx, EXPLICIT_LIFETIMES_BOUND, self.generics_span, msg);
                }
            }
        }

        for (declared_bound, predicate_span) in self.declared_bounds_spans {
            if self.implied_bounds_spans.contains_key(&declared_bound) {
                let help_span = None; // the span of the nested ref would be better
                span_lint_and_help(
                    cx,
                    IMPLICIT_LIFETIMES_BOUND,
                    predicate_span,
                    &format!(
                        "declared lifetimes bound is implied: {}",
                        declared_bound.as_bound_declaration(),
                    ),
                    help_span,
                    "consider removing this lifetimes bound",
                );
            }
        }
    }
}
