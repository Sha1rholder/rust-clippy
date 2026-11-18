use clippy_utils::diagnostics::span_lint_and_then;
use clippy_utils::msrvs::{self, Msrv};
use clippy_utils::res::MaybeResPath as _;
use clippy_utils::source::SpanExt as _;
use clippy_utils::sugg::Sugg;
use clippy_utils::ty::expr_type_is_certain;
use clippy_utils::{eq_expr_value, expr_custom_deref_adjustment, span_contains_comment, sym};
use rustc_errors::Applicability;
use rustc_hir::{Expr, ExprKind, Mutability, UnOp};
use rustc_lexer::{FrontmatterAllowed, TokenKind, tokenize};
use rustc_lint::{LateContext, std_or_core};
use rustc_middle::ty::{self, TyCtxt};

use super::MANUAL_BOOL_TOGGLE;

pub(super) fn check(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
    lhs: &Expr<'_>,
    rhs: &Expr<'_>,
    msrv: Msrv,
    has_competing_toggle: &mut Option<bool>,
) {
    if let ExprKind::Unary(UnOp::Not, operand) = rhs.kind
        && !expr.span.from_expansion()
        && !rhs.span.from_expansion()
        && !operand.span.from_expansion()
        && cx.typeck_results().expr_ty(lhs).is_bool()
        && msrv.meets(cx, msrvs::BOOL_TOGGLE)
        && is_repeatable_place(cx, lhs)
        && eq_expr_value(cx, expr.span.ctxt(), lhs, operand)
        && expr.span.check_text(cx, is_plain_assignment)
    {
        span_lint_and_then(
            cx,
            MANUAL_BOOL_TOGGLE,
            expr.span,
            "manual implementation of `bool::toggle`",
            |diag| {
                let (receiver, is_mut_ref) = match lhs.kind {
                    ExprKind::Unary(UnOp::Deref, base) => (base, true),
                    _ => (lhs, false),
                };
                let use_method = expr_type_is_certain(cx, receiver)
                    && (is_mut_ref || !*has_competing_toggle.get_or_insert_with(|| trait_may_shadow_toggle(cx.tcx)));
                // Other configurations may bring a competing trait into scope for a bare bool.
                let mut app = if (use_method && !is_mut_ref) || span_contains_comment(cx, expr.span) {
                    Applicability::MaybeIncorrect
                } else {
                    Applicability::MachineApplicable
                };
                let sugg = Sugg::hir_with_applicability(cx, receiver, "..", &mut app);
                let replacement = if use_method {
                    format!("{}.toggle()", sugg.maybe_paren())
                } else if let Some(krate) = std_or_core(cx) {
                    let arg = if is_mut_ref { sugg } else { sugg.mut_addr() };
                    format!("::{krate}::primitive::bool::toggle({arg})")
                } else {
                    return;
                };
                diag.span_suggestion(expr.span, "use", replacement, app);
            },
        );
    }
}

fn is_plain_assignment(source: &str) -> bool {
    use TokenKind::{Bang, BlockComment, Eq, LineComment, OpenParen, Pound, Whitespace};
    // Forwarded macro arguments can have call-site spans even after expansion.
    let mut tokens = tokenize(source, FrontmatterAllowed::No)
        .map(|token| token.kind)
        .filter(|kind| !matches!(kind, Whitespace | LineComment { .. } | BlockComment { .. } | OpenParen));
    tokens.find(|kind| matches!(kind, Eq | Bang | Pound)) == Some(Eq)
        && tokens.next() == Some(Bang)
        && !tokens.any(|kind| matches!(kind, Eq | Bang | Pound))
}

// rustc records in-scope trait candidates for existing method calls. For a new call on a
// `bool`, conservatively check for methods that could precede its inherent `&mut self` method.
fn trait_may_shadow_toggle(tcx: TyCtxt<'_>) -> bool {
    tcx.all_traits_including_private()
        .filter(|&id| tcx.is_trait(id))
        .flat_map(|id| tcx.associated_item_def_ids(id))
        .any(|&item| {
            tcx.opt_item_name(item) == Some(sym::toggle)
                && tcx.associated_item(item).is_method()
                && !matches!(
                    tcx.fn_sig(item).instantiate_identity().skip_binder().inputs()[0].kind(),
                    ty::Ref(_, _, Mutability::Mut)
                )
        })
}

// Removing the second evaluation must not skip a call to user-defined Deref or Index.
fn is_repeatable_place(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if expr.span.from_expansion() || expr_custom_deref_adjustment(cx, expr).is_some() {
        return false;
    }
    match expr.kind {
        ExprKind::Field(base, _) => is_repeatable_place(cx, base),
        ExprKind::Unary(UnOp::Deref, base) => {
            cx.typeck_results().expr_ty(base).is_ref() && is_repeatable_place(cx, base)
        },
        ExprKind::Index(base, index, _) => {
            cx.typeck_results().type_dependent_def_id(expr.hir_id).is_none()
                && !index.span.from_expansion()
                && (index.res_local_id().is_some() || matches!(index.kind, ExprKind::Lit(_)))
                && is_repeatable_place(cx, base)
        },
        _ => expr.res_local_id().is_some(),
    }
}
