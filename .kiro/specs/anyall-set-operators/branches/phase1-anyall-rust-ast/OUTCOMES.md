# Phase 1 Outcomes — Rust AST node (`phase1-anyall-rust-ast`)

Implements spec Phase 1: the Rust AST node `ExprKind::All { expr, pred }` (the
non-nested set quantifier `expr.all(pred)` over the element keyword `it`) and
the restricted-predicate type `PredExpr`, all gated behind the `anyall` cargo
feature and fully inert on the default build.

Scope: **cedar repo only** (`cedar-spec/cedar`, the nested independent repo).
No Lean, no DRT, no surface syntax yet. The node is **construct-only**: nothing
parses it, nothing evaluates or validates it meaningfully — those land in later
phases. Every exhaustive-match site that the node forces to be covered gets a
*conservative* Phase-1 arm (reject / fail / unsupported), never a silent pass.

## Commits (cedar repo, branch `phase1-anyall-rust-ast` off Phase 0)

| SHA | What |
|---|---|
| `f9bcc713` | `ast/pred.rs` — `PredExpr`/`PredExprKind` (set-free, non-nested predicate over `it`), smart constructors rejecting every set term, `negate()`, shape eq/hash/cmp, generic `eq_shape<U>`, `with_default_data`; gated re-export in `ast.rs`. 6 unit tests. |
| `e80f22c1` | `ExprKind::All` node (`variant_order` 18) + `Expr::all` / `Expr::any` (`any` lowered losslessly to `!all(!p)`); gated `ExprBuilder::{Pred, all, pred_from_ast}` trait items + impls on the AST, EST, PST builders; all 8 `expr.rs` match arms + `expr_iterator`, `expr_visitor` (`visit_all`), `restricted_expr`, `value`, `evaluator`, `level_validate`, `typecheck`, `entity_manifest`. 6 `Expr`-level tests. |
| `dff948a4` | **Review round 1 fix** — `tpe/residual.rs` exhaustive match missing an `All` arm (reached via `experimental` → `tpe`). Added gated `AllNotSupportedError` + conservative arm. |
| `fd487f13` | **Review round 2 fix** — (a) `ExprWithErrsBuilder` (the `tolerant-ast` fallible builder) missing the gated `type Pred`/`all`/`pred_from_ast` → `anyall+tolerant-ast`, `--all-features`, cedar-policy `--features experimental` all failed E0046; (b) cedar-policy `proto/ast.rs` AST→protobuf serialization missing an `All` arm → `protobufs+anyall` failed E0004; (c) NIT: `PredExpr::cmp_shape` `Like` arm now uses `Pattern`'s `Ord` directly. |

## Design decisions as built

- **`PredExpr` set-freeness is enforced two ways**: structurally (no `Set`
  variant, no nested `All`, no `Slot`/`Unknown`) and by smart constructor
  (`PredExprBuilder` rejects `isEmpty` and `contains`/`containsAll`/`containsAny`).
  `in` is allowed structurally (whether a particular `in` over a set is a "set
  term" is a Phase-3 validator concern, not a construction-time structural reject).
  `Literal` is already set-free, so `PredExprKind::Lit(Literal)` is reused with no
  wrapper (the planned `SetFreeLiteral` is unnecessary).
- **`any` is a free constructor** `Expr::any(expr, pred)` = `!all(expr, !pred)`,
  not a trait default — because `negate()` lives on `PredExpr`, not on a generic
  builder's `Pred` type. The lowering is lossless (mirrors `e1 >= e2 := !(e1 < e2)`).
- **Builder trait (B2, forced not optional)**: `Expr::try_into_expr<B>` is generic
  over any builder `B` and every arm routes through a trait method on `builder`,
  so the `All` arm must call `builder.all(..)`. Hence gated `type Pred` +
  `fn all` + `fn pred_from_ast` on the shared `ExprBuilder` trait. The AST builder
  has the real impl (`Pred = PredExpr<T>`); `ExprWithErrsBuilder` mirrors it;
  EST/PST have no `All` form until Phase 4, so their `all()` is a documented
  `unreachable!` (`#[expect(clippy::unreachable)]`) — genuinely dead in Phase 1
  since nothing constructs an EST/PST `All` — and their `pred_from_ast` is a safe lift.
- **Conservative Phase-1 arms** (real behavior lands later): `try_type_of` ⇒
  `Some(Type::Bool)`; `evaluator` ⇒ `non_value` residual (real short-circuit eval
  = Phase 3); `typecheck` ⇒ `TypecheckAnswer::fail` (real type rule = Phase 3 §6);
  `entity_manifest` ⇒ unsupported-feature error; `tpe` ⇒ `AllNotSupportedError`
  (real TPE = Phase 6.5); `restricted_expr` ⇒ rejected; `value` `TryFrom` ⇒
  `NotValue`; `level_validate` ⇒ recurse the receiver only.
- **Subexpression/visitor walks descend into the `Expr` receiver only**, not the
  `PredExpr` (a distinct type). Harmless in Phase 1 (`PredExpr` has no `Unknown`/
  `Slot`), but recorded as a Phase-3 follow-up: once a parser produces an `All`,
  any analysis relying on `subexpressions()` to see every leaf (e.g.
  `contains_unknown`, slot/var collection) must also walk the predicate.

## Verification (green, non-vacuous)

- **Build matrix 8/8 green** (round 3 confirmed): core `default` / `anyall` /
  `anyall tolerant-ast` / `experimental` / `--all-features`; cedar-policy
  `default` / `experimental` / `--all-features`. No `E0004`/`E0046`.
- **Tests**: `cedar-policy-core` lib **1562** (default) → **1574** (`--features
  anyall`) = exactly **+12** new tests (6 `ast::pred::test::*` + 6
  `ast::expr::anyall_test::*`), all pass, 0 ignored. Non-vacuity proven by a
  reviewer: mutating `Expr::any` to drop `.negate()` makes
  `any_lowers_to_not_all_not` FAIL.
- **clippy** `--all-features` (core): 0 errors; no new warning attributable to
  the diff.
- **Inertness**: `default` lists contain no `anyall`; every new item is
  `#[cfg(feature = "anyall")]`; diff is purely additive.

## Review loop (user mandate — fresh blind agent each round until clean)

| Round | Agent | Verdict |
|---|---|---|
| 1 | `e92f6e48` | 1 BLOCKER — `tpe/residual.rs` missing `All` arm (feature-combination gap `experimental`→`tpe`). Fixed `dff948a4`. |
| 2 | `680e5e0b` | 1 BLOCKER — `ExprWithErrsBuilder` + cedar-policy `proto/ast.rs` missing `All` (combinations `anyall+tolerant-ast`, `protobufs+anyall`); + 1 NIT (`cmp_shape` Like). Fixed `fd487f13`. |
| 3 | `083848fa` | **NO ACTIONABLE FINDINGS** — full 8/8 matrix green, every exhaustive `ast::ExprKind` match has a gated arm, prior fixes correct, tests non-vacuous. Loop converged. |

**Process lesson carried forward**: a single `cargo check --features anyall` is
insufficient for a feature-gated enum-variant change — exhaustive matches in
*other* gated modules only break under feature *combinations*. The required
sweep (now in the reviewer brief and saved as a durable lesson): default, the
flag, flag+each sibling gated feature (`tolerant-ast`, `protobufs`, `tpe`),
`--all-features`, and each dependent crate's `experimental`/`--all-features`
(cedar-policy `experimental` pulls a different gated set — `tolerant-ast` +
`anyall` + `protobufs` — than core's `anyall` + `tpe`).

## Residual risks / follow-ups for later phases
- Predicate is invisible to `subexpressions()`/visitors (Phase 3, see above).
- EST/PST `all()` is `unreachable!` until Phase 4 adds their `All` form.
- `tpe` / `entity_manifest` / protobuf serialization of `.all`/`.any` are
  deliberately unsupported until Phases 6.5 / later.
- `level_validate` does not yet descend into the predicate (Phase 3).
