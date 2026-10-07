# Tasks — `.any` / `.all` non-nested set operators

Implementation plan as a sequence of **small commits**. Every commit must keep **all three
surfaces green**:

- Lean: `lake build Cedar` from `cedar-lean/`.
- DRT: `cargo test` and `cargo test --features integration-testing` from `cedar-drt/`.
- Rust core: the `cedar-policy-core` / `cedar-policy` test suites, both with and without
  `--features anyall`.

The ordering guarantees each intermediate commit builds and passes, because the feature is
introduced **flag-gated and inert** first, then wired surface-by-surface, and the DRT
generator arm (which couples the surfaces differentially) is turned on **last**, only after
all three engines understand the node.

Each task lists the requirement IDs (from `requirements.md`) it satisfies.

---

## Phase 0 — Feature flags, inert

- **T0.1 Add the `anyall` Cargo feature (off by default).**
  Add `anyall = []` to `cedar-policy-core/Cargo.toml` and propagate an optional pass-through
  feature in `cedar-policy/Cargo.toml`, `cedar-drt/Cargo.toml`, `cedar-drt/fuzz/Cargo.toml`,
  and `cedar-policy-generators/Cargo.toml`. No code paths yet.
  _Green check:_ builds unchanged with and without the flag.
  _Satisfies:_ 3.1.

- **T0.2 Add the Lean build flag, inert.**
  Introduce the `anyall` gating mechanism in `cedar-lean/` (lakefile option / `set_option`
  or a `Cedar/Spec/Features.lean` boolean the new constructs are guarded by). No new
  constructors yet.
  _Green check:_ `lake build Cedar` unchanged.
  _Satisfies:_ 3.2.

## Phase 1 — Rust AST, gated, no parser/eval yet

- **T1.1 Add the `PredExpr` / `PredExprKind` module.**
  New file `cedar-policy-core/src/ast/pred.rs`, all `#[cfg(feature = "anyall")]`; re-export
  from `ast/mod.rs`. `PredExprKind::Lit` reuses the existing `Literal` directly (already
  set-free — no wrapper type). Include smart constructors that reject `IsEmpty` and
  `Contains`/`ContainsAll`/`ContainsAny` ops and have no `Set` form.
  _Green check:_ core builds with and without `anyall`; new types only compiled under flag.
  _Satisfies:_ 1.5 (structural set-freeness), design Surface 1.

- **T1.2 Add `ExprKind::All { expr, pred }` under `#[cfg(feature = "anyall")]`.**
  Extend every exhaustive match on `ExprKind` with a flag-gated arm: `variant_order`,
  `try_type_of` (→ `Some(Type::Bool)`), `subexpressions`, `eq_shape`, `hash_shape`,
  `cmp_shape`, `substitute_general`, `try_into_expr`. Add `ExprBuilder::all` and a default
  `ExprBuilder::any` method that lowers to `self.not(self.all(expr, pred.negate()))` — the
  same layer and pattern as the existing `greatereq`/`greater` default methods (`>`/`>=` have
  no AST node; neither does `any`).
  _Green check:_ core builds + unit tests pass with and without `anyall`.
  _Satisfies:_ 2.3 (lowering at the builder layer), 4.1 (shape machinery), design Surface 1.

## Phase 2 — Lean spec node + evaluator, gated

- **T2.1 Add `PredExpr` inductive and `Error.quantifierError` (gated).**
  `Cedar/Spec/Expr.lean` + `Cedar/Spec/Value.lean`. Update the hand-written `DecidableEq`
  (`decExpr`/`decExprList`/`decProdAttrExprList`) and any `Repr`/`Inhabited` derivations and
  `sizeOf`/termination lemmas to cover the new constructors.
  _Green check:_ `lake build Cedar`.
  _Satisfies:_ 2.5/2.6 (error constructor), design Surface 2.

- **T2.2 Add `Expr.all` constructor + `evaluate` arm + `PredExpr.instantiate` + `evalAll`.**
  `Cedar/Spec/Expr.lean` (constructor), `Cedar/Spec/Evaluator.lean` (`evalAll`, instantiation,
  new `.all` match arm; type-error when receiver is not a set; deterministic
  `quantifierError` fold; empty-set ⇒ `true`). **Lean has NO `any`**: just as the Lean
  `BinaryOp` has `less`/`lessEq` but no `greater`/`greaterEq` (because the Rust `ExprBuilder`
  already lowered `>`/`>=` before the AST crosses into Lean via DRT), the Lean spec receives
  only `all`. There is therefore no `any` desugaring arm in `Evaluator.lean` — the single
  `all` evaluator arm is all that is needed. The `evalAll` fold MUST NOT short-circuit to
  `.ok false` on the first false element — it must keep scanning for a possible error (req
  2.8); it may stop early only on the first error.
  _Green check:_ `lake build Cedar`; add Lean spec unit tests for 2.1/2.2/2.5/2.7, plus a test
  that `[false-element, erroring-element].all(..)` yields `quantifierError`, not `false` (2.8).
  _Satisfies:_ 2.1, 2.2, 2.3, 2.4, 2.5, 2.6, 2.7, 2.8.

- **T2.3 Repair the structural proofs over `Expr` (gated).**
  Add the `.all` case everywhere a `Thm/` proof recurses over `Expr`: `Thm/WellTyped*`,
  `Thm/Validation/Typechecker*`, `Thm/Validation/Validator.lean`, and evaluator-soundness
  lemmas. Prove the sound type rule: `e : Set τ` and `pred : Bool` under `it : τ` ⇒
  `e.all(pred) : Bool`.
  _Green check:_ `lake build Cedar` (all proofs).
  _Satisfies:_ 2.x type soundness, design Surface 2.

## Phase 3 — Rust evaluator + validator, gated

- **T3.1 Implement the Rust evaluator arm for `ExprKind::All` (gated).**
  Mirror the Lean semantics exactly: instantiate `PredExpr` with each element, deterministic
  `QuantifierError` (new evaluation-error variant, witness = smallest erroring element by the
  existing `Ord`), empty-set ⇒ `true`, non-set receiver ⇒ type error. Do NOT short-circuit on
  the first `false`; scan all elements for a possible error first (req 2.8), matching the Lean
  fold exactly.
  _Green check:_ core tests with `--features anyall`; parity unit tests mirroring the Lean ones
  (including the false-then-error ⇒ QuantifierError case, req 2.8).
  _Satisfies:_ 2.1, 2.2, 2.4, 2.5, 2.6, 2.7, 2.8.

- **T3.2 Implement the Rust validator / well-formedness checks (gated).**
  Type rule for `All` (as T2.3); reject nested quantifiers (1.4), set-containing predicates
  (1.5), and `it` outside a predicate (1.6), in `Expr::try_validate` and the validator.
  _Green check:_ core tests with `--features anyall`.
  _Satisfies:_ 1.4, 1.5, 1.6.

## Phase 4 — Rust surface syntax + roundtrip, gated

- **T4.1 Parser: CST→AST for `.all( … )` / `.any( … )` and the `it` keyword (gated).**
  Add the access-form production and bind `it` → `PredExprKind::Item`; the production **calls
  `builder.all(..)` / `builder.any(..)`** (the builder does the `any`→`!all(!p)` lowering, as
  the relational arm calls `builder.greatereq(..)` at `cst_to_ast.rs:2321`). The parser does
  not construct the negation itself.
  Keep `it` an ordinary identifier when the flag is off (1.3).
  _Green check:_ core parser tests with and without `anyall`.
  _Satisfies:_ 1.1, 1.2, 1.3, 2.3.

- **T4.2 EST (JSON) + `Display` pretty-printer (gated).**
  Add an EST `All { expr, pred }` form whose `pred` is a **full `Expr`** (EST stays simple — no
  restricted predicate type for now; nesting is rejected at EST→AST). Extend `est::Builder` so
  AST→EST stays lossless/infallible; emit `expr.all(pred)` (and `any` as its lowered
  `!expr.all(!pred)`). AST↔EST↔text roundtrip tests. ⚠️ Flagged: a restricted `est::PredExpr`
  (structural non-nesting at EST) is a possible future tightening.
  _Green check:_ core roundtrip tests with `anyall`.
  _Satisfies:_ 4.1, 4.3.

- **T4.3 Protobuf schema + round-trip (gated).**
  Add the `All` message to the protobuf schema and the encode/decode mapping; round-trip test.
  _Green check:_ core protobuf tests with `anyall`.
  _Satisfies:_ 4.2.

## Phase 5 — SymCC analyzability, gated

- **T5.1 SymCC compiler arm for `all` (gated).**
  `Cedar/SymCC/Compiler.lean` (+ `SymCCOpt/`): compile `all` to a bounded conjunction over the
  symbolic set's elements of the compiled set-free predicate; reject predicates that contain a
  set term (5.2).
  _Green check:_ `lake build Cedar`.
  _Satisfies:_ 5.1, 5.2.

- **T5.2 SymCC soundness/completeness proofs for `all` (gated).**
  Add the `all` case across `Thm/SymCC/{Compiler,Enforcer,Verifier,Concretizer,…}`.
  _Green check:_ `lake build Cedar`.
  _Satisfies:_ 5.1 (verified), design Surface 2/SymCC.

## Phase 6 — DRT generator + differential wiring (LAST)

- **T6.1 Add the gated AST generator arm.**
  `cedar-policy-generators/src/expr.rs`: `#[cfg(feature = "anyall")]` arm generating
  `ExprKind::All` with a Set-typed receiver and a generated **set-free, non-nested** `PredExpr`
  (`arbitrary_pred_expr`). Gated on the same flag as the engines, so differential comparison
  only happens once all engines support the node.
  _Green check:_ `cargo test` and `cargo test --features integration-testing` from `cedar-drt/`
  (with and without `anyall`).
  _Satisfies:_ 3.3.

- **T6.2 Exercise eval + analyzability differentially.**
  Confirm `eval-type-directed.rs` (via `run_eval_test`, Rust vs. Lean FFI) and the `symcc-*`
  targets agree on generated `.all`/`.any` policies; optionally add an `anyall`-focused target.
  _Green check:_ DRT `cargo test` + `cargo test --features integration-testing`.
  _Satisfies:_ 2.x parity, 5.3.

## Phase 7 — Docs & open questions

- **T7.1 Document the feature, keyword `it`, and the set-free restriction; cite Mudathir (2025).**
  _Satisfies:_ US-1..US-6 traceability; records the resolved analyzability citation.

- **T7.2 Record the sets-of-sets decidability open question (OQ-1) in the design/docs.**
  Leave it explicitly out of scope and un-implemented.
  _Satisfies:_ OQ-1.

---

## Ordering rationale

1. Flags first and inert (Phase 0) → default build never changes (3.1/3.2).
2. Node + types before behavior, per surface (Phases 1–5) → each surface compiles with the new
   node before the next depends on it.
3. The DRT generator arm (Phase 6) is **last**: it is the only change that makes the Rust and
   Lean engines compare the new node against each other, so it must not be enabled until both
   engines (and SymCC) implement it — otherwise an intermediate commit would produce a
   differential failure. This is why 3.3 ("generator gated on the same flag") is a requirement,
   not just a convenience.
