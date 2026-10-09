# Phase 6.5 Outcomes — TPE of `.all` / `.any` (`phase6.5-anyall-tpe`)

Scope: cedar repo (`cedar-policy-core/src/tpe`); cedar-spec only docs. Satisfies reqs
7.1 / 7.2 / 7.3 / 7.4; closes the open **D-32** stray-`it` NIT. Decisions **D-80/D-81/D-82**.

## Commits

| Repo | SHA | What |
|---|---|---|
| cedar | `71c6912` | W1–W4 — `ResidualKind::All`, concrete-receiver fold, residual passthrough, central stray-`it` backstop; 12 anyall-gated tests; mutation-verified |
| cedar-spec | _(this commit)_ | DECISIONS D-80/D-81/D-82; tasks.md Phase 6.5 status; this OUTCOMES.md |

(Branches cut off `phase6-anyall-drt-differential`; cedar `826cc339`, cedar-spec `d923c63`.
Rebase onto Phase 6's final tip before merge.)

## As built
- **W1 node (`residual.rs`):** `ResidualKind::All { expr: Arc<Residual>, pred: Arc<PredExpr> }`.
  `try_from_typed_expr` translates `ExprKind::All` (receiver residualized; predicate stored
  raw via `with_default_data`, since predicates carry no `Unknown`/`Slot`, D-18). Extended
  `all_literal_uids` (receiver uids ∪ new `pred_literal_uids` walk, mirroring Lean
  `PredExpr.litUIDs`), `can_error_assuming_well_formed` (`.all` ⇒ `true`: QuantifierError is a
  genuine runtime-error source), and `From<Residual> for Expr` (rebuilds `Expr::all` for
  re-authorization).
- **W2 concrete fold (`evaluator.rs`, D-80 option A):** when the receiver interprets to a
  `Concrete` set, instantiate the predicate per element and interpret each via a new
  `Residual::from_untyped_expr` (assigns the quantifier's own placeholder `Type` to the
  ephemeral per-element residual — the fold inspects only booleans/errors/residual-ness, so the
  exact type is irrelevant). Semantics mirror the Phase-3 concrete `.all` arm exactly: non-set
  receiver ⇒ error; any erroring/non-bool element ⇒ QuantifierError image (`mk_error`); **no
  short-circuit on a `false` element** (reqs 2.5/2.8); empty set ⇒ `true`; record elements
  supported (B1).
- **W3 passthrough (reqs 7.2/7.4):** a residual receiver keeps the whole `.all` node (receiver
  partially evaluated). A concrete receiver whose per-element predicate stays residual (reads an
  unknown request attribute) conservatively keeps the whole node with the receiver rebuilt from
  its concrete value (D-80). The full per-element-residual refinement (keep only undecided
  elements while preserving 2.8/QuantifierError — needs a new residual shape) is deferred to
  Phase 9.
- **W4 stray-`it` backstop (closes D-32):** `try_from_typed_expr` rejects a stray `IT_SENTINEL`
  reaching TPE outside a predicate with a dedicated `StrayItError`, agreeing with the parser's
  `reject_stray_it` (req 1.6) through the shared `ast::is_it_sentinel`. (Replaced the Phase-1
  `AllNotSupportedError` placeholder, now dead.)
- **Lean (D-81):** unchanged. The Lean TPE `.all` arm already residualizes conservatively and is
  already proved sound (`Thm/TPE/Soundness.lean`, D-48). Rust/Lean parity is **"the
  re-authorized residual agrees with full evaluation on the completed input"**, not shape-equal.
- **DRT (D-82):** no new TPE differential harness; TPE is covered by in-crate parity tests (no
  TPE target exists in `cedar-drt`).

## Verification
- **Counts:** `tpe::` suite **93 (non-anyall) → 105 (`tpe,anyall`)**, +12 anyall-gated tests, 0
  failures. Non-anyall count is byte-unchanged before/after (confirmed by stashing the change),
  so the default build is unaffected (reqs 3.1/7.4). (The PLAN's "91" was a `#[test]`-attribute
  grep; the runtime filter `tpe::` counts 93 — the +12 delta is what matters.)
- **Core `cargo check --tests`:** default / `anyall` / `anyall,tolerant-ast` / `experimental` /
  `all-features` — all clean.
- **cedar-policy `cargo check --tests`:** default / `experimental` / `protobufs` /
  `protobufs,anyall` / `all-features` — all clean.
- **`cargo clippy --all-features --lib`** (core): no new warnings from `tpe/` (13 pre-existing
  warnings elsewhere, none in changed files).
- **`cargo test -p cedar-policy-core --features tpe,anyall tpe::`** = 105 passed.

## Mutation checks (each caught by a named test, then reverted)
| Mutation | Test(s) broken |
|---|---|
| empty-set / all-true fold init flipped to `false` | `concrete_all_empty_is_true`, `concrete_all_true` (+3) |
| erroring element folds to `false` (short-circuit) | `false_then_error_is_quantifier_error_not_false` (printed `false` instead of `error()`) |
| stray-`it` guard disabled | `stray_it_is_rejected_by_tpe_backstop` (fell through to `UnknownNotSupported`) |

## What a blind reviewer must verify
1. Non-`anyall` `tpe` suite byte-unchanged (93); no `ResidualKind::All`/`All` reachable without
   the flag.
2. Concrete-receiver parity is semantic (matches the concrete evaluator), incl. the
   false-then-error ⇒ Error case (2.8) and record elements (B1); parity tests run (count>0) and
   break under the fold mutations.
3. Residual receiver ⇒ node retained (7.2); the test exercises a genuinely unknown receiver.
4. D-80: a concrete receiver + unknown-reading predicate keeps the whole node residual
   (`concrete_receiver_residual_predicate_keeps_node`).
5. Stray-`it` backstop does not loosen the parser's entry checks and does not reject legitimate
   `it`-named attrs/keys (D-26).

## Follow-ups (Phase 9)
- Full req-7.3 per-element-residual refinement: a TPE residual shape that keeps only the
  undecided elements of a concrete-receiver `.all` while preserving the 2.8 no-short-circuit +
  QuantifierError semantics (D-80).
- Optional Lean concrete-fold parity (D-81), if shape-level Rust/Lean parity is wanted.
- Optional DRT TPE differential (D-82), comparing "re-authorized residual agrees".

## Review loop
| Round | Agent | Verdict |
|---|---|---|
| _pending_ | — | awaiting independent blind review |
