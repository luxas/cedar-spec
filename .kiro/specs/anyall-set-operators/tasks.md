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

## Status overview

Live implementation status. Branch-level detail lives in `branches/<branch>/{PLAN,OUTCOMES}.md`;
decisions that may need the owner's attention are in `DECISIONS.md`.

| Phase | Branch | Status |
|---|---|---|
| 0 | `1-anyall-feature-flags` | DONE — review converged (2 rounds) |
| 1 | `phase1-anyall-rust-ast` | DONE — review converged (3 rounds) |
| 2 | `phase2-anyall-lean-spec` | DONE — review converged (2 rounds); T2.3 type rule deferred (D-11) |
| 3 | `phase3-anyall-rust-eval-validator` | DONE — review converged (1 round) |
| 4 | `phase4-anyall-surface-syntax` | DONE — review converged (1 round) |
| 5 | `phase5-anyall-symcc` | user chose full type rule + bounded quantifier (D-33); part A type rule + soundness done on WIP branch (D-50), red only in SymCC Opt until part B (D-49); part B implementing |
| 6 | `phase6-anyall-drt-differential` | DONE — review-clean (rounds 1+2; F-1..F-7 all fixed); see `branches/phase6-anyall-drt-differential/OUTCOMES.md` |
| 6.5 | `phase6_5-anyall-tpe` | not started |
| 7 | `phase7-anyall-docs` | not started |
| 8 | `phase8-anyall-benchmarks` | not started |

---

## Phase 0 — Feature flags, inert

- **T0.1 Add the `anyall` Cargo feature (off by default).**
  Add `anyall = []` to `cedar-policy-core/Cargo.toml` and propagate an optional pass-through
  feature in `cedar-policy/Cargo.toml`, `cedar-drt/Cargo.toml`, `cedar-drt/fuzz/Cargo.toml`,
  and `cedar-policy-generators/Cargo.toml`. No code paths yet.
  _Green check:_ builds unchanged with and without the flag.
  _Satisfies:_ 3.1.
  _Status:_ DONE (cedar `e40e6d8d`, `e181a796`; cedar-spec `f427ffc`, `9964ab0`, `a814b11`).

- **T0.2 Add the Lean build flag, inert.**
  Introduce the `anyall` gating mechanism in `cedar-lean/` (lakefile option / `set_option`
  or a `Cedar/Spec/Features.lean` boolean the new constructs are guarded by). No new
  constructors yet.
  _Green check:_ `lake build Cedar` unchanged.
  _Satisfies:_ 3.2.
  _Status:_ DONE (`9e35bad`). Lean has no conditional compilation, so `Features.anyAll` is documentation only; the real gate is Rust/DRT-side (D-08).

## Phase 1 — Rust AST, gated, no parser/eval yet

- **T1.1 Add the `PredExpr` / `PredExprKind` module.**
  New file `cedar-policy-core/src/ast/pred.rs`, all `#[cfg(feature = "anyall")]`; re-export
  from `ast/mod.rs`. `PredExprKind::Lit` reuses the existing `Literal` directly (already
  set-free — no wrapper type). Include smart constructors that reject `IsEmpty` and
  `Contains`/`ContainsAll`/`ContainsAny` ops and have no `Set` form.
  _Green check:_ core builds with and without `anyall`; new types only compiled under flag.
  _Satisfies:_ 1.5 (structural set-freeness), design Surface 1.
  _Status:_ DONE (cedar `f9bcc713`, `fd487f13`).

- **T1.2 Add `ExprKind::All { expr, pred }` under `#[cfg(feature = "anyall")]`.**
  Extend every exhaustive match on `ExprKind` with a flag-gated arm: `variant_order`,
  `try_type_of` (→ `Some(Type::Bool)`), `subexpressions`, `eq_shape`, `hash_shape`,
  `cmp_shape`, `substitute_general`, `try_into_expr`. Add `ExprBuilder::all` and a default
  `ExprBuilder::any` method that lowers to `self.not(self.all(expr, pred.negate()))` — the
  same layer and pattern as the existing `greatereq`/`greater` default methods (`>`/`>=` have
  no AST node; neither does `any`).
  _Green check:_ core builds + unit tests pass with and without `anyall`.
  _Satisfies:_ 2.3 (lowering at the builder layer), 4.1 (shape machinery), design Surface 1.
  _Status:_ DONE (cedar `e80f22c1`, `dff948a4`, `fd487f13`). As built, `any` is a free constructor `Expr::any`, not a trait default (D-05); the trait gains `type Pred`/`all`/`pred_from_ast` (D-04).

## Phase 2 — Lean spec node + evaluator, gated

- **T2.1 Add `PredExpr` inductive and `Error.quantifierError` (gated).**
  `Cedar/Spec/Expr.lean` + `Cedar/Spec/Value.lean`. Update the hand-written `DecidableEq`
  (`decExpr`/`decExprList`/`decProdAttrExprList`) and any `Repr`/`Inhabited` derivations and
  `sizeOf`/termination lemmas to cover the new constructors.
  _Green check:_ `lake build Cedar`.
  _Satisfies:_ 2.5/2.6 (error constructor), design Surface 2.
  _Status:_ DONE (`b58a4fd`, `ce91a4b`). `PredExpr` lives in `Expr.lean` (not `Value.lean`).

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
  _Status:_ DONE (`ce91a4b`, tests `f7239bf`: 16 tests, no-short-circuit regression verified by mutation). Implemented via `evaluatePred` (threads `it` as a full Value) rather than `PredExpr.instantiate`.

- **T2.3 Repair the structural proofs over `Expr` (gated).**
  Add the `.all` case everywhere a `Thm/` proof recurses over `Expr`: `Thm/WellTyped*`,
  `Thm/Validation/Typechecker*`, `Thm/Validation/Validator.lean`, and evaluator-soundness
  lemmas. Prove the sound type rule (req 6.1/6.4): `e : Set τ` and `pred : Bool` under `it : τ`
  ⇒ `e.all(pred) : Bool`, sound w.r.t. the evaluator.
  _Green check:_ `lake build Cedar` (all proofs).
  _Satisfies:_ 6.1, 6.4, design Surface 2.
  _Status:_ PARTIAL (`ce91a4b`). Every structural proof has its `.all` case (about 25 files, no `sorry`). The sound type rule is NOT done: the Lean `typeOf` conservatively rejects `.all` — see D-11.

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
  _Status:_ DONE (cedar `a409133e`, `911ee3ea`): instantiation via `From<Value> for Expr` (D-14); 18 parity tests.

- **T3.2 Implement the Rust validator / well-formedness checks (gated).**
  Implement the type rule for `All` (req 6.1–6.3: `E : Set<τ>`, `P : Bool` under `it : τ` ⇒
  `Bool`; reject non-set receiver / non-Bool predicate; defer to existing element-type handling
  for unknown `τ`); reject nested quantifiers (1.4), set-containing predicates (1.5), and `it`
  outside a predicate (1.6), in `Expr::try_validate` and the validator.
  _Green check:_ core tests with `--features anyall`.
  _Satisfies:_ 1.4, 1.5, 1.6, 6.1, 6.2, 6.3.
  _Status:_ DONE for 1.5/6.1-6.3 (cedar `78c79bc5`, `05adec3d`); 1.4/1.6 are unrepresentable in the AST and enforced by the Phase 4 parser (D-20).

## Phase 4 — Rust surface syntax + roundtrip, gated

- **T4.1 Parser: CST→AST for `.all( … )` / `.any( … )` and the `it` keyword (gated).**
  Add the access-form production and bind `it` → `PredExprKind::Item`; the production **calls
  `builder.all(..)` / `builder.any(..)`** (the builder does the `any`→`!all(!p)` lowering, as
  the relational arm calls `builder.greatereq(..)` at `cst_to_ast.rs:2321`). The parser does
  not construct the negation itself.
  Keep `it` an ordinary identifier when the flag is off (1.3).
  _Green check:_ core parser tests with and without `anyall`.
  _Satisfies:_ 1.1, 1.2, 1.3, 2.3.
  _Status:_ DONE (cedar `0ee7bc97`). As built, the parser lowers `.any` itself via `not` + `all` (the builder trait has no `any`, D-05); `it` is not reserved but a bare-value `it` lowers to `item()` and a stray `it` is rejected (D-26). 15 parser tests + 2 off-build tests.

- **T4.2 EST (JSON) + `Display` pretty-printer (gated).**
  Add an EST `All { expr, pred }` form whose `pred` is a **full `Expr`** (EST stays simple — no
  restricted predicate type for now; nesting is rejected at EST→AST). Extend `est::Builder` so
  AST→EST stays lossless/infallible; emit `expr.all(pred)` (and `any` as its lowered
  `!expr.all(!pred)`). AST↔EST↔text roundtrip tests. ⚠️ Flagged: a restricted `est::PredExpr`
  (structural non-nesting at EST) is a possible future tightening.
  _Green check:_ core roundtrip tests with `anyall`.
  _Satisfies:_ 4.1, 4.3.
  _Status:_ DONE (cedar `408ced71`): EST `all`/`it` nodes, PST `All` (D-30); Display prints `.any` lowered (D-28).

- **T4.3 Protobuf schema + round-trip (gated).**
  Add the `All` message to the protobuf schema and the encode/decode mapping; round-trip test.
  _Green check:_ core protobuf tests with `anyall`.
  _Satisfies:_ 4.2.
  _Status:_ DONE (cedar `23056938`): fields 17 `All`, 18 `Item`; decode re-checks the predicate (D-27). Lean decoder deferred to Phase 6 (D-29). Note: proto lives in `cedar-policy`, not core.

## Phase 5 — SymCC analyzability, gated

**Status (2026-10-09, Phase 5B): DONE — review-clean (round 2: NO ACTIONABLE FINDINGS).**
D-74 remains OPEN but ships behind the D-74-interim (`SymCCSupported(.all)=false`); if deferred,
Phase 9 carries D-70 option B **and** D-74 option A. Residual follow-ups D-78/D-79 (LOW) tracked.
M1–M4 of SymCC `.all` support are DONE — `compile`,
`compile_interpret_on_footprint`, `compile_evaluate`, and the footprint (`footprintAllPred`,
D-71) all handle `.all` with proofs (axioms = the three standard ones; see run notes). The
`compile_well_typed` (well-typed ⇒ compiles) dispatcher `compilePred_well_typed` is DONE
(all 13 arms, 0 sorry, axioms `[propext, Classical.choice, Quot.sound]`). Its `.all`
assembly is BLOCKED on **D-74 (OPEN)** — `normalize_evaluatePred` needs predicate type
soundness, which does not yet exist. **D-74-interim** (committed): `TypedExpr.SymCCSupported
(.all _ _ _) := false` so the `well-typed ⇒ compiles` fragment temporarily excludes `.all`
and `compile_well_typed_on_wf_expr`'s `.all` arm closes by contradiction — this keeps every
theorem true while D-74 is decided (restore the real guard + arm under option A or C').
CedarFFI `ToJson` now serializes the anyall nodes (`Op.set.all`, `PredExpr`).
**D-77 (SETTLED, option b) — DONE:** the `SymCCSupported` guard is threaded into the SymCC
verifier COMPLETENESS lane only. `compile_ok_iff_welltypedpolicy[ies]_ok` is split into the
UNGUARDED `.mp` (`compile_ok_implies_welltypedpolicy[ies]_ok`, soundness) and a GUARDED
biconditional; every `verify*_is_ok` caller and `*Opt?_eqv_*?` / `check*_eqv_*` (and their
`_ok`) theorem now carries a `PolicySymCCSupported`/`PoliciesSymCCSupported` hypothesis.
Soundness-lane theorems stay unguarded. **Full tree is GREEN** (782 jobs; Cedar, SymCC,
SymTest, UnitTest, DiffTest, Protobuf, CedarProto), 0 sorry; the DRT FFI static-lib target
(`lake build Cedar:static Protobuf:static CedarProto:static Cedar.SymCC:static CedarFFI:static
Batteries:static`) builds and archives `libCedar_CedarFFI.a` (1079 jobs). Guarded top-level
verifier theorems' axioms = `[propext, Classical.choice, Quot.sound]` (no sorryAx). The
`CedarSymTests` executable **links and runs** here with the documented env
`LIBRARY_PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/lib:$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean`
and `CVC5` set (D-13 host quirk): **1216/1216 success, 0 failure** (AnyAll.e2e 12/12, incl. the
F4 overflow error-path and `.any`-lowering cases). `.all` COMPLETENESS of `compile_well_typed`
remains the only narrowed piece, behind the D-74-interim, pending D-74 (option A or C').

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

> **Status: DONE — review-clean.** All W1–W8 landed; blind review rounds 1 and 2 converged
> (findings F-1..F-7 all fixed). See `branches/phase6-anyall-drt-differential/OUTCOMES.md` for
> per-item commits (nested cedar @ `d34291f8`; cedar-spec head = the OUTCOMES/tasks doc commit),
> ~6% non-vacuity, ~183k fuzz executions (0 mismatch), the F-4 HO_ALL fix + cvc5 proof, the F-6
> deterministic footprint tests, and the Phase 9 carry (D-70 option B, D-74 honest normalization,
> D-78 logic-narrowing, solved-symbolic-`set.all` coverage metric). D-31 FIXED (W1).

- **T6.1 Add the gated AST generator arm.**
  `cedar-policy-generators/src/expr.rs`: `#[cfg(feature = "anyall")]` arm generating
  `ExprKind::All` with a Set-typed receiver and a generated **set-free, non-nested** `PredExpr`
  (`arbitrary_pred_expr`). Gated on the same flag as the engines, so differential comparison
  only happens once all engines support the node. **Also generate the `.any` shape:** because
  `.any` has no node and lowers to `!all(!p)`, a generator that only emits `All` never exercises
  `.any`. The arm MUST sometimes emit the lowered `!all(!p)` form (equivalently, call
  `builder.any(..)`) so the `.any` surface and its lowering identity are actually produced — not
  just assumed. The element type is varied over primitives, entities, and **records** (per the
  B1 instantiation fix: elements are `Value`s, not just literals).
  _Green check:_ `cargo test` and `cargo test --features integration-testing` from `cedar-drt/`
  (with and without `anyall`).
  _Satisfies:_ 3.3, 2.3 (`.any` lowering exercised).

- **T6.2 Exercise eval + analyzability differentially — `.all` AND `.any`.**
  Confirm `eval-type-directed.rs` (via `run_eval_test`, Rust vs. Lean FFI) and the `symcc-*`
  targets agree on generated `.all` policies **and on the `.any`/`!all(!p)` shape from T6.1**, so
  `.any` semantics (req 2.3) and record-valued elements (B1) are covered, not merely assumed.
  Include a targeted differential case: a set with a record element whose predicate reads an
  attribute of `it`.
  _Green check:_ DRT `cargo test` + `cargo test --features integration-testing`.
  _Satisfies:_ 2.1, 2.2, 2.3, 2.5, 2.7, 2.8 (parity), 5.3.

## Phase 6.5 — Typed partial evaluation (late commit)

- **T6.5.1 TPE residual node + concrete-receiver evaluation (gated).**
  Add `ResidualKind::All { expr, pred }` in `cedar-policy-core/src/tpe/residual.rs` and the
  `Residual::from_expr` arm. In `tpe/evaluator.rs`, evaluate `All` when the receiver reduces to
  a `Concrete` set: instantiate `pred` per element `Value` (§3 Value-instantiation, incl. record
  elements), fold with the no-short-circuit QuantifierError semantics (2.8), and return
  `Concrete(bool)` / `QuantifierError`.
  _Green check:_ core tests with `--features anyall`; parity vs. the concrete evaluator on
  concrete-receiver cases.
  _Satisfies:_ 7.1, 7.3.

- **T6.5.2 Residual-receiver passthrough + soundness (gated).**
  When the receiver is `Partial`, produce a residual `All` rather than erroring; preserve the
  TPE soundness invariant (residual re-evaluated on remaining input agrees with full eval). Add
  the Lean TPE/residual `all` arm + soundness lemma if the spec's TPE is modeled in `cedar-lean`.
  Runs LATE — a conservative "always residualize non-trivial `All`" is an acceptable first cut.
  _Green check:_ `lake build Cedar` (if Lean TPE touched) + core tests with `--features anyall`;
  confirm non-`anyall` TPE behavior is byte-unchanged (3.1).
  _Satisfies:_ 7.2, 7.4.

## Phase 7 — Docs & open questions

- **T7.1 Document the feature, keyword `it`, and the set-free restriction; cite Mohamed et al. (FMCAD 2025).**
  _Satisfies:_ US-1..US-6 traceability; records the resolved analyzability citation.

- **T7.2 Record the sets-of-sets decidability open question (OQ-1) in the design/docs.**
  Leave it explicitly out of scope and un-implemented.
  _Satisfies:_ OQ-1.

## Phase 8 — cvc5 runtime benchmarks (LAST — empirical analyzability characterization)

Motivation: RFC 0021 explicitly flagged that these operators "will likely have a negative
impact on analysis performance," and Mohamed et al. (FMCAD 2025) measured exactly this — solver
scaling of the filter/bounded-quantifier encoding. Decidability guarantees termination, not
tractability; this phase measures how cvc5 actually behaves on `.all`/`.any` policies in
practice. It runs LAST because it needs the whole feature (SymCC compilation of `all`, Phase 5)
working end-to-end.

cvc5 is invoked via `LocalSolver` in `cedar-drt/fuzz/src/symcc.rs` (binary from the `CVC5` env
var, 1 GB memory cap, tokio `timeout`). The measurable queries are the existing SymCC check
verbs: `check-always-allows`, `check-always-denies`, `check-equivalent`, `check-implies`,
`check-disjoint`, `check-never-errors`. The benchmark compiles `.all`/`.any` policies to SMT and
times cvc5 on each verb.

- **T8.1 Benchmark harness (new, gated).**
  Add an `anyall`-gated benchmark binary/target under `cedar-drt/` (e.g.
  `cedar-drt/benches/anyall_symcc.rs` or an `--anyall-bench` mode of the fuzz manager). It
  generates `.all`/`.any` policies parameterized by the dimensions below, compiles them through
  SymCC, invokes cvc5 per check verb, and records wall-clock solve time, cvc5 exit status
  (sat/unsat/unknown/timeout/oom), and SMT term size. Emit CSV/JSON for plotting. Use a fixed
  per-query `timeout` and the same 1 GB memory cap as the DRT harness so results are comparable;
  record `unknown`/`timeout`/`oom` as first-class outcomes, not failures. Keep it OUT of the
  default `cargo test` path (own target, `bench = false` elsewhere) so CI time is unaffected.
  _Satisfies:_ 5.4, RFC 0021 performance drawback.

- **T8.2 Dimensions to sweep (each varied independently against a fixed baseline).**
  1. **Set size** — bound/cardinality of the quantified set (e.g. 1, 2, 4, 8, 16, 32, 64, …):
     the primary scaling axis, since `all` compiles to a bounded conjunction over elements.
  2. **Predicate complexity** — predicate AST depth / number of operators (a bare `it == k`
     vs. nested `&&`/`||`/`if` chains vs. `like`/`is`/attribute access), still set-free.
  3. **Element type** — `Long` (LIA), `String`, `Bool`, `EntityUID`, and record elements with
     attribute access in the predicate; element theory is Condition 2 of the paper and affects
     solver difficulty.
  4. **Number of quantifiers per policy** — 1 vs. several *sibling* (non-nested) `.all`/`.any`
     conjoined, to see additive vs. super-additive cost (nesting stays excluded — not a
     dimension).
  5. **Check verb** — all six SymCC verbs above; equivalence/implication (two policies) are
     typically harder than always-allows/denies (one).
  6. **`.all` vs `.any`** — confirm the `!all(!p)` lowering carries no surprising asymmetry.
  7. **SAT vs UNSAT shape** — satisfiable (counterexample-bearing) vs. unsatisfiable queries,
     which cvc5 handles very differently (mirrors the paper's sat/unsat split).
  _Satisfies:_ 5.4.

- **T8.3 Report + regression guardrail.**
  Produce a short results doc (table + cactus-style plot of instances solved under a time
  budget, as in the paper's Fig. 3) under `.kiro/specs/anyall-set-operators/` or
  `cedar-drt/benches/README`. Call out where cvc5 falls off a cliff (timeouts/unknowns) and at
  what set size, so the feature's practical envelope is documented. OPTIONAL: a loose CI
  smoke-bench at one small size with a generous timeout to catch gross regressions, kept off the
  default path.
  _Satisfies:_ 5.4 (documents the practical analyzability envelope).


## Phase 9 — Enforcer set-footprint extension (D-70 option B) — PLANNED-LATER (not in current stack)

Follow-up to D-70 (RESOLVED 2026-10-09: option A shipped in Phase 5B; option B deferred to here).
The user placed this at **Phase 9**, the very end of the stack, AFTER Phase 8 benchmarks. This is now
the concrete meaning of "Phase 9" — superseding the historical "phase 9 = end of the branch stack"
reading in D-01 (there is no separate abstract Phase 9; this is it).

Phase 5B option A keeps the quantifier footprint `it`-free by having `compile` reject `.all`
predicates that apply `in` (the ancestors UF) to an `it`-dependent left operand. Phase 9 lifts that
restriction by extending the Enforcer with SET-TYPED footprint entries (the receiver set itself),
grounding the hierarchy assumptions via `set.filter` instead of only over finitely-many named entity
Terms, and extending `SameOn` to grant ancestor agreement over the filtered set. Scope: acyclicity for
a set entry is one `set.filter`; element-vs-footprint-term transitivity is one `set.filter`;
element-vs-element transitivity is a `set.filter` NESTED over the same set — whose SMT decidability
(does cvc5's `ALL`/`set.filter` fragment stay decidable under the nested quantifier?) is the open
question this phase must settle before committing to the encoding. Status: PLANNED-LATER.
_See:_ `branches/phase9-anyall-set-footprint/PLAN.md`, DECISIONS.md D-70.

---

1. Flags first and inert (Phase 0) → default build never changes (3.1/3.2).
2. Node + types before behavior, per surface (Phases 1–5) → each surface compiles with the new
   node before the next depends on it.
3. The DRT generator arm (Phase 6) is **last**: it is the only change that makes the Rust and
   Lean engines compare the new node against each other, so it must not be enabled until both
   engines (and SymCC) implement it — otherwise an intermediate commit would produce a
   differential failure. This is why 3.3 ("generator gated on the same flag") is a requirement,
   not just a convenience.
4. Benchmarks (Phase 8) run **after everything else**: they need the full SymCC pipeline
   (Phase 5) and the generator (Phase 6) to produce and solve real `.all`/`.any` queries. They
   measure tractability (how cvc5 scales), which decidability alone does not promise, and are
   kept off the default `cargo test` path so they never gate a commit's green check.
5. Typed partial evaluation (Phase 6.5) is sequenced **late**: it needs the Value-instantiation
   evaluator (Phase 2/3) and reuses it for concrete receivers. Until it lands, the TPE `All` arm
   may conservatively residualize, and the non-`anyall` default build is unaffected (3.1), so
   deferring it never blocks an earlier green commit.
