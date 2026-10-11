# Phase 9 — `.all`/`.any` completion — PLAN (`phase9-anyall-completion`)

> **Status: PLAN only** (plan agent, 2026-10-11). This is the final phase of the
> `anyall-set-operators` feature: it lands the five items the earlier phases deferred —
> **D-74 option A** (predicate type soundness + wiring the honest `normalize`), **D-70 option B**
> (Enforcer set-typed footprints so `it`-dependent `in` is supported), **req 7.3** (per-element
> residual refinement in Rust TPE, D-80), **D-78** (gate `HO_ALL` on a `set.all` term), and
> **D-79** (fold `PredExpr.normalize`'s constant-`ite` once instead of duplicating). It subsumes
> the earlier stub `branches/phase9-anyall-set-footprint/PLAN.md` (D-70 B only); that file is left
> as a pointer.
>
> **Branches.** cedar-spec `phase9-anyall-completion` cut from `phase8-anyall-cvc5-benchmarks`
> (HEAD = Phase 8 tip). Nested cedar `phase9-anyall-completion` cut from `phase7-anyall-docs`
> (Phase 8 changed nothing in the Rust tree). The Lean build cache is seeded in `cedar-lean/.lake`.
> Both repos share the branch name, as every prior phase did.

---

## 0. Where the feature stands going into Phase 9

Phases 0–8 shipped `.all`/`.any` end-to-end, flag-gated and inert by default, with one honest
narrowing: SymCC **soundness** for `.all` is fully proven and axiom-clean (`compile`,
`compile_interpret_on_footprint`, `compile_evaluate`, the footprint, the Part-A type-soundness
`type_of_all_is_sound`), but two things are deferred:

1. **SymCC completeness for `.all` is guarded out** behind the **D-74-interim**
   (`TypedExpr.SymCCSupported (.all _ _ _) := false`) and **D-77** (the guard is threaded only
   into the verifier completeness lane). `PredExpr.normalize` and the 13-arm dispatcher
   `compilePred_well_typed` are landed but **inert** — `typeOfAll` stores the *source* predicate,
   not `normalize p₀`, so the dispatcher's `compilePred (normalize p₀)` conclusion does not line
   up with what `compile`'s `.all` arm actually compiles. Closing this is **D-74** (recommended
   option A), which needs a predicate **type-soundness** theorem that does not exist yet.
2. **An `it`-dependent `in` inside a predicate is rejected** by `compile` with `.unsupportedError`
   (**D-70 option A**), because the quantifier footprint is kept `it`-free (a symbolic receiver's
   element UIDs cannot be named by finitely many footprint Terms). Lifting this is **D-70 option B**
   — set-typed footprint entries grounded via `set.filter`.

Rust TPE folds `.all` concretely only when the receiver *and every per-element instantiation* are
concrete; a concrete receiver with any residual-predicate element conservatively keeps the whole
node (D-80). **req 7.3**'s full per-element refinement is the remaining TPE item.

Everything below is additive to a green tree; nothing here changes the default (non-`anyall`) build.

---

## 1. Recommended branch split (stacked sub-branches)

Phase 9 is large and heterogeneous: a multi-day Lean soundness proof, an SMT encoding whose
decidability question is now **settled go** (§4), independent Rust TPE work, and two small
follow-ups. The Phase-5B lesson (parallel worktrees for independent lemma files; rotate long
worker conversations) applies. Recommended split into **four stacked sub-branches**, ordered to
land the independent/small items first and keep the long proof off the critical path of the others:

| Order | Sub-branch | Items | Size | Depends on | Worktree |
|---|---|---|---|---|---|
| 1 | `phase9a-anyall-ho-all-logic` | **D-78** | XS (~0.5 day) | none (independent of all others) | own, cut from Phase 8 tip |
| 2 | `phase9b-anyall-tpe-refinement` | **req 7.3 / D-80 full** | M (~2–3 days, Rust only) | none (nested cedar only; independent of Lean) | own, nested cedar |
| 3 | `phase9c-anyall-pred-type-soundness` | **D-74 A** (`type_of_pred_is_sound`, `normalize_evaluatePred`, wire `normalize`, restore the real `compile_well_typed` `.all` arm) **+ D-79** | **L–XL (multi-day, the critical path)** | none to *start*, but is the longest; D-79's fold needs D-74 A's soundness | own, Lean-heavy; split lemma files across parallel worktrees |
| 4 | `phase9d-anyall-set-footprint` | **D-70 B** (set-typed footprint entries, `SameOn` extension, drop the option-A `in` guard, Rust mirror) | **L (multi-day)** | **D-74 A** landed (it removes the D-74-interim; D-70 B must restore the *real* `compile_well_typed` `.all` arm **without** the `in` guard, which only exists once D-74 A has wired `normalize`) | own, Lean + nested cedar |

**Rationale for the order and the dependency edges.**

- **9a (D-78) and 9b (D-80/7.3) are fully independent** of each other and of the two Lean-proof
  branches — 9a touches only `Encoder.lean`'s logic-selection line; 9b touches only
  `cedar-policy-core/src/tpe`. Land them first so the small/medium wins are not gated behind the
  multi-day proof. They can run in parallel worktrees from the start.
- **9c (D-74 A) is the critical path** and should start in parallel immediately (its own worktree)
  because it is the longest. D-79's constant-`ite` fold is folded into 9c because it is only
  *correct* once `normalize_evaluatePred` (a D-74 A deliverable) proves the fold preserves
  evaluation — doing D-79 anywhere else would duplicate that dependency.
- **9d (D-70 B) must be stacked on top of 9c.** D-70 B's whole point is to make an `it`-dependent
  `in` *supported*, which means removing the option-A `in`-rejection guard from `compile`'s `.all`
  arm **and** restoring the real (`SymCCSupported`-based) completeness arm — but that arm only
  exists once D-74 A has wired `normalize` and lifted the D-74-interim. Building 9d on the interim
  would mean writing the footprint proofs against a `.all` that is still completeness-excluded,
  then redoing them. Cut 9d from 9c's final tip.

Merge order is bottom-up: 9a, 9b, then 9c, then 9d. 9a/9b can merge as soon as reviewed (they do
not touch 9c/9d). Expect the recurring **DECISIONS.md / tasks.md rebase conflicts** when 9c and 9d
rebase onto a moved base — the standing resolution (keep the HEAD block, append only the branch's
new D-rows, `rebase --onto` to replay a phase's own commits) applies; see the learned-corrections
note on D-74/D-75/D-76-style row merges.

Each sub-branch gets its own `PLAN.md` section/file with milestones, the green bar, non-vacuity
evidence, and deterministic mutation checks, following the Phase-5B pattern. §2–§6 below are the
per-sub-branch plans.

---

## 2. `phase9a-anyall-ho-all-logic` — D-78 (gate `HO_ALL` on a `set.all` term)

**Problem.** `Encoder.lean`'s `encode` sets `Solver.setLogic "HO_ALL"` **unconditionally** for
every SymCC query. `HO_ALL` is a strict superset of the first-order logic the non-`.all` queries
need, so this is *sound* (the whole regression suite passes under `HO_ALL`) but needlessly widens
the logic for every existing query — a measured LOW follow-up (D-78, reviewer F6, Phase 5B).

**Design.**
- Add a `Term.containsSetAll : Term → Bool` (structural, mirroring `Term.mentionsAnyAllIt`'s walk:
  `true` on any `.app Op.set.all _ _`, recurse into children otherwise).
- In `encode`, compute `needsHO := ts.any (·.containsSetAll)` over the asserted terms and call
  `Solver.setLogic (if needsHO then "HO_ALL" else "ALL")` — restoring the previous first-order logic
  (`ALL`, whatever the pre-`.all` encoder used; confirm the exact prior literal from git blame on
  the `setLogic` line before Phase 5B) when no `set.all` is present.
- The **Rust encoder must byte-match** (D-36): make the identical change in the Rust
  `cedar-policy-symcc` encoder's logic-selection, or the `symcc-*` DRT differential breaks.

**Green bar.** `lake build Cedar SymCC SymTest`; `CedarSymTests` 1216/1216 unchanged; a `.all`
query still emits `(set-logic HO_ALL)` and a non-`.all` query emits the first-order logic.
Rust side: the `symcc-*` differential still byte-matches (run the eval/symcc fuzzers).

**Non-vacuity + mutation.** A deterministic unit check: encode one `.all` policy and one `.all`-free
policy, assert the emitted `(set-logic …)` line differs (`HO_ALL` vs `ALL`). Mutation: force
`needsHO := true` always ⇒ the `.all`-free assertion fails; force `needsHO := false` always ⇒ a
`.all` query fails to parse under `ALL` (the Phase-5B evidence that `set.filter` parse-errors under
`ALL`), caught by `CedarSymTests`.

**Size.** XS. One encoder predicate + one call-site change per engine + one unit test per engine.

**Implementation decisions (recorded during 9a).**
- **D-P9a-1.** `Term.containsSetAll` is a `public` def in the `Cedar.SymCC` namespace (not inside
  `Encoder`), so dot-projection resolves from both `encode` and `SymTest`. `encode` calls it as
  `ts.any (fun t => Term.containsSetAll t)` (the `mentionsAnyAllIt` idiom), not `(·.containsSetAll)`.
- **D-P9a-2.** The Rust `Op::SetAll` match arm in `Term::contains_set_all` is `#[cfg(feature =
  "anyall")]`-gated (the variant only exists under `anyall`); without the feature no term can carry a
  `set.all`, so every `App` recurses and `logic_for` always yields `ALL` — which is exactly the
  pre-`.all` behavior and byte-matches Lean (whose inert `.all` code never produces a `set.all` node
  in the default build). The logic selection is factored into a private `fn logic_for(&Asserts) ->
  &'static str` used at both `set_logic` call sites in `symcc.rs`.
- **D-P9a-3.** The per-engine deterministic logic-selection check is a **build-time** check (Lean
  `#eval`/`#guard` in `SymTest/AnyAll.lean`; Rust `#[cfg(test)]` unit test), NOT a runtime
  `CedarSymTests` case, so the 1216 `CedarSymTests` count is preserved as the green bar requires.
- **D-P9a-4.** The DRT `symcc-smt-script-drt` differential initially flagged a real
  Lean-emits-`HO_ALL`/Rust-emits-`ALL` mismatch because the Lean FFI static lib
  (`libCedar_CedarFFI.a`) was stale; rebuilding it via `cedar-drt/build_lean_lib.sh` (plus forcing
  the `Cedar.SymCC.Encoder:c.o` native recompile) made both engines byte-match. Any later consumer
  of the Lean side must rebuild the FFI lib after an `Encoder.lean` change.

---

## 3. `phase9b-anyall-tpe-refinement` — req 7.3 / D-80 full per-element residual refinement

**Problem.** Today (D-80, Phase 6.5) Rust TPE folds `.all` concretely only when the receiver is a
`Concrete` set **and every** per-element instantiation evaluates to a concrete value; if *any*
element's predicate stays residual (reads an unknown request attribute), TPE conservatively keeps
the **whole** node (`ResidualKind::All { expr: concrete-set, pred }`). req 7.3 asks for *per-element*
refinement: keep only the still-undecided elements, having already discharged the decided ones,
**while preserving** the 2.8 no-short-circuit + deterministic-QuantifierError semantics.

**Why it needs a new residual shape (the Phase-6.5 note).** A refined residual must represent
"these concrete elements are decided (some `true`, some `false`), these elements are still
undecided, and an error on *any* undecided element still outranks the decided `false`s". The
current `ResidualKind::All { expr, pred }` cannot say that — it only carries a receiver + one
predicate.

**Design (option B of D-80, which D-80 explicitly flagged as the reversal/refinement path).**
- Add a residual shape that carries the partial fold state. Recommended:
  `ResidualKind::AllPartial { decided_false: bool, pending: Arc<[Residual]> }` where `pending` is
  the list of per-element predicate residuals for the elements not yet decided, and `decided_false`
  records whether some element already evaluated to a concrete `false` (so the final value is
  `false` *iff* no pending element errors — else QuantifierError). An empty `pending` collapses to
  `Concrete(!decided_false)` (fold complete); the all-`true` case has `decided_false=false` and
  empty `pending` ⇒ `Concrete(true)`.
  - *Alternative considered:* reuse `ResidualKind::All` with a filtered receiver value. Rejected —
    it cannot carry `decided_false`, so it would lose the "a `false` is already pinned" fact and
    could let re-authorization wrongly short-circuit.
- `tpe/evaluator.rs` `.all` arm: when the receiver is `Concrete`, fold element-by-element —
  concrete-`true` elements drop; a concrete-`false` sets `decided_false`; a concrete error ⇒ the
  node collapses to `mk_error()` immediately (an error is the whole result, 2.5/2.8); a residual
  element's predicate residual is pushed to `pending`. If `pending` is empty, collapse per above;
  else emit `AllPartial`.
- `From<Residual> for Expr` / re-authorization: an `AllPartial` re-expands to a conjunction over
  the pending element predicates **and** the pinned `decided_false`, preserving no-short-circuit
  (do not `&&`-short-circuit past a pending element that could error). The re-authorized residual,
  evaluated on completed input, must agree with full evaluation — the TPE soundness invariant.
- **Lean side stays conservative (D-81):** no Lean refinement. Parity is defined as "the
  re-authorized residual agrees with full evaluation on the completed input", not shape-equality,
  so a more-reduced Rust residual that re-evaluates to the same value is sound. (Only revisit the
  Lean arm if shape-level parity is later wanted.)

**Green bar.** `cargo test -p cedar-policy-core --features tpe,anyall --lib` (whole lib + `tpe::`
filter, counts up); default/`anyall`/`all-features` `cargo check --tests` clean; non-`anyall`
`tpe::` count **byte-unchanged** (req 3.1); clippy clean.

**Non-vacuity + mutation.** New in-crate parity tests (D-82, no new DRT harness):
`concrete_receiver_mixed_elements_refines` (a concrete set with some decided-`true`, one
decided-`false`, one unknown-reading element ⇒ `AllPartial{decided_false:true, pending:[one]}`,
re-authorized against full eval over several completions **including an error-on-the-pending-element
completion** so the QuantifierError outranks the pinned `false`). Mutations, each caught by a named
deterministic test: (a) drop `decided_false` ⇒ a completion that errors the pending element wrongly
yields `false`; (b) short-circuit past a pending element ⇒ the error-after-false completion yields
`false`; (c) collapse `AllPartial` with non-empty `pending` to `Concrete` ⇒ re-authorization parity
fails.

**Size.** M (~2–3 days). Rust only; independent of every Lean branch.

### 3.1 Decisions taken while implementing 9b (`D-P9b-*`)

- **D-P9b-1 — `AllPartial` re-expansion is `[<pending bools>, <!decided_false>].all(it)`.**
  `From<Residual> for Expr` re-expands an `AllPartial` into a literal set of the pending
  element booleans plus a `!decided_false` marker element, quantified by the identity predicate
  `it`, rather than a hand-built non-short-circuiting conjunction. Rationale: `Expr::all` is the
  *one* operator whose no-short-circuit + deterministic-`QuantifierError` semantics are already
  the spec and already proven (reqs 2.5/2.8), so re-authorization parity is inherited rather than
  re-derived; a `&&` chain would short-circuit on the pinned `false` and lose the "a pending
  element may still error" guarantee (the very thing D-92 requires). Eager set-literal evaluation
  makes a pending-element error surface as a (kind-free, D-80) evaluation error before the
  quantifier runs, which matches the full `.all`'s `QuantifierError` under the parity definition
  "same value or both error" (D-81). Set-literal dedup of the booleans does not change the
  conjunction result because every element is evaluated before dedup.
- **D-P9b-2 — idempotent `AllPartial` re-interpret arm.** `Evaluator::interpret` handles a
  received `AllPartial` by re-interpreting each pending element (an unknown it reads may now be
  known), applying the same per-element fold and collapsing to `Concrete(!decided_false)` when
  `pending` empties. A second TPE pass is therefore sound and monotone — a pending element can
  only become decided, never un-decided — so TPE is safe to run on an already-refined residual.
- **D-P9b-3 — clippy bar is `cargo clippy --all-features --lib` (the Phase-6.5 OUTCOMES bar).**
  That invocation is clean (0 new warnings in `tpe/`). The repo's `--lib --tests` clippy is
  *already* non-clean at the 9b base (147 warnings — a pervasive test-code idiom:
  `Evaluator::new(req, &entities, &exts)` trips `needless_borrow`), so it is not the clean bar;
  the new tests follow the identical surrounding-test idiom. The genuinely needless borrows the
  new tests *did* introduce (`&residual.into()`) were removed.

---

## 4. `phase9d`'s decidability question — SETTLED **GO** (raw-cvc5 probe, this plan)

The stub PLAN flagged one go/no-go question for D-70 B: the **element-vs-element transitivity**
constraint is a `set.filter` whose body quantifies over the **same** set S (a nested filter), and
it was *not established* that cvc5's finite-sets + `HO_ALL` fragment stays decidable (returns
`sat`/`unsat`, not `unknown`) under that nesting. **This plan settled it: GO.**

**Probe.** Raw cvc5 1.4.1 (`(set-logic HO_ALL)`), entities as an abstract sort `E`, the ancestors
UF as `anc : E -> (Set E)` (exactly the `declare-fun` shape the encoder emits for the ancestors
`uuf`), the receiver as a symbolic `(Set E)`. Five instances, matching the three grounding shapes
of the stub PLAN:

| Instance | Shape | Expect | Result | Wall |
|---|---|---|---|---|
| `p1_single_filter` | acyclicity + element-vs-named-term transitivity (single-level `set.filter`) | sat | **sat** | 4.8 ms |
| `p2_nested_filter` | **element-vs-element transitivity (NESTED `set.filter` over the same S)** | sat | **sat** | 4.6 ms |
| `p3_nested_unsat` | nested transitivity + acyclicity + a forced **2-cycle** | unsat | **unsat** | 5.1 ms |
| `p4_pinned5_sat` | nested transitivity over a 5-member membership-constrained set | sat | **sat** | 10.0 ms |
| `p5_3cycle_unsat` | nested transitivity + acyclicity + a forced **3-cycle** | unsat | **unsat** | 6.1 ms |

The exact SMT is saved alongside this plan at
`branches/phase9-anyall-completion/probe/d70b/*.smt2` (reproduce with
`cvc5 --tlimit=60000 <file>`). The nested `set.filter` representation of
"∀x∈S. ∀y∈S. y∈anc(x) ⇒ anc(y)⊆anc(x)" is written as
`filter(λx. (filter(λy. y∈anc(x) ⇒ anc(y)⊆anc(x), S) = S), S) = S`.

**Verdict.** cvc5 1.4.1 **decides** every instance — including the nested filter in both polarities
and both a 2- and 3-cycle UNSAT — in single-digit milliseconds, **no `unknown`**. The nested
`set.filter` transitivity constraint is in cvc5's decidable `HO_ALL`/finite-sets fragment, so D-70
option B is encodable with the three-filter grounding and **no reshaping is required**. The decision
is **go** on the direct nested-filter encoding.

**Fallback (recorded, not needed).** If a future cvc5 or a real benchmarked instance regresses to
`unknown`/timeout at useful set sizes, the stub PLAN's fallbacks stand: (a) **bounded unrolling** of
element-vs-element transitivity to the receiver's cardinality when the receiver is a *literal* set
(already the D-68 fold path — those receivers never hit the symbolic footprint); (b) a different
transitivity formulation (e.g. assert transitivity only against the finite set of *named* footprint
terms, dropping element-vs-element, at the cost of a weaker — but still sound, because stricter —
`SameOn`). **These stay in reserve; the probe says the direct encoding is fine.** §6 additionally
requires the Phase-8 harness to measure the nested-filter query at swept set sizes before the Lean
`SameOn` change is committed, so a *tractability* cliff (distinct from decidability) is caught early.

---

## 5. `phase9c-anyall-pred-type-soundness` — D-74 option A (+ D-79)

This is the critical path. It builds the predicate type-soundness theorem that D-74 B's
`normalize_evaluatePred` needs, wires the honest `normalize` into `typeOfAll`, and restores the
real `compile_well_typed` `.all` arm — closing the Phase-5B completeness gap for `.all`.

### 5.1 The theorems to build

**`type_of_pred_is_sound`** — the predicate analogue of `type_of_is_sound`
(`Thm/Validation/Typechecker.lean:52`), over `PredExpr`/`evaluatePred`/`typeOfPred` with `.item`
bound to the element. Proposed statement (the predicate-aware capability invariant is the one new
ingredient — see 5.2):

```
theorem type_of_pred_is_sound {p : PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  InstanceOfWellFormedEnvironment request entities env →
  InstanceOfType env it itTy →                       -- the bound element is an instance of its static type
  typeOfPred p itTy c₁ env = .ok (ty, c₂) →
  GuardedCapabilitiesInvariant p.toExpr c₂ request entities ∧
  ∃ (v : Value), EvaluatesToPred p it request entities v ∧ InstanceOfType env v ty.typeOf
```

where `EvaluatesToPred p it … v` mirrors `EvaluatesTo` (value, or one of the allowed errors
`entityDoesNotExist`/`extensionError`/`arithBoundsError`) over `evaluatePred`. **Note:**
`evaluatePred` cannot itself produce `quantifierError` (it is introduced only by `evalAll`; the
Phase-5B `*_ne_qerr` lemmas in `All.lean` already certify every primitive the predicate can call),
so `EvaluatesToPred` carries the **same three** allowed errors as `EvaluatesTo` — the 4th disjunct
is *not* needed at the predicate level, which simplifies the mirror.

**Files to mirror** (each a per-operator lemma, same shape as the expression soundness proof — this
is the ~6.5k-line fear made concrete, but see 5.3 for the reuse that collapses most of it):
`Thm/Validation/Typechecker/{And,Or,IfThenElse,UnaryApp,BinaryApp,GetAttr,HasAttr,ExtHasAttr,Record,Call,LitVar}.lean`,
plus `.item` (trivial: `evaluatePred .item it = .ok it`, typed `.var .principal itTy`, closed by the
`InstanceOfType env it itTy` hypothesis).

**`normalize_evaluatePred`** — once soundness exists, the preservation proof D-74 B needs:

```
theorem normalize_evaluatePred {p : PredExpr} {itTy c env it request entities} :
  CapabilitiesInvariant … → InstanceOfWellFormedEnvironment … → InstanceOfType env it itTy →
  (∃ ty c', typeOfPred p itTy c env = .ok (ty, c')) →
  evaluatePred (PredExpr.normalize p itTy c env) it request entities
    = evaluatePred p it request entities
```

Its `and`/ff→left, `or`/tt→left, and `ite`→duplicate-live-branch folds preserve evaluation given
that a `.bool .ff`/`.tt`-typed sub-predicate evaluates to `false`/`true`-or-error — i.e. exactly
`type_of_pred_is_sound` + the predicate analogues of `instance_of_ff_is_false` /
`instance_of_tt_is_true` / `instance_of_anyBool_is_bool`. The `ite_self`/`and`/`or` reasoning is the
same shape as the expression `type_of_preserves_evaluation_results` `and`/`or`/`ite` cases.

### 5.2 The predicate-aware capability invariant (`it` enters the capability set)

`evaluatePred` resolves `.item` to the bound value directly — `it` is **not** a request var and is
**not** a slot/unknown (`PredExpr` has no `Slot`/`Unknown`, D-18). The capability invariant for the
predicate world is therefore the ordinary `CapabilitiesInvariant c request entities` **unchanged** —
`it` does not establish or consume a capability about the request/entity store (an `it has a`
capability is predicate-internal and is dropped at the quantifier boundary, D-39; `typeOfAll`
discards the predicate's output capabilities). Concretely: the capability invariant is **not**
predicate-indexed; the only new hypothesis is `InstanceOfType env it itTy` (the element is an
instance of its static element type), which is exactly what `type_of_all_is_sound` already extracts
from the receiver's set-type inversion (`instance_of_set_type_is_set`). This is simpler than D-74's
worst-case framing — confirm it against the `hasAttr`/`getAttr`/`ite` arms early (they are the arms
that read capabilities in the expression proof), but the `it`-as-value structure strongly suggests
no new invariant is needed.

### 5.3 The reuse that keeps this from being a 6.5k-line rewrite

Phase 5B already built the **non-short-circuiting** half of the predicate dispatcher:
`compilePred_well_typed`'s `unaryApp`/`hasAttr`/`binaryApp`/`getAttr`/`extHasAttr`/`record`/`call`
arms are done, and the `evaluatePred`↔`evaluate (p.toExpr …)` **bridge** (D-44 Lemma L3 /
`CompilePredEvaluate`) exists — `evaluatePred p it = evaluate (p.toExpr) …` under the `.item ↦ it`
substitution. **Use the bridge:** prove `type_of_pred_is_sound` by reducing each arm to the
*existing* expression `type_of_<op>_is_sound` via the bridge + `typeOfPred`'s already-threaded
`x₁.toExpr` arguments (`typeOfPred` already calls `typeOfBinaryApp … x₁.toExpr x₂.toExpr`, etc.), so
the per-operator soundness is inherited rather than re-proved. The genuinely new work is: the
`.item` arm, the `.and`/`.or`/`.ite` arms (which thread capabilities and need the predicate
`instance_of_{tt,ff,anyBool}` facts), and assembling `normalize_evaluatePred` from them. Estimate:
**the and/or/ite + item arms + normalize_evaluatePred, ~1–2k lines**, not 6.5k, if the bridge holds
for the straight-line arms. Validate the bridge covers `getAttr`/`hasAttr` capability threading in
the first milestone (M1) — if it does not, fall back to proving those arms directly (the expression
proofs are the template).

### 5.4 Wiring and the ripple

1. `typeOfAll` stores `PredExpr.normalize p₀ τ c env` instead of the source `p` (one line, already
   designed in D-73b; `normalize` is landed).
2. `TypedExpr.WellTyped.all`'s `h₄` is already the D-73b residue hypothesis; the typeOf-ok⇒WellTyped
   `.all` case supplies `p₀ = source` (it already does — confirm it still type-checks after step 1).
3. **Restore the real `compile_well_typed` `.all` arm:** set `TypedExpr.SymCCSupported (.all x₁ p _)
   := x₁.SymCCSupported && p.NoItDependentIn` (lift the D-74-interim `false`), and close the arm
   with the now-wired `compilePred_well_typed` — its `compilePred (normalize p₀)` conclusion now
   lines up with `compile`'s `.all` arm because `typeOfAll` stores `normalize p₀`.
4. Fix the two preservation sites: `type_of_preserves_evaluation_results` `.all` case (now needs
   `normalize_evaluatePred` because `typeOfAll` stores `normalize p₀`, not the source — the exact
   gap D-74 identified) and Part A's `type_of_all_is_sound` (re-confirm; it leans on
   `evalAll_bool_or_qerr` for an arbitrary `f`, so it likely only needs the receiver/set-type
   inversion unchanged — verify the stored-predicate change does not disturb it).
5. **D-79 (folded in here):** now that `normalize_evaluatePred` proves the fold preserves
   evaluation, change `PredExpr.normalize`'s `.ite` constant-condition arms from *duplicating* the
   live branch (`.ite c' t' t'`, worst-case exponential, D-73a) to **folding to the live branch
   once** (`t'` or `e'`) — guarded by the `ite_self`/condition-error reasoning that
   `normalize_evaluatePred` now supplies (a `.tt`/`.ff` condition can still error, so the fold is
   valid only with the error case discharged by soundness). Re-run `normalize_evaluatePred` to
   confirm the simpler fold still preserves evaluation. Keep `Normal`/`typeOfPred_normalize`
   consistent with the new fold.
6. **D-77 completeness lane:** every `SymCCSupported`/`PolicySymCCSupported` hypothesis threaded in
   Phase 5B now discharges for a `.all` whose predicate has no `it`-dependent `in` — nothing to
   change structurally, but re-confirm the verifier completeness theorems and the split
   `compile_ok_iff_welltypedpolicy_ok` still build with the lifted guard.

### 5.5 Green bar, non-vacuity, mutation

**Green bar.** `lake build Cedar SymCC SymTest UnitTest DiffTest Protobuf CedarProto` green, 0
`sorry`; `#print axioms` on `type_of_pred_is_sound`, `normalize_evaluatePred`, and the restored
`compile_well_typed` = `[propext, Classical.choice, Quot.sound]` (+ only the pre-existing datetime
`native_decide` set where a datetime op is reachable — no *new* axiom). The DRT FFI static-lib
target still archives `libCedar_CedarFFI.a`. `CedarSymTests` ≥ 1216/1216 and a **new** e2e test
compiles a `.all` policy and confirms `compile` **succeeds** on it via the restored completeness
path (not merely that the soundness arm holds).

**Non-vacuity.** The `compile_well_typed` `.all` arm must no longer close by contradiction — add a
`#guard`/e2e that a well-typed `it`-free-`in` `.all` policy is `SymCCSupported` and compiles, so the
arm is *exercised*, not vacuously true. (The Phase-5B lesson: a completeness theorem green only
because its guard is `False` proves nothing.)

**Mutation (deterministic unit tests, not fuzzer-only — the learned rule).**
(a) break the `and`/ff→left fold in `normalize` ⇒ `normalize_evaluatePred` fails;
(b) make `type_of_pred_is_sound`'s `.item` arm return the wrong type ⇒ the `getAttr`-of-`it` arm
fails;
(c) revert `typeOfAll` to store the source `p` ⇒ the restored `compile_well_typed` `.all` arm fails
to line up (dispatcher mismatch) — this is the exact F2 gap, now a caught regression.

**Size.** L–XL, multi-day. Split the per-operator lemma files across parallel worktrees cut from
9c's base (Phase-5B pattern); rotate the worker conversation if runs shrink to <1 lemma each and it
reverts red drafts (the learned rule — spawn a fresh worker or drive the file directly).

### 5.6 Implementation decisions (9c implementer, 2026-10-11)

- **D-P9c-1 — `type_of_pred_is_sound` statement shape.** Stated as a `TypeOfPredIsSound (p : PredExpr)`
  predicate (mirroring `TypeOfIsSound`) carrying the extra hypothesis `InstanceOfType env it itTy`
  (the §5.2 "it enters as a value" fact), and a `type_of_pred_is_sound : ∀ {p}, TypeOfPredIsSound p`
  dispatcher proved by structural recursion on `p` (`termination_by sizeOf p`), exactly like
  `type_of_is_sound`. Per-arm lemmas live in `Cedar/Thm/Validation/Typechecker/Pred/<Op>.lean` so
  independent arms can be proved in parallel.
- **D-P9c-2 — `EvaluatesToPred`.** Mirrors `EvaluatesTo` with the SAME three allowed errors
  (`entityDoesNotExist`/`extensionError`/`arithBoundsError`) — no `quantifierError` disjunct, since
  `evaluatePred` never produces it (the `*_ne_qerr` lemmas in `All.lean` certify this; §5.1 note).
- **D-P9c-3 — the capability invariant is NOT predicate-indexed (§5.2 confirmed early).** The
  ordinary `CapabilitiesInvariant c request entities` is reused unchanged; the only new hypothesis is
  `InstanceOfType env it itTy`. `GuardedCapabilitiesInvariant` is stated over `p.toExpr` (the Expr
  reconstruction), since capabilities are keyed by Expr and `typeOfPred` already threads `x₁.toExpr`.
- **D-P9c-4 — straight-line arms mirror the Expr proofs directly, NOT via a type-level bridge.**
  A `typeOfPred p itTy c env = typeOf p.toExpr c env` bridge is FALSE (the `.item` arm types as
  `.var .principal itTy`, whereas `typeOf itExpr = typeOf (.var .principal)` yields the request's
  principal type — they differ in the type component, the same source-vs-normalized hazard as the
  SymCC lesson). So each arm is a near-copy of its Expr twin with `typeOf→typeOfPred`,
  `evaluate→evaluatePred`, inheriting the per-op helpers (`typeOfUnaryApp`, `typeOfBinaryApp`,
  `typeOfGetAttr`, `typeOfHasAttr`, …) which `typeOfPred` calls identically on `.toExpr` args.
- **D-P9c-5 — RESOLVED option (c) → D-94 (2026-10-11).** CAPABILITY THREADING is the real difficulty in `.getAttr`/`.hasAttr`/`.binaryApp`
  (found while scoping M2; §5.2 under-specified this).** The Expr `.getAttr`/`.hasAttr` soundness
  leans on `capability_implies_entity_attribute` / `capability_implies_record_attribute`, which read
  `(x₁, .attr a) ∈ c` as `EvaluatesTo (.hasAttr x₁ a) request entities true` — i.e. capabilities are
  interpreted through `evaluate`, binding `it`↦`request.principal`, NOT through `evaluatePred`
  binding `it`↦the real element. `typeOfPred` nonetheless threads capabilities keyed by `x₁.toExpr`
  (and `.and`/`.ite` extend them with `c ∪ c₁`). So a capability about an `it`-DEPENDENT subterm is
  meaningless under `evaluate`, and the Expr capability lemmas cannot be reused verbatim. §5.2's "the
  invariant is not predicate-indexed" is correct for the QUANTIFIER BOUNDARY (`typeOfAll` discards
  the predicate's OUTPUT caps, D-39) but does NOT by itself discharge the WITHIN-predicate getAttr
  capability check. **Resolution options for M2's capability arms (next worker, decide in M2):**
  (a) prove that the capabilities `typeOfPred` consults for a getAttr/hasAttr check are only ever
  about `it`-free subterms (so `evaluate = evaluatePred` on them, and the Expr lemmas transfer) —
  likely true because `it` has no attrs capability established (an `it has a` is dropped at the
  boundary, D-39), but must be proven as a `evaluatePred`-vs-`evaluate` agreement lemma on the
  capability-keyed subterm; OR (b) state a predicate-aware capability invariant
  `CapabilitiesInvariantPred c it request entities` (over `evaluatePred` with `it` bound) and thread
  it, re-proving the two `capability_implies_*` lemmas for `evaluatePred`. Option (a) is lighter if
  the it-free claim holds; (b) is the general fallback. The `.binaryApp .hasTag`/`.getTag` arms have
  the same shape (tag capabilities). The `.item`/`.lit`/`.var`/`.unaryApp`/`.record`/`.call` arms do
  NOT hit this (unaryApp/record/call output `∅` caps and read none from `c`).

**Milestones (9c):**
- **M1** — foundation: `EvaluatesToPred`, `TypeOfPredIsSound`, prove `.item`/`.lit`/`.var`; stub the
  recursive arms as separate lemmas; dispatcher assembled. Validates the mirror strategy.
- **M2** — straight-line arms: `.unaryApp`, `.binaryApp`, `.getAttr`, `.hasAttr`, `.extHasAttr`,
  `.record`, `.call` (parallelizable; copy the Expr proofs).
- **M3** — hard arms: `.and`, `.or`, `.ite` (capability threading + `instance_of_{tt,ff,anyBool}`).
- **M4** — `normalize_evaluatePred` from M1–M3.
- **M5** — wiring §5.4 (steps 1–6) + D-79 fold-once + restored `compile_well_typed` `.all` arm.
- **M6** — green bar §5.5, non-vacuity + mutation evidence, `#print axioms`.

---

## 6. `phase9d-anyall-set-footprint` — D-70 option B (set-typed footprints)

Stacked on 9c's final tip (it needs the real, un-guarded completeness arm; §1). The decidability
question is **settled go** (§4), so this is an encoding + proof branch, not a research branch.

### 6.1 The encoding (three `set.filter` groundings)

For a footprint **set entry** S (the compiled receiver, `(Set E)`) and the ancestors UF `anc : E ->
(Set F)` per entity-type pair:

- **Acyclicity of S:** `(= (set.filter (λ x. not (set.member x (anc x))) S) S)` — one filter
  (probe `p1`).
- **Element-vs-named-term transitivity** (an element x∈S vs a named footprint Term c): one filter
  over S asserting `(=> (member c (anc x)) (subset (anc c) (anc x)))` and the symmetric direction
  (probe `p1`).
- **Element-vs-element transitivity** (two elements of the same S): the nested filter
  `(= (set.filter (λ x. (= (set.filter (λ y. (=> (member y (anc x)) (subset (anc y) (anc x)))) S) S)) S) S)`
  (probes `p2`/`p4` sat, `p3`/`p5` unsat) — **decided** by cvc5 1.4.1 (§4).

Mirror the existing `acyclicity`/`transitivity` term-builders in `Enforcer.lean` with set-entry
analogues (`acyclicitySet`/`transitivitySet`), emitted by `enforce` when a footprint entry is
set-typed. **The Rust `cedar-policy-symcc` enforcer must emit byte-identical SMT** (D-36) for the
`symcc-*` differential.

### 6.2 Footprint + `SameOn` changes

- **`footprint`/`footprintAllPred`:** add the receiver **set term** itself as a footprint entry for
  a `.all` whose predicate contains an `it`-dependent `in` (the case option A rejected). The
  `it`-free entity subterms stay as today (`footprintPred`). A new entry kind (set-typed) is needed
  — `footprint` currently returns `Set Term` of `.option .entity` terms only; widen it to admit a
  `.set (.entity …)` term, or carry set entries in a parallel field (prefer the former if the WF
  lemmas stay simple).
- **`SymEntities.SameOn`** (`Thm/SymCC/Enforcer/Footprint.lean:147`): today it grants ancestor
  agreement `∀ t ∈ ft, ∀ uid, t.interpret I₁ = .some (.entity uid) → …`. Add a disjunct for a
  **set-typed** footprint entry: for every element UID in the interpreted set S, ancestor agreement
  holds — grounded via the same `set.filter` the enforce step emits. The extension must be exactly
  strong enough to discharge the `.all` case of `compile_interpret_on_footprint` **without** the
  option-A `in` guard.
- **Drop the option-A guard:** remove `if ¬ p.NoItDependentIn then .error .unsupportedError` from
  `compile`'s `.all` arm (`Compiler.lean`), and the matching `NoItDependentIn` conjunct from
  `TypedExpr.SymCCSupported` (restored to `x₁.SymCCSupported` alone for `.all`, since the `in`
  restriction is gone). Re-confirm `compile_well_typed`'s `.all` arm and the D-77 completeness lane.

### 6.3 Order within 9d (encoding-first, per the stub PLAN)

1. **Encoding + raw-cvc5 + Phase-8 harness first** (before any Lean `SameOn` change): wire the
   set-entry grounding into the Rust enforcer, and run the Phase-8 `anyall_symcc_bench` harness over
   the nested-filter query at swept set sizes to confirm *tractability* (not just decidability) at
   useful N — the §4 probe decides in ms, but the harness must show it does not fall off a cliff at
   the N the benchmark already exercises. Record the envelope in `RESULTS.md`.
2. Then the Lean changes: footprint set entries, `SameOn` extension, the
   `compile_interpret_on_footprint` `.all` case **without** the A guard, the WF/mem lemmas
   (`footprintAllPred_wf`, `mem_footprint_exists_wf_prop`), and the Rust mirror for the differential.

**Green bar.** `lake build Cedar …` green, 0 `sorry`, axiom-clean; `CedarSymTests` green with a new
e2e that compiles **and solves** a `.all` policy whose predicate uses an `it`-dependent `in` (the
exact shape option A rejected) and confirms cvc5 decides it. The `symcc-*` DRT differential (Rust vs
Lean) byte-matches on an `it`-dependent-`in` `.all`. The generator's low-weight `it`-dependent-`in`
arm (D-76) now produces **solved** queries, not `unsupportedError` lockstep — update the D-76
generator/differential expectation accordingly (both engines now *compile* it).

**Non-vacuity + mutation.** e2e that cvc5 returns `unsat` on a genuine always-allows query through
the `it`-dependent `in` (so a real `set.filter` grounding is exercised, not a folded/rejected
query). Mutation: drop the element-vs-element nested filter from the grounding ⇒ a transitivity
counterexample that should be `unsat` comes back `sat` (caught by the e2e); break the `SameOn`
set-entry disjunct ⇒ `compile_interpret_on_footprint` `.all` fails.

**Size.** L, multi-day (Lean footprint/SameOn proofs + Rust mirror). On the critical path *after*
9c.

---

## 7. Forks (numbered; recommendation given — the orchestrator decides, do NOT stop)

**FORK-1 — D-74 resolution: option A (honest soundness) vs option C' (tightened guard, defer A).**
D-74 (Phase 5B) left this open. Option A builds `type_of_pred_is_sound` + `normalize_evaluatePred`
and wires `normalize` (full `.all` completeness; §5). Option C' keeps `typeOfAll` storing the source
predicate and tightens `TypedExpr.SymCCSupported` to exclude any `.all` with a non-Bool dead operand
(smaller proof, but widens the compile guard / rejects more `.all` policies, and leaves `normalize`
+ `compilePred_well_typed` as permanent dead code or requires deleting them).
**Recommendation: option A.** The user mandate is "implement all phases eventually" and Phase 9 is
*the* completion phase — C' was explicitly the "unblock the stack *now*, do A at Phase 9" escape, and
this *is* Phase 9. A also discharges the F2 dead-code debt (`normalize`/`compilePred_well_typed`
become live) and closes req 5.1 completeness for `.all` honestly. The multi-day cost is the point of
this phase.

**FORK-2 — D-70 B footprint entry representation: widen `footprint`'s term set vs a parallel
set-entry field.** §6.2. Widening `footprint : … → Set Term` to admit `.set (.entity …)` terms keeps
one data structure and one WF lemma family, but every existing `footprint` consumer that assumes
`.option .entity` must tolerate a set term. A parallel field (`footprint` + `footprintSets`) keeps
the entity-term consumers untouched but doubles the WF/mem lemma surface.
**Recommendation: widen the term set**, and prove `footprint_wf` admits the new shape, *unless* the
first milestone finds a consumer that genuinely breaks on a set-typed term — then fall back to the
parallel field. (Decide in 9d M1 against the actual consumer list; this is an internal-structure
call, not user-level.)

**FORK-3 — req 7.3 residual shape: `AllPartial{decided_false,pending}` vs a filtered-receiver
`All`.** §3. The `AllPartial` shape carries the pinned-`false` fact that no-short-circuit needs; the
filtered-receiver reuse of `All` is smaller but cannot represent it.
**Recommendation: `AllPartial`.** The filtered-receiver form is unsound for the 2.8 semantics (it
can lose a pinned `false` and wrongly short-circuit), which the mutation tests in §3 are designed to
catch — so the smaller option is not actually viable. Internal-structure call.

None of these is irreversible or taste-level enough to block on; all three have a clear recommended
default, taken above.

---

## 8. Milestone summary & green commands

Sub-branch bars, in merge order:
- **9a (D-78):** `lake build Cedar SymCC SymTest` + `CedarSymTests` 1216/1216; logic-selection unit
  test per engine; Rust `symcc-*` byte-match.
- **9b (7.3/D-80):** `cargo test -p cedar-policy-core --features tpe,anyall --lib` up; non-`anyall`
  `tpe::` byte-unchanged; refinement + re-authorization-parity tests; 3 mutations caught.
- **9c (D-74 A + D-79):** full Lean tree green, 0 `sorry`, axiom-clean; `type_of_pred_is_sound` +
  `normalize_evaluatePred` + restored real `compile_well_typed` `.all` arm; `normalize` wired into
  `typeOfAll`; D-79 fold-once; new "compile succeeds on a `.all`" e2e; 3 mutations caught.
- **9d (D-70 B):** full Lean tree green, 0 `sorry`, axiom-clean; set-typed footprint entries +
  `SameOn` extension; option-A `in` guard removed; `it`-dependent-`in` `.all` compiles **and** cvc5
  decides it; Rust mirror byte-matches; D-76 generator expectation flipped to solved.

Environment (verbatim, every Lean build): `export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"; unset LD_PRELOAD; export LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar CVC5=/home/linuxbrew/.linuxbrew/bin/cvc5`.
cvc5-backed `CedarSymTests` additionally needs the D-13 `LIBRARY_PATH`/`LD_LIBRARY_PATH` host quirk
(see Phase-5B OUTCOMES §6). Logs/probes under `$KIROCREW_SCRATCH`; the D-70 B probe SMT is committed
under `branches/phase9-anyall-completion/probe/d70b/`.

---

## 9. Decisions recorded by this plan

See DECISIONS.md **D-89..D-93** (sub-branch split; D-70 B probe = go; D-74 A as the chosen D-74
resolution; req-7.3 `AllPartial` shape; D-70 B footprint-entry representation). The forks above are
recorded there with their recommended defaults.

### 5.7 D-97 implementation notes (9c implementer, resumed 2026-10-11)

- **M0 landed green:** `PredExpr.toCapKey`/`itCapKey` + `typeOfPred` rewire; `lake build Cedar`
  616 jobs, `CedarSymTests` 1216/1216, `CedarUnitTests` 466/466. Only re-green needed was the
  Phase-5B `compilePred_well_typed` chain (`predExpr_toCapKey_eq_lit` + the extHasAttr key arg).
- **Predicate capability invariant landed:** `CapabilitiesInvariantPred` /
  `GuardedCapabilitiesInvariantPred` + `empty_*` + `capability_union_invariant_pred`;
  `TypeOfPredIsSound` restated as the full mirror. `.item`/`.lit`/`.var`/`.unaryApp`/`.record`
  arms GREEN under it (record axiom-clean). The attr/tag arms' VALUE side now closes via `hci`
  (the capability-`.tt` case that D-96 showed unprovable under weak-only soundness).
- **OPEN gap for the resumer — the guarded PRODUCTION side needs `toCapKey` injectivity.**
  `CapabilitiesInvariantPred`'s fields quantify `∀ q, q.toCapKey = e → <fact of q>`. The attr/tag
  arms' guarded conclusion must PRODUCE `CapabilitiesInvariantPred (singleton (x₁.toCapKey) (.attr a))`,
  i.e. show the fact for EVERY `q` with `q.toCapKey = x₁.toCapKey` — which needs `q = x₁`, i.e.
  `toCapKey` injectivity. **`toCapKey` is NOT unconditionally injective**: `.item` and the predicate
  `.getAttr (.var .context) "__cedar::anyall::it"` both map to `itCapKey`. Injectivity holds only
  for predicates whose context does NOT declare the reserved attribute — exactly the
  `TypeEnv.NoReservedItKey` side condition the D-97 brief requires. **Resolution:** (a) add
  `TypeEnv.NoReservedItKey` (decidable: `"__cedar::anyall::it" ∉ env.reqty.context` keys) and thread
  it into `TypeOfPredIsSound`; (b) prove `toCapKey_injective_of_no_reserved` (structural induction);
  (c) use it to discharge the `∀q` production side. Alternatively reformulate
  `CapabilitiesInvariantPred` so the production side asserts the fact for the single producing `q`
  (carry the `q` witness in the capability) — avoids injectivity but changes the invariant shape.
  Until this lands, the attr/tag arms are red ONLY on the production side (2–4 errs each); their value
  side is done.
- **Then:** finish `.and` inversion field-shaping (the recurring post-`simp` Eq-vs-And shape of the
  `h_1` pair-equality — use the exact goal state, not guessed `rfl`/`obtain`), `.or`/`.ite` (same
  shape as `.and`), the dispatcher `type_of_pred_is_sound`, M4 `normalize_evaluatePred`, M5 wiring,
  M6. The Lean validator regression (reject `principal has "a" && context.s.all(it.a==1)`) and the
  DRT differential are M6 non-vacuity items, not yet done.

### 5.8 D-P9c-7 — production-side resolution (approach A, 2026-10-11)

Chose **approach (A), inverse-based invariant.** Added to `Cedar/Spec/Expr.lean`: `itCapKey`
(already present), `PredExpr.NoReservedItAccess` (true unless the predicate contains the reserved
access `context["__cedar::anyall::it"]`), and `PredExpr.ofCapKey : Expr → PredExpr` (total structural
inverse of `toCapKey`, `.getAttr` arm guarded by a DECIDABLE `if a = .var .context ∧ attr =
"__cedar::anyall::it"`). `CapabilitiesInvariantPred` (`Pred/Basic.lean`) is restated over `ofCapKey`:
`∀ e a, (e,.attr a) ∈ c → EvaluatesToPred (.hasAttr (ofCapKey e) a) it … true` (and the `.tag`
analogue) — no `∀q` quantifier, so the production side carries a single fact. `TypeOfPredIsSound`
gains an `NoReservedItKey env` hypothesis (`¬ context.contains "__cedar::anyall::it"`). The bridge
lemma `ofCapKey_toCapKey : q.NoReservedItAccess → ofCapKey q.toCapKey = q` connects consumer and
producer (`toCapKey` injective exactly on `NoReservedItAccess` predicates). Still TODO: finish
`ofCapKey_toCapKey`'s getAttr/list cases; the `well-typed-under-NoReservedItKey ⇒ NoReservedItAccess`
lemma; the outer→predicate invariant entry lemma at the quantifier boundary (`evaluatePred q it =
evaluate q.toExpr` on it-free `q`); then re-thread the arms, dispatcher, M4, M5, M6.


### 5.9 D-P9c-8 / D-P9c-9 — fresh-worker progress (2026-10-11)

**D-P9c-8 — `type_of_pred_implies_wf_type` is the remaining support lemma for the `.getAttr`
record-receiver error-side witness.** The weak-soundness existential `∃ v, InstanceOfType env v
ty.typeOf` needs `ty.typeOf` inhabited, hence well-formed, on the branch where the sub-expression
ERRORS and the attribute is OPTIONAL (the required case is witnessed from the IH value instance; the
entity-receiver case gets WF from the schema via `wf_env_implies_wf_attrs`). `InstanceOfType` alone
does not yield record-type WF (an absent optional attr's type is unconstrained by the value).
Resolution: add `type_of_pred_implies_wf_type` (predicate twin of `typechecked_has_well_formed_type`),
carrying `env.WellFormed` + `itTy.WellFormed env` (threaded at the `typeOfAll` boundary, where `itTy`
is the set element type, WF by set-type inversion). Bounded structural induction over `typeOfPred`:
`.item` → `itTy.WellFormed env`; every other arm reuses the SAME per-op type helper, so output WF
follows from operand WF. Left as the single open obligation for `.getAttr` (2 red spots, no sorry).

**D-P9c-9 — the ofCapKey single-fact invariant ELIMINATES the former ∀q producer-side gap
(D-95/D-96/D-97).** With `CapabilitiesInvariantPred` keyed through `PredExpr.ofCapKey` (approach A,
§5.8), the producer side of every attr/tag arm proves one fact about `ofCapKey e` instead of a fact
for every `q` with `q.toCapKey = e`. Support lemma (a) `type_of_pred_implies_no_reserved` (§5.1 step
1, LANDED GREEN) gives `x.NoReservedItAccess` from the typing, so `ofCapKey_toCapKey` rewrites
`ofCapKey x.toCapKey = x` and the producer/consumer sites close about `x` directly. This is why
`.hasAttr` is now fully GREEN and `.extHasAttr`'s producer closes. The residual in `.extHasAttr` is
the reserved-attr-NAME exclusion for `ofCapKey (.getAttr x₁ a)` when `a` could be the reserved key: a
well-typed ext-has-attr never names the reserved attr (Rust's schema parser refuses `__cedar` names),
but that needs an attr-name `NoReservedItAccess` premise threaded through `typeOfExtHasAttr`, deferred
(2 red spots, no sorry).
