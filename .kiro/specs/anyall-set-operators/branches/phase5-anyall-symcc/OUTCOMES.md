# Phase 5 outcomes — SymCC analyzability of `.all` (`phase5-anyall-symcc`)

## Result

M1–M4 DONE. The Lean symbolic compiler (SymCC), its optimized variant (SymCCOpt), the
encoder, the footprint, and the interpret/evaluate soundness theorems all support Cedar's
`.all` set quantifier end-to-end, axiom-clean. The full tree is **GREEN** —
`lake build Cedar SymCC SymTest UnitTest DiffTest Protobuf CedarProto` = 782 jobs, 0 errors,
`grep -rn '\bsorry\b' cedar-lean/Cedar cedar-lean/SymTest` = 0. The `CedarSymTests` exe runs
**1216/1216** (`AnyAll.e2e` 12/12) with cvc5 1.4.1. Review round 1 raised 5 findings; F3/F4/F5
fixed; F1/F2 are tied to the open **D-74** (user decision) and documented, not closed.

One thing is deliberately NOT established: SymCC `.all` **completeness** (the
`well-typed ⇒ compiles` direction) is guarded out behind the D-74-interim and D-77. See item 2.

---

## 1. Final encoding (D-52, SETTLED)

`Op.set.all` is encoded via the decidable **`set.filter` comprehension** fragment (Mohamed et
al., FMCAD 2025), NOT quantifiers. `Encoder.lean`'s `Op.set.all [set, pred, err]` arm emits
exactly two comprehensions and the tri-valued Option shape:

- `valFilter = (set.filter (λ it. P[it]) S)` — elements where the predicate holds;
- `errFilter = (set.filter (λ it. ERR[it]) S)` — elements where the predicate errors;
- result `ite (not (errFilter = ∅)) none (some (valFilter = S))` — i.e. quantifierError
  (`none`) if ANY element errors, else `some (all elements satisfy P)`.

`encode` sets the SMT logic to `HO_ALL`. The literal-receiver concrete fold was moved OUT of
`Factory.set.all` into the compiler (D-68), so `Factory.set.all` is now purely symbolic
(`.app Op.set.all [set, pred, err] (.option .bool)`). This supersedes the earlier
quantifier-shaped D-34/D-51 encoding.

## 2. Soundness proven + axiom-clean; completeness guarded behind D-74-interim / D-77

**Soundness (PROVEN, axiom-clean = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):**
- `compile_interpret_on_footprint` — the `.all` arm is real (`compile_interpret_all_on_footprint`,
  the D-70 option-A footprint path), statement unchanged (`SameOn ft ⇒ interpret I₁ = interpret I₂`).
- `compile_evaluate` — real `.all` arm (axioms = the three standard ones PLUS only the
  pre-existing datetime `native_decide` set; no new axiom).
- `type_of_all_is_sound` (Part A) — full strength; `EvaluatesTo` carries the 4th disjunct
  `.error .quantifierError`; folds via `evalAll_bool_or_qerr`.
- `footprintAllPred` (D-71) mirrors `compile`'s `.all` arm; `Opt.compile.correctness` /
  `Opt.compile_footprint_wf` carry real `.all` arms (SymCCOpt supports `.all`).
- `compilePred_well_typed` — the 13-arm predicate dispatcher is fully proven (axiom-clean).

**Completeness (GUARDED OUT — req 5.1 open for completeness):** under the **D-74-interim**,
`TypedExpr.SymCCSupported (.all _ _ _) := false`, so every `.all` is excluded from the
`well-typed ⇒ compiles` fragment and the `compile_well_typed_on_wf_expr` `.all` arm closes by
contradiction (the real arm is retained commented, "BLOCKED on D-74"). **D-77** (SETTLED,
option b) threads the `SymCCSupported` / `PolicySymCCSupported` / `PoliciesSymCCSupported` guard
into the SymCC verifier COMPLETENESS lane only: `compile_ok_iff_welltypedpolic{y,ies}_ok` is
split into an UNGUARDED `.mp` (`compile_ok_implies_welltypedpolic{y,ies}_ok`, soundness) and a
GUARDED biconditional; soundness-lane theorems stay unguarded. Adding a hypothesis never makes a
theorem false, so everything is sound — but the SymCC analyzability promise for `.all` ships as
the **soundness half only** until D-74 lands. The e2e cvc5 tests DO compile concrete `.all`
policies and the SMT decides them, so this is a proof-coverage gap, not evidence compilation fails.

## 3. Deviations

- **D-61** (bug found + fixed): the `set.all` bound-variable double-wrap — `some vi` coercing to
  `Option.some (Term.some vi)` inside a `Term` namespace double-wrapped the substituted element.
  Fixed; `SymTest/AnyAll.lean` compile-time `#guard`s regression-guard it (mutation (a) catches a
  revert).
- **D-68**: the literal-receiver concrete fold was moved from `Factory` into the compiler
  (per-element `compilePred p (someOf vi)`, `conj = foldr and … true`,
  `anyErr = foldr or (not isSome) … false`), so the fold survives recompilation under an
  interpretation (keeps `compile_interpret .all` true).
- **D-70 option A** implemented (quantifier footprint kept `it`-free: `compile` REJECTS an
  `it`-dependent LEFT operand of `in` with `unsupportedError`, D-71 guard); **option B**
  (set-typed footprint entries) deferred to **Phase 9** (its own `branches/phase9-…/PLAN.md`).

## 4. `PredExpr.normalize` / `compilePred_well_typed` are landed but NOT wired (F2), pending D-74

D-73b is recorded SETTLED as "`typeOfAll` stores `normalize p₀`", but that wiring did NOT land:
`typeOfAll` still returns the SOURCE `p`. `PredExpr.normalize` is referenced only inside the
statement/proof of `compilePred_well_typed`; `compile`'s `.all` arm compiles the un-normalized
stored predicate, so the dispatcher's `compilePred (normalize p₀)` conclusion does not line up
with it — which is exactly why the real `compile_well_typed` `.all` arm is left behind the
D-74-interim contradiction. These are inert scaffolding for a D-74 resolution: compile green,
0 sorry, axiom-clean, but proving nothing the live pipeline uses. Resolving D-74 must either wire
`normalize` in (option A: store `normalize p₀`, add `type_of_pred_is_sound` +
`normalize_evaluatePred`, fix the two preservation sites, wire the real `.all` arm) or drop the
`normalize` dependence (option C': prove the dispatcher over the source predicate under a
tightened guard) — it must not remain permanent dead code.

## 5. Phase 6 preconditions

- **D-31 — FIXED** on the `phase6-anyall-drt-differential` branch (the pre-existing
  `cedar-drt/fuzz` proto-record `BTreeMap` mismatch that blocked the fuzz targets).
- **Rust `cedar-policy-symcc` `.all` arm EXISTS** (cedar `826cc339`): the Rust SymCC mirrors the
  Lean `HO_ALL` / `set.filter` encoding (D-36). **Encoder emission is in progress** — the Rust
  side must emit the same two `set.filter` comprehensions + tri-valued Option shape as
  `Encoder.lean` for the differential (`symcc-*`) targets to agree.
- The DRT consumes the Lean FFI **static library**, not the exe: `build_lean_lib.sh` runs
  `lake build Cedar:static Protobuf:static CedarProto:static Cedar.SymCC:static CedarFFI:static
  Batteries:static` (1079 jobs here), which archives `libCedar_CedarFFI.a`. `CedarFFI/ToJson.lean`
  now serializes the anyall nodes (`Op.set.all`, `PredExpr`).

## 6. Exact green commands

```sh
cd /local/home/luxask/code/wt/p5b-main/cedar-lean
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"
unset LD_PRELOAD; export LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar

# full proof tree (782 jobs, 0 errors, 0 sorry)
lake build Cedar SymCC SymTest UnitTest DiffTest Protobuf CedarProto

# the DRT FFI static-lib target (1079 jobs; archives libCedar_CedarFFI.a)
lake build Cedar:static Protobuf:static CedarProto:static Cedar.SymCC:static CedarFFI:static Batteries:static

# cvc5-backed SymTest suite (1216/1216; AnyAll.e2e 12/12) — the D-13 host-lib quirk:
LEANLIB=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/lib
export LIBRARY_PATH="$LEANLIB:$LEANLIB/lean"
export LD_LIBRARY_PATH="$LEANLIB:$LEANLIB/lean:$LD_LIBRARY_PATH"
export CVC5=$(which cvc5)       # /home/linuxbrew/.linuxbrew/bin/cvc5 (1.4.1)
lake build CedarSymTests && .lake/build/bin/CedarSymTests
```

Count note: the `CedarSymTests` exe reports **1216** solver-backed tests (12 of them
`AnyAll.e2e`). The M5-prep note's "2422" figure double-counts / includes the separate
`CedarUnitTests` exe; the solver-backed figure is 1216.

## Review

**Round 1** (`review-round1.md`) — 5 findings:
- **F1 (MAJOR, by design)** — SymCC `.all` COMPLETENESS not established; `SymCCSupported(.all)=false`
  excludes `.all` from `well-typed ⇒ compiles` and the verifier completeness theorems. **OPEN**,
  tracked by D-74 (interim shipped) / D-77. Sound and documented.
- **F2 (MODERATE)** — `typeOfAll` does not store `PredExpr.normalize p`; `normalize` +
  `compilePred_well_typed` are landed but inert (not wired). **OPEN**, tied to D-74 (recorded on the
  D-74 row).
- **F3 (MINOR, doc)** — stale "SymCCOpt rejects `.all`" / D-49-D-50 "tree RED" / "exe does not link"
  claims. **FIXED** — `c07b677` (AnyAll NOTE) + `33f3e38` (D-49/D-50 SUPERSEDED, tasks.md exe-link
  corrected to links/runs 1216/1216 with the D-13 `LIBRARY_PATH`).
- **F4 (MINOR, test-coverage)** — no e2e sat case pivoting on a genuine per-element error; no `.any`
  e2e. **FIXED** — `c07b677` added `all(it < it+1) ≢ true` [overflow error path, sat] and the `.any`
  lowering pair (`≡` unsat, `≢ all` sat); exe 1213 → 1216, AnyAll.e2e 12/12.
- **F5 (NIT)** — OUTCOMES.md missing. **FIXED** — `34af13b` (this file).

**Round 2** (`review-round2.md`) — **NO ACTIONABLE FINDINGS.** Two LOW residual observations,
recorded as follow-ups:
- **F6 → D-78 (LOW)** — `HO_ALL` set for every SymCC query, not only `.all` queries (sound; candidate
  improvement: gate on a `set.all` term being present).
- **F7 → D-79 (LOW, dead code today)** — `PredExpr.normalize`'s `.ite` arms duplicate the live branch
  ⇒ worst-case exponential; inert until D-74 option A; fix by sharing or folding-to-live-branch.

**Publication:** PR [#6](https://github.com/luxas/cedar-spec/pull/6) (luxas/cedar-spec) updated to
`34af13b` (and the final doc-close-out commit below).

---

---

## Per-milestone commit map

Branch `phase5-anyall-symcc` (= `phase5-anyall-symcc-wip-partA`), parent
`phase4-anyall-surface-syntax`; 200 commits. Key anchors (newest first within a milestone):

**M1 — trusted `set.filter` encoder layer / encoding frozen (D-51, D-52):**
- `0a3ab8f` D-52 (`set.filter` encoding supersedes the D-34/D-51 quantifier shape)
- `09625d4` D-51 (SymCC `.all` encoding frozen; decidability measured)
- `5b8ec0f` M1 trusted `set.filter` layer for `Expr.all`

**M2 — `Op.set.all` term typing + WF + the concrete fold (D-53–D-57, D-61):**
- `342626c` D-53 full predicate-fragment encoder
- `a4aef0b`/`59606e0` `Op.WellTyped.set.all_wt` term typing rule + domain/typeOf arms
- `bc6b1fb`/`a1a04af`/`924d072` D-54 reject → D-55 concrete fold + `interpretWith`
- `d8de411` D-55a (`set.all` operands are Bool-typed); `6a192b9` `Term.NoSetAll`
- `532b0f8`/`e5b232c` Lemma A/B (`substAnyAllIt` agreement + WF/typeOf transport)
- `f88cfa2`/`bc91b68` D-56 `NoSetAll` / D-57 `anyAllItTyped` premises

**M3 — compiler `.all` arm + interpret + evaluate soundness (D-62–D-69):**
- `a4c04cc` `compile_interpret .all` proven (D-68 fold / D-69 `.none` short-circuit)
- `555bcad`…`ea42f83` `CompilePredEvaluate` dispatcher (all 13 arms) + `evaluatePred_wf`
- `bab5d5d`…`4d567bb` `compile_evaluate_all` (`all_fold_reconcile` / `evalAll_mem_char` /
  `all_fold_mem_char`); `b94439c` wires `compile_evaluate` `.all` arm

**M4 — footprint (D-70 A, D-71) + optimized compiler + the compile_well_typed dispatcher (D-72/73/74/77):**
- `b7e80d8` D-70 common (`mentionsIt`/`NoItDependentIn` + `footprintPred` + `footprint .all`)
- `4dd6b9e` `Enforcer/Footprint.lean` fully green (`.all` case proven)
- `c87f855` **D-71** `footprintAllPred` mirrors `compile`'s `.all` arm
- `0d44204`/`963d777` **D-70 A** complete (`compile_interpret_on_footprint .all`; guard SymTest)
- `cde2f46` **M4** SymCCOpt compiler `.all` arm
- `deb1c08` **D-72** `SymCCSupported` guard + `WellTyped.all` Bool-residue `h₄`
- `2607fdb`/`c1009a7` **D-73** SETTLED (B): `PredExpr.normalize` + `Normal`
- `a3f24c5`…`b6d41c5` **D-72 step 3** `compilePred_well_typed` arms (item/lit/var … binaryApp all ops)
- `a92b954`…`f1f6256` **D-73b** generic arms + dispatcher recurses on source `p₀`, record/call arms
- `f0608bf` **D-73b** dispatcher fully green (`compilePred_well_typed` complete)
- `dd8cead` **D-74 (OPEN)** predicate-type-soundness blocker recorded
- `1e5d4bd` **D-72 step 4i** `NoQuantifier → SymCCSupported` rename
- `937648e` **D-74-interim** `SymCCSupported (.all) := false`; `.all` arm by contradiction
- `32a34a2` CedarFFI `ToJson` serializes the anyall nodes
- `b8fcde7` **D-77** (option b) thread the guard into the verifier completeness lane
- `392dd3c`/`2daf3bc` tasks.md Phase 5 status

**Review round 1 fixes:**
- `c07b677` F3 (SymCCOpt NOTE) + F4 (`.all` overflow error-path + `.any`-lowering e2e; 1216/1216)
- `33f3e38` F2/F3 docs (D-49/D-50 superseded; D-74 F2 wiring note; tasks.md exe-link corrected)
- this commit: F5 (this OUTCOMES.md)
