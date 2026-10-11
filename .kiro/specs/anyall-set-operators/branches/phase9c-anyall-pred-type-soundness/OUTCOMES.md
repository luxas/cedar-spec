# Phase 9c Outcomes — D-74 option A: predicate type soundness, `normalize` wiring, honest `.all` completeness (`phase9c-anyall-pred-type-soundness`)

**Status:** DONE — review converged (round 1: NO ACTIONABLE FINDINGS). Sub-branch 3 of 4 of Phase 9
(`branches/phase9-anyall-completion/PLAN.md` §5, implementation notes §5.6–§5.10). Closes **D-74 (option A)**,
**D-73 B / D-73b** (wired), **D-79**, and the Phase 5B review finding F2 (`normalize` / `compilePred_well_typed`
were dead code). Lean only; the nested cedar (Rust) repo is unchanged by this branch (its tip stays the Phase 7 /
9b tip), so there is no cedar-side PR. 74 commits (incl. 4 merges of a parallel arm wave) off `bfb7d02`.

## What was proved (all axiom-clean: `[propext, Classical.choice, Quot.sound]`; 0 `sorry`)
- **`type_of_pred_is_sound`** (`Thm/Validation/Typechecker/Pred/`, 14 arm files + dispatcher): well-typed
  predicates evaluate (per element `it`) to a value of the declared type or an error, and produce the
  capabilities their typing claims. Hypotheses: `NoReservedItKey env`, `itTy.WellFormed env`,
  `InstanceOfType env it itTy`, `CapabilitiesInvariantPred c it …` (interpreted through `PredExpr.ofCapKey`).
  The error disjunct admits ANY error (D-94): the expression theorem's "no missing-attribute error" guarantee
  is deliberately not claimed for predicates; downstream needs only value-level facts.
- **`type_of_pred_implies_wf_type`** (D-P9c-8), **`type_of_pred_implies_no_reserved`**, **`ofCapKey_toCapKey`**,
  `capability_{union,intersection}_invariant_pred`, the it-free bridge `evaluatePred_eq_evaluate_toExpr`, and
  the quantifier-boundary entry lemma `entry_capabilities_invariant_pred` (D-99).
- **`normalize_evaluatePred`** (M4): the D-73 B normalization is evaluation-preserving under source typing.
- **`type_of_preserves_evaluation_results`**, `.all` case closed (typed-AST erasure now covers `.all`).
- **`compile_well_typed`**, real `.all` arm (`compile_well_typed_all`): a well-typed `.all` with no
  it-dependent `in` compiles in SymCC to an option-Bool term — `.all` completeness without the interim.

## Validator semantics changed (each matched against Rust by running both validators; DRT 0 mismatches)
- **D-97** — `it`-rooted capability keys. `PredExpr.toCapKey` maps `it` to `itCapKey =
  context["__cedar::anyall::it"]` (Rust: the reserved `IT_SENTINEL` unknown), so an outer capability on
  `principal` can no longer justify `it.a` (the Lean validator previously accepted
  `principal has "a" && context.s.all(it.a == 1)`; Rust rejected it). `ofCapKey`/`NoReservedItAccess`
  give the inverse on reserved-free predicates.
- **D-98** — the environment validator rejects a request-context attribute literally named
  `__cedar::anyall::it` (`RequestType.WellFormed` conjunct; `#guard` regression). Known deliberate
  divergence: Rust reserves the `__cedar` *namespace* but does not reject that bare attribute name; Lean is
  now strictly stricter on it (safe direction, unobservable by the generators).
- **D-99** — `typeOfAll` passes only clean outer capabilities (keys in the image of `toCapKey` with an
  it-free preimage) into the predicate. Acceptance no-op: a set-free, reserved-free predicate's key can
  never equal a dropped key. Returned capabilities stay `c` (D-39).
- **D-73 B / D-73b** — `typeOfAll` stores `PredExpr.normalize p₀` in the typed `.all` node; the well-typedness
  premise is existential over the source predicate (`∃ p₀, p = normalize p₀ ∧ typeOfPred p₀ … = Bool`,
  plus the lift relation). No re-typing lemma (`typeOfPred (normalize p₀) = typeOfPred p₀` is false,
  D-P9c-12).
- **D-74 interim lifted** — `TypedExpr.SymCCSupported (.all x₁ p _) = x₁.SymCCSupported && p.NoItDependentIn`
  (the honest D-70 A guard); `Opt.lean`'s D-77 completeness lane now covers `.all`.
- **D-79** — `normalize` shares the static-`ite` live branch (`let`) instead of duplicating it; the condition
  is still evaluated first (D-73a).

## Verification
- `lake build Cedar` 648 jobs, 0 errors, 0 `sorry`. `CedarUnitTests` 466/466 (incl. D-98 and the D-99
  REJECT/ACCEPT `#guard`s, which the reviewer confirmed can fail). `CedarSymTests` 1216 → **1220** through cvc5;
  `AnyAll.e2e` 16/16 incl. two `[SymCCOpt]` completeness witnesses (optimized verbs on a `.all` policy, which
  the interim refused).
- Mutation checks (verified, reverted): re-adding the interim `false` breaks the `compile_well_typed` arm /
  completeness test; breaking `normalize`'s `and` fold breaks `normalize_wellTyped` / `normalize_evaluatePred`.
- Reviewer ran BOTH validators (Rust `--features anyall`) on six policy/schema shapes (D-97/D-99 cases, tags,
  nested `it.b.a`): all agree. Rebuilt the Lean FFI lib and ran the DRT differentials ~3 min each under
  `anyall`: validation 53,572 + type-directed validation 53,982 + type-directed eval 77,212 executions,
  0 mismatches.

## Decisions recorded on this branch
D-94 (weak soundness), D-95 (itExpr parity bug, resolved by D-97), D-96 (blocker, resolved by D-97), D-97
(collision-free `it` key + option-(b) invariant), D-98, D-99, and D-P9c-1..13 in PLAN §5.6–§5.10.

## Follow-ups
- D-98 divergence: if Rust ever reserves attribute *names* in the `__cedar` namespace, the Lean check matches
  exactly; until then it is documented as stricter.
- Generator: add the "outer `has` capability + quantifier reading `it.<optional attr>`" shape to the
  Phase 6 type-directed generator so the D-97 parity is fuzzed, not only unit-tested.
- The DRT fuzz binaries report no coverage instrumentation (`new_units_added: 0`); pre-existing.

## Review loop
| Round | Verdict | Notes |
|---|---|---|
| 1 | NO ACTIONABLE FINDINGS | Statement strength checked (invariant real, any-error admission documented and not over-claimed); D-97/D-98/D-99 parity by running both validators + 185k DRT executions, 0 mismatches; D-73b not observable (D-81/D-82 parity definitions); completeness verified with cvc5; D-79 shape covered; counts reproduced; mutations re-applied. Nit-1 (D-98 "Rust refuses" wording) fixed in the close-out; nit-2 merge commits lack the trailer (bookkeeping). |
