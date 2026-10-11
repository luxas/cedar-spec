# Phase 5 PLAN — PART A: the full Lean type rule + soundness for `.all` (`phase5-anyall-symcc`)

**Scope of Part A (this plan):** the Lean validation type rule for `Expr.all` (req 6.1/6.2/6.3)
and its machine-checked soundness proof (req 6.4), i.e. the work D-11 "Full" names and that the
existing `branches/phase5-anyall-symcc/PLAN.md` §6 called the "P0 pre-req". Resolved by the user
on 2026-10-08: **D-11 option 1 (Full type rule), D-33 option 1 (full rule first, then SymCC),
D-37 (lands as Part A of this branch, before Part B SymCC).** Part B (the SymCC bounded-quantifier
encoding) is already planned in `branches/phase5-anyall-symcc/PLAN.md` and is **out of scope here**.

**Deliverable of THIS plan agent:** only this `PLAN-A.md`, committed on branch
`phase5-anyall-symcc` with `git commit -F <msgfile>`. **No implementation.** Tree otherwise clean.

> **BOTTOM LINE UP FRONT.** The full rule is sound and tractable, and smaller than D-11's "~6.5k
> lines / days" worst case, because of one structural fact in the *already-shipped* Phase-2
> evaluator: **`evalAll` collapses every per-element predicate error — including the three
> otherwise-"allowed" errors (`entityDoesNotExist`/`extensionError`/`arithBoundsError`) — into the
> single `quantifierError`** (`Evaluator.lean`: `match … mapM (f v).as Bool with | .error _ =>
> .error .quantifierError`). So a well-typed `.all` evaluates to exactly one of: `ok (bool _)`, a
> *receiver* allowed-error, or `quantifierError`. Therefore `EvaluatesTo` needs **one** new
> disjunct (`quantifierError`), and the predicate's soundness is needed only to show *the element
> result is a Bool-or-error*, never to thread the three allowed errors through the quantifier. That
> is the lever that keeps Part A to a self-contained, non-vacuous rule. See §3.
>
> **CRITICAL DECISION NEEDED: no** (the one-way-door choice D-11/D-33 is already made; the
> decisions proposed below, D-38..D-42, are implementation-shape choices the owner may revisit, not
> go/no-go gates). One **SHOULD-DECIDE-BEFORE-C2** item is flagged in §1 (D-38: typed-predicate
> mirror vs. reserved-placeholder reuse) — it is reversible but changes the proof shape, so the
> implementer should lock it before writing the soundness lemma.

---

## 0. Unavailable tooling this session
`@kirocrew-computer` MCP server was **declared by the agent spec but not configured**; its tools
were unavailable. Nothing else was blocked — all investigation used `shell`/`read`/`git` against
the live tree. (The `work_brief`/`work_report` crew tools also returned `peer_session_mismatch`
this session — a session-binding fault, not a code issue — so this plan is grounded directly in
the user's self-contained task spec and the files read, not in a conductor brief.)

---

## 1. What was read / verified (grounding) and REPRESENTATION DECISION (D-38)

All references are real, read this session, in `/local/home/luxask/code/cedar-spec/cedar-lean`.

### 1.1 The pieces Phase 2 already shipped (the floor we build on)
- **`Cedar/Spec/Expr.lean`** — `inductive PredExpr` (set-free: `item | lit | var | ite | and | or
  | unaryApp | binaryApp | getAttr | hasAttr | extHasAttr | record | call`; **no `set`, no `all`**)
  and `Expr.all (expr : Expr) (pred : PredExpr)`. Hand-written `decPredExpr`/`decExpr` already carry
  the `.all` arm. **No change needed in Part A.**
- **`Cedar/Spec/Value.lean`** — `Error` already has `| quantifierError` (D-10, payload-free).
  **No change needed.** `Value.lt` total order exists (unused by the payload-free error — kept for
  Part B / future diagnostics).
- **`Cedar/Spec/Evaluator.lean`** — `evaluatePred (p) (it : Value) req es` (threads `it`, D-14/the
  Phase-2 OUTCOMES note it was used instead of `PredExpr.instantiate`); `evalAll (s) (f)`:
  ```
  match s.toList.mapM (fun v => (f v).as Bool) with
  | .error _ => .error .quantifierError          -- ANY element error ⇒ one quantifierError
  | .ok bs   => .ok (bs.all id)                  -- conjunction; true on empty
  ```
  and the `.all` arm of `evaluate`:
  ```
  | .all x₁ p => do
      let s ← (evaluate x₁ req es).as (Set Value)  -- non-set receiver ⇒ typeError; receiver error propagates
      evalAll s (fun v => evaluatePred p v req es)
  ```
  **No change needed** — Part A proves this existing evaluator sound against a new type rule.

### 1.2 The validation side that Part A changes
- **`Cedar/Validation/TypedExpr.lean`** — `inductive TypedExpr` has **no `all`**; `TypedExpr.typeOf`,
  `TypedExpr.toExpr`, `TypedExpr.liftBoolTypes`, and `decTypedExpr` all match every constructor and
  will go **non-exhaustive** when `.all` is added. These are in-file edits.
- **`Cedar/Validation/Typechecker.lean`** — `typeOf` currently **rejects** `.all` conservatively:
  `| .all _ _ => .error (.unexpectedType (.bool .anyBool))` (lines ~426-428, D-11 comment). This is
  the single line Part A replaces with the real rule (delegating to a new `typeOfAll`).
- **`Cedar/Validation/Types.lean`** — `CedarType` has `| set (ty : CedarType)` (line 89). The
  receiver type `τ_set` must be a `.set τ`; the element type is that `τ`. The `.bool` type carries a
  `BoolType` (`anyBool`/`tt`/`ff`); the rule returns `.bool .anyBool` (matches how other predicate
  operators return a general bool — see `typeOfUnaryApp .not`).
- **`Cedar/Validation/Levels.lean`** — `TypedExpr.checkLevel` and `TypedExpr.checkEntityAccessLevel`
  match on `TypedExpr`; both need an `.all` arm (D-23 parity: dereferencing `it` is charged the
  level of the receiver's elements).
- **`Cedar/Thm/WellTyped/Expr/Definition.lean`** — `inductive TypedExpr.WellTyped` (the structural
  well-typedness relation SymCC consumes) needs an `.all` constructor; `TypeLifting.lean` and
  `WF.lean` carry matching proof arms.
- **`Cedar/Thm/Validation/Typechecker/Basic.lean`** — `EvaluatesTo` (the 3-allowed-error disjunction)
  and `TypeOfIsSound`. This is the single most load-bearing edit (§2).
- **`Cedar/Thm/Validation/Typechecker.lean`** — `type_of_is_sound` dispatches each `Expr` arm to a
  `type_of_<op>_is_sound` lemma; the `.all` arm currently closes vacuously `simp [typeOf] at h₃`.
  Part A replaces it with `exact type_of_all_is_sound …` and a new sibling file
  `Typechecker/All.lean`.

### 1.3 REPRESENTATION — **D-38 (SHOULD lock before C2).**
Two faithful ways to type the predicate; both are sound, they differ in proof-duplication and in
how closely Lean mirrors the Rust validator (D-21):

- **Option (a) — typed-predicate mirror `TypedPredExpr` + `typeOfPred`.** A parallel annotated
  predicate inductive and a `typeOfPred : PredExpr → CedarType → Capabilities → TypeEnv →
  Except TypeError (TypedPredExpr × Capabilities)` taking the element type as an extra argument,
  with its own per-constructor soundness mirror. **Cost:** duplicates ~every per-operator typing
  lemma for the predicate world (the ~6.5k-line fear in D-11). **Benefit:** `it : τ` is a clean
  extra parameter; no sentinel; capability leakage is structurally impossible (predicate caps live
  in a separate thread, discarded at the quantifier boundary).

- **Option (b) — reuse `typeOf` by substituting `it` with a typed placeholder (MIRRORS RUST D-21).**
  Define `PredExpr.toExpr (it_expr : Expr) : PredExpr → Expr` that maps `.item ↦ it_expr` and every
  other constructor to its `Expr` twin. Type the predicate as `typeOf (p.toExpr it_sentinel) c env'`
  where `env'` extends the context so the sentinel types as the element type `τ`. **This is exactly
  what the Rust validator does** (D-21: a reserved unknown `__cedar::anyall::it` typed as the
  element type, reusing every existing typing rule). **Cost:** needs a way to make a leaf type as
  `τ` — either a reserved `Var`/`Unknown` the environment maps to `τ`, or (cleaner in Lean) a
  dedicated `Expr`/`TypedExpr.lit`-shaped placeholder whose `typeOf` is pinned to `τ`. **Benefit:**
  **zero duplication of per-operator typing lemmas** — the predicate is typed by the *existing*
  `typeOf`, so `type_of_is_sound` *already* proves the predicate's body sound; Part A only needs an
  instantiation lemma relating `evaluate (p.toExpr …)` with `it := v` to `evaluatePred p v`.

- **RECOMMENDATION: Option (b).** It mirrors Rust (so the Phase-6 differential's Rust==Lean on
  `.all` is a like-for-like comparison, req parity §6), and it collapses the dominant proof cost: we
  reuse `type_of_is_sound` for the predicate body instead of re-proving it. The one new lemma it
  needs is the **instantiation/substitution lemma** (§3, Lemma L3) — compared to Option (a)'s full
  predicate-world soundness mirror. The risk in (b) is getting the placeholder's typing and the
  "no capability leak" property right; see §3 and the `it`-capability note below.
  **Decision recorded as D-38 (recommend b).** If (b)'s placeholder proves awkward in Lean's
  `typeOf` (e.g. no clean way to pin a leaf to `τ` without touching `TypeEnv`), fall back to (a) —
  tractable, just larger. The implementer locks this before writing C2.

**How `it` gets type τ, and no-capability-leak (both options).** The element type is `τ` where the
receiver types as `.set τ` (req 6.1). Under (b), the placeholder leaf is the only thing typed as `τ`
inside the predicate; the predicate is typed under the request's capabilities `c` **but the
capabilities it *outputs* are discarded at the quantifier boundary** — `typeOfAll` returns the outer
`c` (or `∅` added), never the predicate's `c'`. This is the structural analogue of req 1.6 (`it`
cannot escape a predicate) and of the Rust rule, and it is also what the soundness proof needs:
`GuardedCapabilitiesInvariant (.all …) c' …` must hold for the *outer* capabilities, and a `.all`
never establishes a `(e,.attr k)` capability about the outside world (its body's `has`-facts are
about `it`, not about `principal`/`resource`). **D-39** records "the predicate's output capabilities
are dropped; `.all` contributes no capability to its enclosing scope."

---

## 2. `EvaluatesTo` extension for `quantifierError` and its ripple

### 2.1 The exact change (`Cedar/Thm/Validation/Typechecker/Basic.lean`)
`EvaluatesTo` today:
```
def EvaluatesTo (e) (request) (entities) (v : Value) : Prop :=
  evaluate e request entities = .error .entityDoesNotExist ∨
  evaluate e request entities = .error .extensionError ∨
  evaluate e request entities = .error .arithBoundsError ∨
  evaluate e request entities = .ok v
```
**Add one disjunct:**
```
  evaluate e request entities = .error .quantifierError ∨      -- NEW (req 6.4)
```
This is the minimal change. Because `quantifierError` is produced **only** by `evalAll` (grep
confirms: `quantifierError` appears solely in `Spec/Value.lean` and `Spec/Evaluator.lean`), adding
the disjunct **cannot change the truth of `EvaluatesTo` for any non-`.all` expression** — those
expressions never produce `quantifierError`, so the new disjunct is simply never the one that holds.
This is the key to bounding the ripple: existing per-operator soundness proofs stay valid; they just
have one more (never-taken) way to be true.

### 2.2 Ripple — every file that case-splits `EvaluatesTo` (per-file estimate)
`EvaluatesTo` is mentioned in **35 files** under `Cedar/Thm/`; of these, the proofs that **destruct**
it (i.e. `rcases`/`cases` into the disjuncts and must now handle a 4th case) are the ones that pay.
Two mitigation facts shrink this:

1. **Most destructs are of a *sub*-expression's `EvaluatesTo`, inside a non-`.all` operator proof.**
   There, the new `quantifierError` disjunct is **discharged by contradiction**: the sub-expression
   is e.g. an `Int`-typed operand, and `evaluate subexpr = .error .quantifierError` contradicts the
   IH's `InstanceOfType`. A one-line `| .error .quantifierError => …` arm (often `simp`/`exact
   absurd`) per destruct site.
2. The destructs cluster in the per-operator soundness lemmas and a few shared helpers.

**Per-file estimate (files that `cases`/`rcases` `EvaluatesTo` and need a new arm):**

| File / area | ~ destruct sites | Nature of the new arm |
|---|---|---|
| `Typechecker/Basic.lean` | 1 (the def) + helpers | the def change itself; `CapabilitiesInvariant`/`GuardedCapabilitiesInvariant` are stated over `EvaluatesTo` and gain the case trivially |
| `Typechecker/IfThenElse.lean` | ~3-4 | condition/branch sub-exprs: `quantifierError` on a `Bool`-typed cond contradicts IH |
| `Typechecker/And.lean`, `Or.lean` | ~2 each | operand is `Bool`-typed ⇒ contradiction |
| `Typechecker/UnaryApp.lean` | ~2 | operand typed ⇒ contradiction |
| `Typechecker/BinaryApp.lean` | ~4-6 | two operands; several op-specific sub-lemmas |
| `Typechecker/GetAttr.lean`, `HasAttr.lean`, `ExtHasAttr.lean` | ~2 each | receiver typed ⇒ contradiction |
| `Typechecker/Set.lean`, `Record.lean`, `Call.lean` | ~2 each | list elements typed ⇒ contradiction |
| `Typechecker/LitVar.lean` | 0-1 | lits/vars never error |
| `Thm/Validation/Validator.lean` | ~2 | `EvaluatesToBool` (`request_is_authorized`-style) gains the `quantifierError` case; a policy that quantifier-errors is a **non-permit** (the error ≠ `.ok true`), consistent with existing allowed-error handling |
| `Thm/Validation/Slice/**`, `Levels/**` | ~1-3 total | these reason about `EvaluatesTo` of reachable subterms; same contradiction pattern |
| `Thm/Typechecking.lean`, `Thm/SymCC/WellTyped.lean` | re-export/statement only | no destruct; recompile only |

**Total estimate: ~25-40 small arms across ~12-15 files, each 1-4 lines**, plus the one real new
proof in the new `Typechecker/All.lean` (§3). This is the "touches every proof that destructs it"
D-11 warned about, but each touch is mechanical because the new case is *vacuous for every operator
except `.all`*. A single reusable lemma helps:
```
theorem evaluatesTo_quantifierError_absurd {e v ty env req es} :
  InstanceOfType env v ty → ty ≠ /*any type .all can't produce under this op*/ →
  evaluate e req es = .error .quantifierError → ... → False
```
— but more practically, the shared helper is "`EvaluatesTo` of a typed operand is not
`quantifierError` unless the operand *is* an `.all`", provable because `quantifierError` ⇒ the
expression's head is `.all` (a small lemma `quantifierError_implies_all`: `evaluate e … = .error
.quantifierError → ∃ x p, e = .all x p`, by cases on `evaluate`). **D-40** records this helper as the
ripple-shrinker: prove `quantifierError_implies_all` once; every operator proof uses it to kill the
new disjunct in one line.

---

## 3. Soundness argument for `.all` (the one real new proof — `Typechecker/All.lean`)

**Statement** (mirrors `type_of_<op>_is_sound`):
```
theorem type_of_all_is_sound {x₁ : Expr} {p : PredExpr} {c₁ c₂ : Capabilities} {env : TypeEnv}
    {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (.all x₁ p) c₁ env = .ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)                         -- receiver IH
  (ihₚ : /* predicate IH, see below */) :
  GuardedCapabilitiesInvariant (.all x₁ p) c₂ request entities ∧
  ∃ v, EvaluatesTo (.all x₁ p) request entities v ∧ InstanceOfType env v ty.typeOf
```

**The rule `typeOfAll`** (new, in `Typechecker.lean`): typecheck the receiver; require its type to be
`.set τ`; type the predicate with `it : τ` (per D-38); require the predicate's type to be `.bool _`;
return `(TypedExpr.all tReceiver tPred (.bool .anyBool), c₁)`. A non-set receiver ⇒ `.unexpectedType`;
a non-bool predicate ⇒ `.unexpectedType` (D-16: at *evaluation* a non-bool predicate is a
`quantifierError`, but at *typing* it is a type error — the validator rejects it, matching Rust).
A set-typed subterm in the predicate is already impossible structurally (`PredExpr` has no `set`); the
remaining set-valued leaks (`it` itself being a set is impossible since `it : τ` is the *element*
type, not the receiver type; set-returning ops are absent from `PredExpr`) — so **req 1.5 is
discharged structurally in Lean**, unlike Rust where it needs the `SetTermInQuantifier` runtime check
(D-19). Record this parity nuance as **D-41** (Lean needs no `SetTermInQuantifier` analogue; the type
is the proof).

**Proof skeleton (3 steps, 3 named lemmas):**

1. From `h₃` + `ih₁`: the receiver `x₁` `EvaluatesTo` a value `vs` with `InstanceOfType env vs
   (.set τ)`. By inversion of `InstanceOfType` on a set type, `vs = .set s` for some `Set Value`
   whose every element `v ∈ s` satisfies `InstanceOfType env v τ`.  — **Lemma L1
   (`instanceOfType_set_inv`)**: already essentially present for `contains`/`containsAll` typing;
   reuse `Thm/Validation/Typechecker/Types.lean` set lemmas. The receiver's allowed-errors
   (`entityDoesNotExist`/…) are handled first: if the receiver errors, `evaluate (.all …)` is that
   same allowed-error (the `← …as (Set Value)` bind propagates it), so `EvaluatesTo` holds by the
   receiver's own disjunct. The main case is receiver `= .ok (.set s)`.

2. **Per element `v ∈ s`, the predicate at `v` is well-typed Bool, hence evaluates to a Bool or an
   error.**  — **Lemma L2 (predicate soundness under `it := v`)**. Under D-38(b) this is *not a new
   induction*: `evaluatePred p v req es = evaluate (p.toExpr itₑ) req es` with `it` bound to `v`
   (Lemma L3), and the predicate's `.toExpr` is typed by the ordinary `typeOf` that
   `type_of_is_sound` already proves sound — so `evaluate (p.toExpr …)` is `ok (bool _)` or an
   allowed error. Under D-38(a) this is the predicate-world `type_of_pred_is_sound` mirror.
   - **Lemma L3 (`evaluatePred_eq_evaluate_instantiate`)**: `evaluatePred p v req es = evaluate
     (p.toExpr (itPlaceholderValue v)) req es`, by structural induction on `PredExpr` (one arm per
     constructor; `.item ↦ the bound value`). This is the bridge between the evaluator's
     `it`-threading (what Phase 2 shipped) and the typing-by-substitution (what D-38(b) uses). **This
     is the single genuinely new structural induction in Part A** and is the riskiest proof (§8).

3. **`evalAll` folds to Bool-or-`quantifierError`.** Given step 2 (every element's predicate result
   is `ok (bool _)` or an error), `evalAll s f = match s.toList.mapM (f ·).as Bool with | .error _
   => quantifierError | .ok bs => ok (bs.all id)`. Either some element's `.as Bool` is `.error`
   (⇒ `quantifierError`, covered by the new `EvaluatesTo` disjunct) or all succeed (⇒ `ok (bool
   (bs.all id))`, `InstanceOfType env (bool _) (.bool .anyBool)`). — **Lemma L4
   (`evalAll_ok_bool_or_quantifierError`)**: the Phase-2 OUTCOMES already lists helpers
   `evalAll_ok_bool` and `all_produces_bool`; L4 extends them to the error branch. Note the
   `.as Bool` masking means a predicate that returns a non-bool (D-16) *also* lands in the `.error`
   branch ⇒ `quantifierError`, exactly matching the type rule rejecting non-bool predicates being the
   only thing that keeps us out of that branch for *well-typed* input — i.e. for well-typed `.all`
   the non-bool case cannot arise from a type-correct predicate, but the fold still handles it
   soundly.

**Capabilities.** `GuardedCapabilitiesInvariant (.all x₁ p) c₂ …`: `c₂ = c₁` (D-39, predicate caps
dropped), and `.all` never evaluates to a `hasAttr`-shaped capability witness, so the invariant is
inherited from the input `h₁` — a 2-3 line discharge, like `unaryApp .not`.

**Well-formedness hypothesis.** `evalAll`'s doc-comment (Phase 2) warns any soundness lemma needs the
set to be well-formed (canonical, order-independent). `vs = .set s` from a sound receiver *is*
`Set.make`-canonical (the evaluator's `.set` arm uses `Set.make`; `InstanceOfType` on a set carries
`Set.WellFormed`). L4 takes that WF hypothesis; it is available from L1. Record as **D-42**: the
soundness of `.all` is conditioned on receiver-set well-formedness, which holds for every value the
evaluator produces (so it is not an extra runtime assumption).

---

## 4. Levels and other `typeOf`-derived validators needing an `.all` case

- **`Cedar/Validation/Levels.lean`** — `TypedExpr.checkLevel` and `TypedExpr.checkEntityAccessLevel`
  get an `.all` arm: recurse into the receiver at the current level, and into the typed predicate
  charging `it`-dereference at the **level of the receiver's elements** (D-23 parity). The matching
  proof files under `Cedar/Thm/Validation/Levels/` (there are per-operator Levels soundness files:
  `And.lean`, `Or.lean`, `GetAttr.lean`, `HasAttr.lean`, `IfThenElse.lean`, `ExtHasAttr.lean`,
  `NoEntitiesError.lean`, …) each gain an `.all` case; most are "recurse + the new EvaluatesTo arm is
  vacuous" (same §2 pattern). A new `Levels/All.lean` sibling holds the real `.all` level-soundness
  lemma. **Estimate: ~1 arm per Levels file (~8 files) + 1 new file.**
- **`Cedar/Validation/EnvironmentValidator.lean`** (4 TypedExpr matches) and
  **`RequestEntityValidator.lean`** (1) — add `.all` arms; these walk `TypedExpr` for entity/request
  validation and mirror the Phase-3 Rust "validator entity/text walks see predicate leaves" (Phase-3
  OUTCOMES / `checkPredEntities`). The Lean side already has `PredExpr.entityUIDs` and
  `checkPredEntities` from Phase 2 — reuse them in the `.all` arm.
- **`Cedar/Validation/Subtyping.lean`** (1), **`Types.lean`** (1) — recompile; add an `.all` arm only
  if they match `TypedExpr` exhaustively (quick grep says one match site each; likely a `typeOf`-only
  use needing no arm, confirm during implementation).

---

## 5. Downstream `TypedExpr` matches that become non-exhaustive (placeholder arms until Part B / Phase 6.5)

Adding `TypedExpr.all` makes every exhaustive `match` on `TypedExpr` fail to compile. The implementer
MUST add an arm to each. Those **owned by later phases** get an explicit placeholder (NOT a silent
catch-all) so Part A stays green without pretending to implement Part B / TPE:

| File | Owner phase | Part-A arm |
|---|---|---|
| `Cedar/TPE/Residual.lean` (13 match sites — `Residual` mirrors `TypedExpr`; `Residual.from_expr`, `.evaluate`, `.typeOf`, `.allLiteralUIDs`, `decResidual`, …) | **Phase 6.5 (TPE)** | add `ResidualKind.all`? **No** — per req 7.4 TPE is a late commit. Part A adds the **minimal** arm needed to compile: `Residual.from_expr` on a `TypedExpr.all` produces a residual `.all` placeholder OR, if `Residual` need not cover `.all` yet, a documented `.error`/`unsupported` residual. **D-43 candidate** (see §7): decide whether Part A adds a real `Residual` `.all` constructor or a stub. Recommend: a stub residual arm that keeps the whole `.all` residual (matches D-17), deferring real per-element TPE to 6.5. |
| `Cedar/TPE/Evaluator.lean` (4) | Phase 6.5 | mirror the Residual stub |
| `Cedar/Thm/SymCC/Compiler.lean` (6), `Compiler/WF.lean` (6) | **Part B (SymCC)** | these are proofs *about* `compile`, which rejects `.all` (`SymCC/Compiler.lean:324 | .all _ _ => .error .unsupportedError`). The `TypedExpr.all` arm here is a **vacuous/`unsupportedError`-justified** case until Part B. Note: SymCC's `compile` matches on **`Expr`**, not `TypedExpr`, so the SymCC *compiler* itself is unaffected by adding `TypedExpr.all`; it is the SymCC **well-typedness/WF proofs** (`Thm/SymCC/*`) that reference `TypedExpr` and need the arm. |
| `Cedar/Thm/SymCC/WellTyped.lean`, `ValidRefs.lean`, `Env/ofEnv.lean`, `Opt/AllowDeny.lean` | Part B | `.all` arm consistent with the new `TypedExpr.WellTyped .all` constructor; vacuous where they only need the shape |
| `Cedar/Thm/WellTyped/Expr/TypeLifting.lean` (2), `WF.lean` | **Part A** (these ARE the well-typedness proofs) | real `.all` arm proving `liftBoolTypes` preserves well-typedness and the WF invariant |

**Principle (D-40 extended):** a Part-A arm for a *later-phase* function is either (i) a faithful
stub that preserves that phase's documented interim behavior (TPE: whole-node residual, D-17) or (ii)
a vacuous case justified by `compile` rejecting `.all` (SymCC, until Part B). **No `_ => sorry`, no
silent wildcard** — every arm is explicit and either real or justified-vacuous, so `#print axioms`
stays clean and a future phase cannot forget an arm. Record which arms are stubs in that commit's
message.

---

## 6. Rust parity (so the Phase-6 validation differential can require Rust == Lean on `.all`)

The Phase-3 Rust validator (OUTCOMES, commits `78c79bc5`/`05adec3d`) is the reference. Part A's Lean
rule MUST decide `accept`/`reject` identically to it on:

| Case | Rust (Phase 3) | Lean (Part A) | Match? |
|---|---|---|---|
| receiver not a set | reject (`expected set`) | `typeOfAll` requires `.set τ` ⇒ `.unexpectedType` | ✅ |
| predicate not Bool under `it:τ` | reject (type error) | `typeOfAll` requires predicate `.bool _` ⇒ `.unexpectedType` | ✅ |
| set-typed subterm in predicate (req 1.5) | reject (`SetTermInQuantifier` runtime check, D-19) | **structurally impossible** (`PredExpr` has no `set`/set-ops) ⇒ no runtime check (D-41) | ✅ accept/reject agree; **mechanism differs** (flag below) |
| `it` typed as element type | reserved placeholder unknown typed as element type (D-21) | D-38(b) mirrors this exactly; D-38(a) uses an explicit `it:τ` param | ✅ (b) is like-for-like |
| element type unknown (empty-set / AnyType) | follows `contains` treatment (req 6.3) | same: `typeOfAll` reuses the existing set-element-type handling | ✅ |
| levels: `it`-deref charged element level | D-23 | §4 mirrors D-23 | ✅ |

**Intended divergence (must be whitelisted in the Phase-6 differential, not treated as a bug):**
- **Mechanism of req 1.5.** Rust *detects* a set-term and raises `SetTermInQuantifier`; Lean makes it
  *unrepresentable*. Both reject the same policies, but the Rust path can emit a distinct error code.
  The differential compares *accept vs reject*, not error codes, so this is fine — **D-41** flags it.
- **D-24 (Rust cascade errors).** When the Rust receiver is a non-set, it still typechecks the
  predicate with `it : Never`, possibly adding cascade errors; Lean can short-circuit at the
  non-set receiver. Both reject; error *sets* differ. Already OPEN in DECISIONS (D-24); the
  differential must compare reject-ness, not error multiplicity.
- **D-16/D-22.** Non-bool predicate ⇒ quantifierError at eval (both); `RecursionLimit` inside a
  predicate propagates in Rust with no Lean counterpart (D-22, OPEN) — an *eval* differential item,
  not a *validation* one, so out of Part A's scope but noted for Phase 6.

---

## 7. Logical commit breakdown (each green, no `sorry`, non-vacuous tests)

Green-check preamble (every commit):
```
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"
unset LD_PRELOAD; export LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar
cd cedar-lean
lake build Cedar.Validation.Typechecker   # fast while iterating
lake build Cedar                          # full, before each commit
# CedarUnitTests exe (D-13 host quirk): needs LIBRARY_PATH at the toolchain libs
LIBRARY_PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/lib:$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean \
  lake build CedarUnitTests && .lake/build/bin/CedarUnitTests   # run it; assert count>0
grep -rn "sorry" Cedar/Validation Cedar/Thm/Validation Cedar/Thm/WellTyped   # must be empty
# axiom check:
echo '#print axioms Cedar.Thm.type_of_is_sound' | ... (via a scratch Lean file importing the Thm)
```

- **C1 — `TypedExpr.all` + the type rule `typeOfAll`, replace the conservative reject.**
  `Validation/TypedExpr.lean` (`.all` constructor; `.all` arms in `typeOf`/`toExpr`/`liftBoolTypes`/
  `decTypedExpr`), `Validation/Typechecker.lean` (new `typeOfAll`, replace line ~428). Green: `lake
  build Cedar.Validation`. *No proofs yet; this breaks `Thm/*` exhaustiveness — so C1 and C2 may need
  to land together to keep `lake build Cedar` green. If so, merge C1+C2.* Decide at implementation.
- **C2 — the ripple: `EvaluatesTo` + the `quantifierError_implies_all` helper + every vacuous arm.**
  `Thm/Validation/Typechecker/Basic.lean` (the disjunct), `Thm/Validation/Typechecker/*.lean` (per-op
  vacuous arms), `Thm/Validation/Validator.lean`, `Slice/**`, and the `type_of_is_sound` `.all` arm
  wired to the new lemma. Green: `lake build Cedar` (everything except the real `.all` lemma may be
  stubbed with the IH plumbing but NOT `sorry` — if a stub is unavoidable mid-commit, keep C2 and C3
  as one commit). *Likely C1+C2+C3 are one atomic commit* because the inductive `type_of_is_sound`
  cannot be green with a `.all` arm that calls an unproven lemma. Plan for **one big "type rule +
  soundness" commit** and split only if a clean intermediate green exists.
- **C3 — `Typechecker/All.lean`: `type_of_all_is_sound` + L1-L4.** The real proof (§3). Green: `lake
  build Cedar`; `#print axioms type_of_is_sound` shows only the standard axioms (no `sorryAx`).
- **C4 — WellTyped + Levels.** `Thm/WellTyped/Expr/Definition.lean` (`.all` WellTyped constructor),
  `TypeLifting.lean`, `WF.lean`; `Validation/Levels.lean` + `Thm/Validation/Levels/All.lean` + the
  per-file Levels arms; `EnvironmentValidator.lean`/`RequestEntityValidator.lean` arms. Green: `lake
  build Cedar`.
- **C5 — downstream placeholder arms (TPE / SymCC-proof exhaustiveness).** §5 stubs/vacuous arms, each
  documented in the commit message as "placeholder until Phase 6.5 / Part B." Green: `lake build
  Cedar`. (**D-43**: whether `Residual` gets a real `.all` constructor now or a stub — recommend
  stub, whole-node residual per D-17.)
- **C6 — non-vacuous unit tests.** `UnitTest/AnyAll.lean` (extend the Phase-2 file) with **validator**
  cases: accept `ports.all(it >= 8000)` where `ports : Set Long` ⇒ `Bool`; accept
  `owners.all(it.dept == "eng")` (set of records); **reject** non-set receiver; **reject** non-bool
  predicate (`it + 1`); empty-set-type / AnyType element follows `contains` (req 6.3). Assert the
  typechecker's accept/reject verdict AND that `CedarUnitTests` runs these (count > 0, non-vacuous
  per the learned rule). Green: run `CedarUnitTests`, report "N anyall-validation tests run".

**Mutation checks (the learned non-vacuous rule — each MUST make a named test fail):**
1. **Drop the Bool check** in `typeOfAll` (accept a non-bool predicate) ⇒ the "reject `it + 1`" test
   must fail, AND `type_of_all_is_sound` must no longer compile (L4 relies on the predicate being
   bool-typed to land in the `ok` branch — a non-bool well-typed predicate would need the
   `quantifierError` branch, which `InstanceOfType … (.bool …)` cannot satisfy). Show both.
2. **Drop the Set-receiver check** (accept a non-set receiver) ⇒ the "reject non-set receiver" test
   fails AND L1 (`instanceOfType_set_inv`) is unprovable ⇒ `type_of_all_is_sound` fails to build.
3. **Leak the `it` capability** (return the predicate's output capabilities `c'` from `typeOfAll`
   instead of `c₁`) ⇒ construct a test where `it has a` inside the predicate must NOT establish a
   capability outside: a policy `ctx.set.all(it has a) && principal has a` must still require the
   second `has` (not be elided by a leaked capability). Assert this policy's typing/behavior; the
   leak makes the capability-invariant case of `type_of_all_is_sound` fail to build (the
   `GuardedCapabilitiesInvariant` discharge needs `c₂ = c₁`).

Each mutation is applied, the build/test failure is recorded, then reverted — exactly the Phase-2/3
mutation discipline.

---

## 8. Effort, riskiest proof, fallback

**Effort estimate.** Smaller than D-11's worst case *if* D-38(b) is used (reuses `type_of_is_sound`
for the predicate body). Rough: C1-C3 (type rule + ripple + soundness) ≈ **2-3 focused days**; C4
(WellTyped+Levels) ≈ **1 day**; C5 (downstream stubs) ≈ **0.5 day**; C6 (tests+mutation) ≈ **0.5
day**. **~4-5 days total**, dominated by C2's ripple breadth and L3's induction. Under D-38(a) add
~2-3 days for the predicate-world soundness mirror.

**Riskiest proof: Lemma L3 (`evaluatePred_eq_evaluate_instantiate`)** — the bridge between the
evaluator's `it`-threading (Phase-2 reality) and the typing-by-`toExpr`-substitution (D-38(b)). Risks:
(i) `PredExpr.toExpr`'s placeholder for `.item` must evaluate to *exactly* the bound value `v` with no
re-encoding loss (records/ext/entity elements, per design §3) — a `Value → Expr` round-trip must be
the identity under `evaluate`; (ii) the induction has a `record`/`call` list-recursion arm needing a
`mapM` congruence lemma. If (i) is awkward, use the **direct** `it ↦ Value` binding form (bind the
value into the environment or a `Value`-carrying placeholder leaf) so no `Value → Expr → Value`
round-trip is needed — the design explicitly prefers this ("thread an `it ↦ Value` binding … avoiding
the Value→Expr round-trip").

**Fallback if a proof is intractable (NEVER weaken soundness, NEVER `sorry`):**
- If D-38(b)'s L3 is intractable, switch to **D-38(a)** (typed-predicate mirror): more code, but each
  predicate operator's soundness is a direct copy of its `Expr` twin — mechanical, not clever.
- If even (a)'s full mirror is too large to finish in budget, the *sound* fallback is **narrow the
  type rule, not the proof**: accept `.all` only when the predicate is in a provable sub-fragment
  (e.g. predicates whose body is already covered), rejecting the rest conservatively. This stays
  sound (rejecting is always sound) and non-vacuous (the accepted fragment has real tests), and it is
  strictly better than D-11's "reject everything." It would be recorded as a scoped interim with a
  follow-up to widen. **It must never be a `sorry` or a weakened `EvaluatesTo`/`InstanceOfType`.**

---

## Proposed new decisions (record in DECISIONS.md as D-38.. — DO NOT edit DECISIONS.md here)

- **D-38 (predicate representation).** Type the predicate by **reusing `typeOf` on
  `PredExpr.toExpr` with `it` bound to a typed placeholder (option b), mirroring the Rust D-21
  reserved-unknown approach** — it eliminates the ~6.5k-line per-operator predicate-soundness
  duplication by reusing `type_of_is_sound` for the body, and makes the Phase-6 Rust==Lean
  differential like-for-like. Fallback to a `TypedPredExpr` mirror (option a) if the placeholder's
  Lean typing is awkward. SHOULD be locked before writing the soundness commit.
- **D-39 (no capability leak).** `typeOfAll` returns the enclosing capabilities (predicate output
  capabilities are dropped at the quantifier boundary); `.all` contributes no capability to its
  scope. This both matches req 1.6's "`it` cannot escape" and is required by the
  `GuardedCapabilitiesInvariant` discharge.
- **D-40 (ripple shrinker).** Prove `quantifierError_implies_all` once (`evaluate e … = .error
  .quantifierError → ∃ x p, e = .all x p`); every non-`.all` operator proof uses it to discharge the
  new `EvaluatesTo` disjunct in one line. Downstream exhaustiveness arms for later-phase functions are
  explicit stubs or `compile`-rejects-justified vacuous cases — never `sorry`, never a silent
  wildcard.
- **D-41 (req 1.5 mechanism differs Rust vs Lean).** Lean enforces "no set term in predicate"
  **structurally** (`PredExpr` has no `set`/set-ops), so it has no `SetTermInQuantifier` analogue;
  Rust uses a runtime check (D-19). Accept/reject verdicts agree; the Phase-6 differential compares
  reject-ness, not error codes.
- **D-42 (well-formedness hypothesis).** `.all` soundness is conditioned on the receiver set being
  well-formed/canonical, which holds for every value the evaluator produces (`Set.make`); it is a
  proof hypothesis, not a new runtime assumption.
- **D-43 (TPE stub scope).** Part A adds only the minimal `Residual`/TPE exhaustiveness arm (whole-node
  residual, consistent with D-17); real per-element TPE for `.all` stays a Phase-6.5 late commit (req
  7.4).

---

### 5-line summary
1. The user resolved D-11/D-33/D-37 to **implement the full Lean type rule + soundness for `.all`
   first** (Part A), before the SymCC encoding (Part B, already planned in `PLAN.md`). This plan
   specifies Part A only; its sole deliverable is this committed `PLAN-A.md`.
2. The decisive simplifier: the shipped `evalAll` **collapses every per-element predicate error into
   one `quantifierError`**, so `EvaluatesTo` needs exactly **one** new disjunct and the predicate's
   three "allowed" errors never thread through the quantifier — the ripple is ~25-40 *mechanical*
   vacuous arms across ~12-15 files, shrunk further by a `quantifierError_implies_all` helper (D-40).
3. Recommended representation is **D-38(b): type the predicate by reusing `typeOf` on
   `PredExpr.toExpr` with `it` as a typed placeholder**, mirroring the Rust D-21 reserved-unknown
   rule and reusing `type_of_is_sound` for the body (avoids the ~6.5k-line predicate-soundness
   mirror); the one genuinely new structural induction is Lemma L3 (`evaluatePred` ↔ instantiated
   `evaluate`), the riskiest proof, with a sound fallback (D-38(a), then a narrowed-but-sound rule —
   never `sorry`, never a weakened invariant).
4. Rust/Lean parity holds on all accept/reject cases (non-set receiver, non-bool predicate, set-term,
   element-type, levels); the only intended divergences are **mechanism**, not verdict (D-41: Lean
   makes set-terms unrepresentable vs Rust's `SetTermInQuantifier`; D-24 cascade errors), to be
   whitelisted in the Phase-6 differential as "compare reject-ness, not error codes."
5. Six commits (type rule + ripple + soundness likely one atomic commit; then WellTyped/Levels;
   downstream TPE/SymCC-proof placeholder arms; non-vacuous validator unit tests with three mutation
   checks — drop-Bool, drop-Set, leak-`it`-capability — each required to break a named test and the
   build); ~4-5 days; green = `lake build Cedar` + `CedarUnitTests` run (count>0) + no `sorry` +
   clean `#print axioms`.

CRITICAL DECISION NEEDED: no — the one-way-door choice (D-11 Full rule) is already made by the user;
D-38..D-43 are reversible implementation-shape decisions (D-38, which predicate representation, SHOULD
be locked before the soundness commit but is not a go/no-go gate).
