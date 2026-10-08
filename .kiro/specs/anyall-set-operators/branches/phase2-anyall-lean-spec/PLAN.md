# Phase 2 Plan — Lean spec node + evaluator (`phase2-anyall-lean-spec`)

Branch `phase2-anyall-lean-spec` (off Phase 1 `fca202a`, which carries the Phase-1 Rust
OUTCOMES). **Scope: `cedar-lean/` only** — the Lean definitional spec surface. No Rust, no DRT,
no surface syntax. This plan is grounded in the files read on 2026-10-08 (paths below are the
real ones; spec line numbers in tasks.md may be stale and were re-derived here).

Implements spec tasks **T2.1, T2.2, T2.3** (`tasks.md` §"Phase 2 — Lean spec node + evaluator").

---

## Goal

Add the universal set-quantifier node to the Lean spec so `lake build Cedar` stays green with
the new constructor present, and so the definitional evaluator computes `expr.all(pred)` with
the deterministic, no-early-false-short-circuit `QuantifierError` semantics required by RFC 0021
(and mirrored from the Phase-1 Rust node). Concretely:

1. `Error.quantifierError` added to the Lean error type.
2. A restricted, set-free, non-nested predicate inductive `PredExpr`.
3. `Expr.all (e : Expr) (p : PredExpr)` — the single new `Expr` constructor. **Lean has no
   `any`** (just as Lean `BinaryOp` has `less`/`lessEq` but no `greater`/`greaterEq`: the Rust
   `ExprBuilder` lowered `>`/`>=` and `any`→`!all(!p)` *before* the AST crosses into Lean via
   DRT, so the Lean spec only ever receives `all`).
4. An `evaluate` arm: receiver must be a `Set`; bind each element (a full `Value`) to `it`;
   instantiate+evaluate the predicate; fold with **no early short-circuit on `false`**;
   deterministic order-independent `quantifierError`; empty set ⇒ `true`.
5. The downstream total-`Expr` matches the new constructor forces to cover, each kept green with
   either the real rule (evaluator) or a conservative arm (typechecker / SymCC compiler / TPE),
   per the spec's phase ordering.

Mirrors Phase-1 Rust shape (`phase1-anyall-rust-ast/OUTCOMES.md`): node for `expr.all(pred)`
over element keyword `it`; `pred` is a restricted set-free non-nested predicate; `it` binds a
full `Value` at eval time; every exhaustive-match site that the node forces to cover gets a
*conservative* arm (reject/typeError) rather than a silent pass, where the real behavior belongs
to a later phase.

---

## Files to touch (exact grounded paths, all under `cedar-lean/`)

### Definitely touched in Phase 2

| File | Why | Task |
|---|---|---|
| `Cedar/Spec/Value.lean` | add `Error.quantifierError`; it has `deriving instance Repr, DecidableEq for Error` (auto-extends, no hand-written arm). | T2.1 |
| `Cedar/Spec/Expr.lean` | add `inductive PredExpr`; add `Expr.all` constructor; extend the **hand-written** `decExpr` (`DecidableEq Expr`); add a hand-written `DecidableEq`/`Repr`/`Inhabited` for `PredExpr`. `Expr` uses `deriving Repr, Inhabited` (auto) but a **hand-written `decExpr`** (needs an `all.all` arm). | T2.1, T2.2 |
| `Cedar/Spec/Evaluator.lean` | the `evaluate` match is **total, no catch-all** (read: arms `.lit`…`.call`, lines 114–153) → forces an `.all` arm. Add `evalAll` + `PredExpr` instantiation/evaluation. | T2.2 |

### Forced green-keeping arms (constructor breaks a total `Expr` match) — Phase 2 must add *something*

Lean has no `#[cfg]`: once `Expr.all` exists, **every total match on `Expr` with no catch-all
stops compiling** until it has an `all` arm. These are the Lean analogue of the Phase-1 Rust
exhaustive-match sweep (`ExprKind` arms + `tpe/residual.rs`, `proto/ast.rs`, etc.). Each gets the
*minimal* arm that keeps `lake build Cedar` green; the *real* behavior lands in the phase named.

| File | Match | Phase-2 minimal arm | Real behavior |
|---|---|---|---|
| `Cedar/SymCC/Compiler.lean` | `def compile` (lines 287+) is a **total `Expr` match, no catch-all** (confirmed: last arm is `.getAttr`, no `| _ =>`). | conservative `.error .unsupportedError`-style arm (reject `all`). | **Phase 5** (T5.1): bounded conjunction over the symbolic set. |
| `Cedar/Validation/Typechecker.lean` | `def typeOf` (lines 387+) is a **total `Expr` match, no catch-all** (confirmed: arms `.lit`…`.call`, no `| _ =>`). | the **real sound type rule** (T2.3 asks for it) *or*, if the `TypedExpr` mirror work is deferred, a conservative `.error`. See Decision 4. | T2.3 (type rule) / Phase 3 (Rust validator parity). |

### Possibly touched — depends on Decisions 2 & 4 (mirror inductives)

The Lean validation/TPE pipeline does **not** route everything through one `evaluate`-style
match. There are **three mirror inductives of `Expr`**, each with its own hand-written
`DecidableEq` and `toExpr`-style lowering:

- `Cedar/Spec/Expr.lean` — `Expr` (hand-written `decExpr`).
- `Cedar/Validation/TypedExpr.lean` — `TypedExpr` (hand-written `decTypedExpr`, `TypedExpr.toExpr`,
  `TypedExpr.typeOf`); the typechecker *produces* this.
- `Cedar/TPE/Residual.lean` — `Residual` (hand-written machinery, `TypedExpr.toResidual`,
  `Residual.evaluate`); TPE *produces* this.

Whether `TypedExpr` and `Residual` need an `all` constructor in Phase 2 is **Decision 4**: they
only need one if `typeOf` returns a typed `all` (rather than conservatively erroring) in Phase 2.
TPE is explicitly **Phase 6.5** in `tasks.md`, so `Residual` is out of Phase-2 scope *unless* a
total `Residual`/`TypedExpr` match elsewhere breaks on the new `Expr` arm — it does not, because
`Residual`/`TypedExpr` are built *from* `Expr` by functions we control, not by a forced total
match. The TPE residual arm is therefore deferred to Phase 6.5 as tasks.md sequences it.

### NOT touched in Phase 2 (deferred, by tasks.md ordering)

- `Cedar/TPE/*` — Phase 6.5 (TPE residual `all`).
- `Cedar/Validation/Levels.lean` — `checkLevel`/`checkEntityAccessLevel` match on **`TypedExpr`**,
  not `Expr`, and only break once `TypedExpr` gains an `all` ctor (Decision 4 / T2.3). If T2.3
  adds `TypedExpr.all`, these two `TypedExpr` matches (lines 57, 148) must get an arm too.
- `Cedar/Thm/**` structural proofs — the heavy proof repair is **T2.3**; see "Proofs that must
  stay green" for exactly which proof trees the new constructor forces.

---

## Task breakdown (logical commits — each keeps `lake build Cedar` green)

The ordering is chosen so no intermediate commit leaves `lake build Cedar` red. Because the
*constructor itself* breaks total matches, the constructor and the forced green-keeping arms land
in the **same commit** (C2) — you cannot add `Expr.all` and defer the `evaluate`/`typeOf`/`compile`
arms to a later commit, or the build between commits is red.

- **C1 — `Error.quantifierError` (T2.1, isolated).**
  `Cedar/Spec/Value.lean`: add `| quantifierError` to `inductive Error`. `Error` has
  `deriving instance Repr, DecidableEq for Error`, so no hand-written arm; this is a safe,
  self-contained commit that builds green on its own (nothing matches `Error` totally in a way a
  new variant breaks — error consumers use it, they don't exhaustively deconstruct it).
  _Green:_ `lake build Cedar`.

- **C2 — `PredExpr` + `Expr.all` + ALL forced green-keeping arms (T2.1 + T2.2 structural).**
  One commit, because the constructor breaks total matches that must be fixed atomically:
  - `Cedar/Spec/Expr.lean`: `inductive PredExpr` (set-free, see Decision 2) with hand-written
    `DecidableEq`/`Repr`/`Inhabited`; `Expr.all (e : Expr) (p : PredExpr)`; extend `decExpr` with
    the `all.all` arm (compares `e` via `decExpr` and `p` via `PredExpr`'s decEq).
  - `Cedar/Spec/Evaluator.lean`: `evalAll` + `PredExpr` instantiation/eval + the `.all` arm
    (the real semantics — Decision 3).
  - `Cedar/SymCC/Compiler.lean`: conservative reject arm in `compile`.
  - `Cedar/Validation/Typechecker.lean`: `typeOf` arm — real rule or conservative (Decision 4).
  _Green:_ `lake build Cedar`.

- **C3 — Lean spec unit tests (T2.2 green check).**
  Add Lean tests (in `cedar-lean`'s test target — locate the existing `Spec`/evaluator test file
  pattern before writing) for 2.1/2.2/2.5/2.7 **plus** the load-bearing regression:
  `[false-element, erroring-element].all(..)` must yield `quantifierError`, **not** `false`
  (req 2.8 — the no-early-short-circuit property). Show the tests RUN (count > 0) and that the
  2.8 test FAILS if the fold is reverted to short-circuit on first `false` (non-vacuity, per the
  retained lesson).
  _Green:_ `lake build Cedar` + the test target.

- **C4 — Structural proof repair (T2.3).**
  Add the `all` case everywhere a `Thm/` proof recurses over `Expr`, and prove the sound type
  rule (req 6.1/6.4): `e : Set τ` and `pred : Bool` under `it : τ` ⇒ `e.all(pred) : Bool`, sound
  w.r.t. the evaluator. See "Proofs that must stay green". **This is the largest, riskiest
  commit** and may itself split into several (one per proof tree) — but each sub-commit must
  leave `lake build Cedar` green.

> ⚠️ If Decision 4 chooses the **conservative-`typeOf`** route for Phase 2 (defer the real type
> rule to T2.3/Phase 3), then C2's `typeOf` arm is `.error` and C4's type-rule proof is deferred
> with it — but the structural proof repair for the *evaluator*-level recursions still lands in
> C4. The plan recommends the real type rule in Phase 2 (Decision 4) to keep T2.3 self-contained.

---

## Design decisions (the 5 the brief requires)

### Decision 1 — Lean has no `#[cfg]`; the `all` constructor is ALWAYS present, "gating" is Rust/DRT-side only

**Grounded in** `Cedar/Spec/Features.lean` (Phase 0): it defines `public def anyAll : Bool := false`
and its own doc comment states the real gate is *structural* — "until the `.all` constructor is
added to `Expr` (Phase 2), the Lean spec simply cannot represent an `all` node, and the
differential-testing harness only ever feeds the Lean spec an `all` node when the Rust `anyall`
Cargo feature is enabled (the generator arm is gated on it, Phase 6)."

**Consequence for Phase 2:** adding `Expr.all` makes the node *unconditionally present* in the
Lean inductive. There is no `#[cfg(feature = "anyall")]` analogue in Lean, so you cannot
conditionally compile the constructor out. "Gating" lives entirely on the Rust/DRT side: the
Phase-6 generator only *emits* `all` under the Rust `anyall` feature, so a non-`anyall` DRT run
never hands Lean an `all` node, and the shared-fragment differential testing is unchanged. The
`anyAll` boolean stays `false` and is **not** used to guard the constructor (it cannot) — it
remains the documented single toggle other Lean code *may* branch on if a runtime guard is ever
wanted. **State this explicitly in the implementation and do not attempt a conditional
constructor.** The design.md "everything behind the `anyall` flag … default build unchanged"
claim holds for the Lean surface in the weaker, real sense: the constructor exists but is
unreachable unless the Rust generator (feature-gated) produces one.

### Decision 2 — `PredExpr`: separate restricted inductive (RECOMMENDED) vs. reuse `Expr` + a WF predicate

**Recommendation: a separate restricted `inductive PredExpr`**, mirroring the Phase-1 Rust
`PredExpr`/`PredExprKind` and design.md Surface 2.

**Grounded in:** `Cedar/Spec/Expr.lean` `inductive Expr` has `set (ls : List Expr)` and the three
set `BinaryOp`s (`contains`/`containsAll`/`containsAny`) and `UnaryOp.isEmpty`. design.md's
"illegal states unrepresentable" discipline (decision #6) and Phase-1 Rust both make non-nesting
and set-freeness *structural* at the typed-AST and Lean layers.

**Shape** (set-free by omission; `item` is the only new leaf):
```lean
inductive PredExpr where
  | item                                          -- the current element `it`
  | lit  (p : Prim)                               -- Prim already set-free
  | var  (v : Var)
  | ite  (cond thenPE elsePE : PredExpr)
  | and  (a b : PredExpr)
  | or   (a b : PredExpr)
  | unaryApp  (op : UnaryOp)  (e : PredExpr)       -- op ≠ isEmpty (constructor-enforced, Rust side)
  | binaryApp (op : BinaryOp) (a b : PredExpr)     -- op ∉ {contains,containsAll,containsAny}
  | getAttr   (e : PredExpr) (a : Attr)
  | hasAttr   (e : PredExpr) (a : Attr)
  | extHasAttr (e : PredExpr) (a : Attr) (as : List Attr)
  | record (map : List (Attr × PredExpr))
  | call   (xfn : ExtFun) (args : List PredExpr)
```
**No `set` constructor, no `all` constructor** → set-literals and nesting are *unrepresentable*
in the type (parse-don't-validate). The op side-conditions (`isEmpty`, the set `BinaryOp`s)
reuse the shared `UnaryOp`/`BinaryOp` enums and are maintained by the **Rust-side smart
constructors before the AST crosses into Lean** (design.md: "The op side-conditions are likewise
maintained by the (Rust-side) constructor before the AST is handed to Lean via DRT; the Lean
type additionally cannot *name* `all` inside a `PredExpr`"). In Lean they are not re-enforced
structurally (would need split op enums); if a proof needs them, a `WellFormedPred` predicate can
be added — but that is a proof convenience, not a construction gate.

**Why not reuse `Expr` + a WF predicate?** Reusing `Expr` for the predicate would make nesting
and set-literals *representable* and push the whole guarantee onto a side-condition that every
proof must carry — exactly the "validate after the fact" the design rejects. A separate inductive
costs hand-written `DecidableEq`/`Repr`/`Inhabited` (the same boilerplate `Expr`/`TypedExpr`
already pay — see the three mirror inductives) and a `sizeOf`/termination story for mutual
recursion, but it makes the analyzability-critical invariants hold *by construction* and matches
the Rust node 1:1, which keeps the DRT differential and the SymCC Condition-1 argument honest.
**Trade-off accepted.**

**Mutual-recursion note:** `Expr.all` embeds a `PredExpr`, and `PredExpr` is recursive with list
children (`record`, `call`). Follow the existing hand-written pattern in `Expr.lean`
(`decExpr`/`decExprList`/`decProdAttrExprList`) — `PredExpr` will need its own
`decPredExpr`/`decPredExprList`/`decProdAttrPredExprList` triple and, if structural recursion
over `Expr` now has to descend through `PredExpr`, a `sizeOf` relationship. Watch the
`termination_by`/`decreasing_by` obligations the way `Value.lt` (Value.lean) and the `decExpr`
mutual block already do.

### Decision 3 — Eval semantics of `expr.all(pred)`: `it` binding, no false-short-circuit, deterministic error

**Grounded in** `Cedar/Spec/Evaluator.lean` (`evaluate` is `Expr → Request → Entities → Result
Value`; `.and`/`.or` already model short-circuit; `.set` uses `mapM₁`; errors are `Except Error`
via `Result`), `Cedar/Spec/Value.lean` (`Value.asSet : Value → Result (Set Value)` returns
`.error typeError` on a non-set; `Value.lt` + `Value.decLt` give a total order for the
deterministic witness; `Set Value` from `Cedar.Data`).

**Receiver type-check (req 2.4):** evaluate `e`; coerce with `Value.asSet` (or the existing
`Coe Value (Result (Data.Set Value))`), which yields `.error .typeError` if the receiver is not a
set — reuse it, do not invent a new check.

**`it` representation and binding (design §3):** the element is a **full `Value`**, not a `Prim`
(sets contain records/ext/entityUIDs; e.g. `resource.owners.all(it.department == "eng")`
quantifies over records). Two options; **recommend option (b)**:
  - (a) `PredExpr.instantiate (p : PredExpr) (elem : Value) : Expr` that folds `elem` into an
    `Expr` (via the existing `Value → Expr` embedding) substituting `.item ↦ elem`, then reuse
    `evaluate`. Costs a `Value → Expr` round-trip and a second recursion.
  - (b) **(recommended)** a dedicated `evaluatePred (p : PredExpr) (it : Value) (req) (es) :
    Result Value` that threads the `it ↦ Value` binding and resolves `.item` to `it` directly,
    reusing the `apply₁`/`apply₂`/`getAttr`/`hasAttr`/`call` helpers. Avoids the Value→Expr
    round-trip, is easier to prove over, and keeps `.lit (p : Prim)` meaning "a literal the
    author wrote", distinct from the element placeholder `.item`. design.md explicitly prefers
    this: "(preferred) thread an `it ↦ Value` binding through `evaluate`".

**The fold (reqs 2.5, 2.7, 2.8) — THE load-bearing semantics:**
```
evalAll e p req es :=
  s ← (evaluate e req es).as (Set Value)         -- typeError if not a set
  -- fold over s in canonical order; seed .ok true (empty set ⇒ true, req 2.7).
  -- For each element v: r := evaluatePred p v req es
  --   r = .error _  → remember this is an error (track the SMALLEST erroring v by Value.lt);
  --                   MAY stop early (an error is already the final answer).
  --   r = .ok false → remember "a false was seen", but KEEP SCANNING (do NOT return .ok false).
  --   r = .ok true  → continue.
  -- After the whole set: if any element errored ⇒ .error .quantifierError (deterministic,
  --   witness = smallest erroring element); else if any false ⇒ .ok false; else .ok true.
```
**No early short-circuit to `.ok false`** (req 2.8): a later element could still ERROR, and an
error outranks a `false` (req 2.5). Early exit on the first *error* is fine (an error is the
final answer); early exit on *false* is NOT. This makes `all` O(n) with no best-case
short-circuit — the accepted cost of the deterministic error semantics. **Deterministic /
order-independent (req 2.5):** the `quantifierError` is a function of the input, not traversal
order; derive any witness from the **smallest** erroring element under `Value.lt` (which
`Value.lean` already defines and proves decidable). **No Lean `any` arm** (Decision 1 / tasks.md
T2.2): `evaluate` gains exactly one `.all` arm.

### Decision 4 — Which proof files the constructor forces, and the minimal obligations to keep `lake build Cedar` green

Two *functional* total-`Expr` matches break immediately (listed above): `typeOf`
(`Validation/Typechecker.lean`) and `compile` (`SymCC/Compiler.lean`). Both must get an arm in
**C2** or the build is red.

**Recommended Phase-2 posture:**
- **`compile` (SymCC): conservative reject arm now.** Real SymCC compilation of `all` is **Phase
  5** (T5.1). Phase 2 adds `| .all .. => .error …` (an unsupported/typeError-style `Result`),
  mirroring the Phase-1 Rust `tpe` conservative arm. This keeps `lake build Cedar` green without
  pulling Phase-5 work forward.
- **`typeOf` (Validation): implement the REAL sound type rule now (T2.3).** tasks.md T2.3 asks
  for the sound type rule (`e : Set τ`, `pred : Bool` under `it : τ` ⇒ `Bool`, req 6.1/6.4), and
  the typechecker is the one place the type rule lives. If `typeOf` returns a typed `all`, then
  **`TypedExpr` must gain an `all` constructor** (and its hand-written `decTypedExpr`,
  `TypedExpr.toExpr`, `TypedExpr.typeOf`, plus the two `Validation/Levels.lean` `TypedExpr`
  matches at lines 57 & 148 all get an `all` arm). This is the real cost of T2.3 and should be
  scoped into C4. *Fallback:* if the `TypedExpr` mirror work proves too large for this branch,
  C2's `typeOf` arm may conservatively `.error` and the real rule move to a Phase-3 follow-up —
  but the recommended path keeps T2.3 whole in Phase 2.

**Proof trees that recurse over `Expr` and so force an `all` case (T2.3, C4)** — enumerated from
the `extHasAttr`-proxy sweep (`grep -rln "\.extHasAttr" Cedar/Spec Cedar/Thm`, which finds the
real total-`Expr`-matching sites):
- `Cedar/Thm/WellTyped/Expr/Definition.lean` (the `Expr.WellTyped` inductive judgment) and
  `Cedar/Thm/WellTyped/Expr/Typechecking.lean` — add the `all` typing rule + its soundness vs.
  `typeOf`.
- `Cedar/Thm/Validation/Typechecker.lean` + `Cedar/Thm/Validation/Typechecker/*` — the
  typechecker soundness/completeness recursion.
- `Cedar/Thm/Validation/Levels/*` (`CheckLevel.lean`, `NoEntitiesError.lean`) — if `TypedExpr`
  gains `all`.
- `Cedar/Thm/WellTyped/Residual/{Definition,Soundness}.lean` — **only if** `Residual` gains an
  `all` ctor; since TPE is Phase 6.5, Phase 2 does **not** add it, and these proofs are untouched
  until then (the `Residual` inductive has no forced total-`Expr` match — it is built *from*
  `Expr`/`TypedExpr` by functions we control).
- `Cedar/Thm/SymCC/**` (`Compiler*`, `Enforcer*`, `Env/WF`, `Opt/Compiler`, `Data/Basic`) —
  these recurse over `Expr`; with the **conservative** `compile` arm, the Phase-2 obligation is
  only to keep them *compiling* (the `all` case maps to the reject arm, provably not emitting an
  undecidable term); the real SymCC soundness/completeness cases are **Phase 5** (T5.2).
- `Cedar/Thm/TPE/**` — **Phase 6.5**, untouched in Phase 2.

**Minimal lemmas / termination obligations (Phase 2):**
- `decExpr` `all.all` arm (DecidableEq Expr) — mechanical, mirrors existing arms.
- `PredExpr` hand-written `DecidableEq`/`Repr`/`Inhabited` + `decPredExpr*` mutual triple.
- `sizeOf`/`termination_by` for any structural recursion that now descends `Expr → PredExpr`
  (the evaluator's `evaluatePred`, and `decExpr` if it recurses into `PredExpr`). Follow the
  `Value.lt`/`decExpr` mutual-block patterns already in the tree.
- Evaluator-level soundness lemmas that are *total* over `Expr` constructors need an `all` case;
  the fold's determinism (order-independence) is the key new lemma for the type-rule soundness
  (prove the result is invariant under set-element permutation — the `Set Value` canonical order
  from `Cedar.Data` should make this a `Set.make`/canonical-order argument).

### Decision 5 — Full list of total `Expr` matches in Spec + Thm the constructor breaks

Derived from `grep -rln "\.extHasAttr" Cedar/Spec Cedar/Thm` (the `.extHasAttr` constructor is a
reliable proxy for a *total* `Expr` match, since catch-all matches don't name it). **23 files**
reference it; the ones that are genuine total `Expr` deconstructions the new ctor forces to cover:

**Spec (functional code — MUST get an arm in Phase 2 to build green):**
1. `Cedar/Spec/Expr.lean` — `decExpr` (hand-written `DecidableEq Expr`). **C2.**
2. `Cedar/Spec/Evaluator.lean` — `evaluate` (total, no catch-all). **C2 (real `evalAll`).**
3. `Cedar/Validation/Typechecker.lean` — `typeOf` (total, no catch-all). **C2 (real rule / fallback reject).**
4. `Cedar/SymCC/Compiler.lean` — `compile` (total, no catch-all). **C2 (conservative reject; real = Phase 5).**

**Spec — mirror inductives, broken only transitively (via Decision 4):**
5. `Cedar/Validation/TypedExpr.lean` — `TypedExpr` + `decTypedExpr`/`toExpr`/`typeOf`: needs an
   `all` ctor **iff** `typeOf` produces a typed `all` (recommended T2.3). **C2/C4.**
6. `Cedar/Validation/Levels.lean` — two `TypedExpr` matches (lines 57, 148): need an arm **iff**
   `TypedExpr` gains `all`. **C4.**
7. `Cedar/TPE/Residual.lean`, `Cedar/TPE/Evaluator.lean` — `Residual` mirror: **Phase 6.5**, not
   forced in Phase 2 (built from `Expr`/`TypedExpr` by our own functions, no forced total match).

**Thm (proofs — T2.3 / later phases):** the `.extHasAttr` sweep returns, in `Cedar/Thm/`:
`SymCC/Compiler.lean`, `SymCC/Compiler/ExtHasAttr.lean`, `SymCC/Compiler/WF.lean`,
`SymCC/Compiler/WellTyped.lean`, `SymCC/Data/Basic.lean`, `SymCC/Enforcer/Compile.lean`,
`SymCC/Enforcer/Footprint.lean`, `SymCC/Env/WF.lean`, `SymCC/Opt/Compiler.lean`,
`TPE/ErrorFree.lean`, `TPE/PreservesTypeOf.lean`, `TPE/Soundness/ExtHasAttr.lean`,
`TPE/WellTyped/ExtHasAttr.lean`, `Validation/Levels/CheckLevel.lean`,
`Validation/Levels/ExtHasAttr.lean`, `Validation/Levels/NoEntitiesError.lean`,
`Validation/Typechecker.lean`, `Validation/Typechecker/ExtHasAttr.lean`,
`WellTyped/Expr/Definition.lean`, `WellTyped/Expr/Typechecking.lean`,
`WellTyped/Residual/Definition.lean`, `WellTyped/Residual/Soundness.lean`.
Partitioned by phase: **Validation + WellTyped/Expr → T2.3 (C4, this branch)**; **SymCC/\* →
Phase 5**; **TPE/\* and WellTyped/Residual/\* → Phase 6.5**. In Phase 2, the SymCC and TPE proof
files must still *compile* (their `all` case resolves to the conservative `compile` reject /
no `Residual.all`), but their real soundness cases are later. **Confirm the exact break set by
building** — `grep` names the suspects; `lake build Cedar` names the victims.

---

## Green-check command + proofs that must stay green

**Build (with the required host env — do NOT re-derive, from Phase 0 OUTCOMES):**
```
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"
export LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar     # glibc 2.26 host; REQUIRED or lake fails to link
cd /local/home/luxask/code/cedar-spec/cedar-lean && lake build Cedar
```
Every commit (C1–C4) must leave this green. Phase-0 baseline was "green (586 jobs)".

**Proofs that must stay green (and are the real risk):**
- The whole `Cedar/Thm/**` tree compiles — the new `Expr.all` ctor must have a case in every
  total-`Expr` proof recursion (Decision 5). Validation + WellTyped/Expr get *real* cases (T2.3);
  SymCC + TPE get *compiling* cases consistent with the conservative Phase-2 arms.
- The new **sound type rule** for `all` (req 6.1/6.4) in `Thm/WellTyped/Expr/*` and
  `Thm/Validation/*`.
- Determinism/order-independence of `evalAll` (the new lemma underpinning type-rule soundness).

**Tests (T2.2 green check, must be NON-VACUOUS — retained lesson):**
- Locate `cedar-lean`'s existing spec/evaluator test file(s) first (do not assume a path).
- Add tests for 2.1/2.2/2.5/2.7 and the 2.8 regression (`[false, erroring].all ⇒ quantifierError`,
  not `false`). Show the count RUN > 0 and that the 2.8 test FAILS if the fold is reverted to
  short-circuit on first `false`.

---

## Risks / unknowns

1. **Proof blast radius (highest risk).** `grep` names ~22 Thm files touching total `Expr`
   matches. The true forced set is only known once `Expr.all` exists and `lake build Cedar` runs
   — budget C4 as potentially several commits. Mitigate by landing C2 (ctor + conservative
   downstream arms) first and letting the compiler enumerate the real breaks.
2. **`TypedExpr` mirror scope (Decision 4).** The real type rule (T2.3) likely requires a
   `TypedExpr.all` ctor + its hand-written `decTypedExpr`/`toExpr`/`typeOf`/Levels arms. This is
   non-trivial boilerplate. If it balloons, the conservative-`typeOf` fallback keeps Phase 2
   building and moves the type rule to a Phase-3 follow-up — but prefer the real rule.
3. **Mutual-recursion termination.** `Expr`↔`PredExpr` and the new `evaluatePred` may trip
   `termination_by`/`decreasing_by` obligations. Follow the existing `decExpr`/`Value.lt` mutual
   blocks; this is a known-shape problem, not a research one.
4. **Deterministic witness proof.** Proving `evalAll`'s `quantifierError` is order-independent
   needs the `Set Value` canonical order (`Cedar.Data`, `Set.make`, `Value.lt`). Confirm the
   `Set` API exposes a canonical fold the determinism proof can lean on.
5. **Cold `lake build` is slow.** Rebuild cost gates iteration; batch proof edits per tree.
6. **MCP:** `@kirocrew-computer` was declared-but-not-configured this session (unavailable); it
   was not needed — all grounding used file reads + grep + git.

---

## Discrepancies vs. tasks.md (corrected here, grounded)

1. **tasks.md T2.1 says "update the hand-written `DecidableEq` … and any `Repr`/`Inhabited`
   derivations".** Grounded correction: in the *real* `Expr.lean`, `Expr` uses
   `deriving Repr, Inhabited` (auto — these extend automatically) but a **hand-written `decExpr`
   / `decExprList` / `decProdAttrExprList`** (NOT derived) — only the hand-written `decExpr`
   needs a manual `all` arm. `Error` (Value.lean) uses `deriving … DecidableEq`, so
   `quantifierError` needs **no** hand-written arm. tasks.md over-states the manual-derivation
   surface for `Expr`'s `Repr`/`Inhabited` and under-specifies that the DecidableEq is a *mutual
   hand-written* block.
2. **tasks.md T2.1 lists `Cedar/Spec/Value.lean` for `PredExpr`.** Grounded correction:
   `PredExpr` and `Expr.all` both belong in `Cedar/Spec/Expr.lean` (where `Expr` and the ops
   live); only `Error.quantifierError` is in `Value.lean`. (design.md Surface 2 agrees;
   tasks.md's file list conflates the two.)
3. **tasks.md T2.3 names `Thm/WellTyped*`, `Thm/Validation/Typechecker*`,
   `Thm/Validation/Validator.lean`.** Grounded correction: the *functional* type rule lives in
   `Cedar/Validation/Typechecker.lean` (`typeOf`, Spec-level, not Thm), and the typed output is a
   separate mirror inductive `Cedar/Validation/TypedExpr.lean` that T2.3 must also extend
   (tasks.md doesn't mention `TypedExpr` or `Validation/Levels.lean`, both of which the real
   `typeOf`-produces-`TypedExpr` design forces). Added to the touch list.
4. **The constructor breaks `SymCC/Compiler.lean`'s `compile` and `Validation/Typechecker.lean`'s
   `typeOf` IMMEDIATELY (both total, no catch-all), even though SymCC is Phase 5.** tasks.md
   phases SymCC at Phase 5 but does not flag that Phase 2 *must* add a (conservative) `compile`
   arm just to keep `lake build Cedar` green — the Lean analogue of the Phase-1 Rust exhaustive-
   match sweep. Called out explicitly so implementation isn't surprised (matches the retained
   process lesson from Phase 1).
5. **No Lean `any` (confirmed, not a discrepancy but worth restating):** tasks.md T2.2 is correct
   that Lean has no `any` desugaring arm; grounded against `Evaluator.lean` having `.less`/`.lessEq`
   but the `BinaryOp` having no `greater`/`greaterEq` — same precedent.
