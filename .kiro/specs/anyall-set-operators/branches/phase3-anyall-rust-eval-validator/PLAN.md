# Phase 3 Plan — Rust evaluator + validator (`phase3-anyall-rust-eval-validator`)

Branch `phase3-anyall-rust-eval-validator` on **both** repos (docs: cedar-spec; code: the nested
cedar repo at `cedar-spec/cedar`). **Scope: the cedar Rust repo only** — give the Phase-1
`ExprKind::All { expr, pred }` node its real *runtime* behaviour (evaluation) and its real
*static* behaviour (validation / type rule), replacing the conservative Phase-1 placeholders.
No surface syntax (Phase 4), no SymCC (Phase 5), no DRT generator (Phase 6), no TPE (Phase 6.5).

Implements spec tasks **T3.1** (evaluator) and **T3.2** (validator / well-formedness),
`tasks.md` §"Phase 3 — Rust evaluator + validator, gated". Everything is `#[cfg(feature =
"anyall")]`; the default build must stay byte-for-byte unchanged (req 3.1).

This plan is grounded in files read on 2026-10-08; the real paths and line numbers below were
re-derived from the sources (tasks.md references may be stale). Every claim cites a file read.

---

## Goal

Make `cedar-policy-core` evaluate and validate `.all`/`.any` policies with semantics that match
the Phase-2 Lean spec exactly, behind `anyall`:

1. **Evaluator** (`evaluator.rs`): replace the Phase-1 `ExprKind::All` arm (currently
   `Err(non_value(expr.clone()))`, `evaluator.rs:779-785`) with real evaluation — receiver must
   be a `Set`; bind each element (a full `Value`) to the predicate's `Item` leaf; evaluate the
   instantiated predicate; fold with **no early short-circuit on `false`**; a predicate error on
   *any* element ⇒ one deterministic, order-independent `QuantifierError`; empty set ⇒ `true`;
   non-set receiver ⇒ `TypeError`; a residual receiver/element ⇒ a conservative residual `All`.
2. **New evaluation-error variant** `EvaluationError::QuantifierError` (payload-free, matching
   Lean D-10), gated on `anyall`, following the existing `tolerant-ast` `ASTErrorExpr`
   precedent on the publicly-exported `EvaluationError` enum (`evaluator/err.rs`).
3. **Validator** (`validator/typecheck.rs`): replace the Phase-1 conservative `All` arm (which
   `TypecheckAnswer::fail`s, `typecheck.rs:1251-1264`) with the real type rule (req 6.1–6.3):
   `E : Set<τ>` and `P : Bool` under `it : τ` ⇒ `Bool`; reject non-set receiver / non-`Bool`
   predicate; defer unknown-`τ` handling to Cedar's existing set-element-type treatment.
4. **Well-formedness** (`Expr::try_validate`, `expr.rs:~980`): reject `it` outside a predicate
   (req 1.6), nested quantifiers (req 1.4 — already structurally impossible in the AST, so this
   is a belt-and-braces decode-path check), and set-containing predicates (req 1.5 — the
   construction smart constructors already reject the set *ops*; here we also reject a predicate
   whose static type is `Set`).
5. **Subexpression / analysis walks**: decide per-site whether `Expr`-level walks must now
   descend into the `PredExpr`.

Mirrors the Phase-2 Lean evaluator (`phase2-anyall-lean-spec/OUTCOMES.md`): payload-free
quantifier error, no `false` short-circuit, receiver error propagated unchanged, element binds a
full `Value`, empty ⇒ `true`.

---

## Files to touch (exact grounded paths, all under `cedar-spec/cedar/cedar-policy-core/src`, except where noted)

| File | Change |
|---|---|
| `evaluator/err.rs` | New gated `EvaluationError::QuantifierError` variant + `evaluation_errors::QuantifierError` struct (payload-free), with `source_loc`, the `source_loc()` arm, the `with_maybe_source_loc` arm, and a `quantifier_error(loc)` constructor. (`err.rs` enum ~line 50; `source_loc()` ~168; `with_maybe_source_loc` ~195; constructors ~end.) |
| `evaluator.rs` | Replace the `ExprKind::All` arm (`779-785`); add a private `eval_all(expr, pred, slots)` + `instantiate_pred(pred, elem_value) -> Expr` (or a threaded `it ↦ Value` binding). Add parity unit tests. |
| `ast/pred.rs` | Add `PredExpr::subexpressions()` (or an internal walker) if the validator/well-formedness needs to inspect predicate leaves; add a `contains_set_term`/typed check helper if 1.5's static-type reject is done here. Already `#![cfg(feature="anyall")]`. |
| `validator/typecheck.rs` | Replace the conservative `All` arm (`1251-1264`) with the real rule; add a `typecheck_pred(pred, it_ty, prior_capability, type_errors)` that threads `it : τ` and resolves `PredExprKind::Item` to `it_ty`. |
| `ast/expr.rs` | `Expr::try_validate` (`~980`): add gated checks for req 1.4/1.5/1.6. Possibly extend `subexpressions`/`is_projectable` behaviour (see decision #4). |
| `ast/expr_iterator.rs` | DECISION #4: optionally descend into `pred` (currently receiver-only, `expr_iterator.rs:89-92`). |
| `ast/expr_visitor.rs` | DECISION #4: `visit_all` default currently visits receiver only (`expr_visitor.rs:254-266`). |
| `validator/level_validate.rs` | DECISION #4: `All` arm currently recurses receiver only (`level_validate.rs:387-390`). Decide whether to recurse the predicate. |
| **No change in Phase 3:** `validator/entity_manifest.rs` (`692-694`, stays `UnsupportedCedarFeature`), `tpe/residual.rs` + `tpe/evaluator.rs` (Phase 6.5), protobuf/EST (Phase 4). | — |

(cedar-spec: only this `PLAN.md`, then `OUTCOMES.md` at the end of the phase.)

---

## Task breakdown (logical commits — cedar repo unless noted)

Ordered so every commit builds and tests green with and without `--features anyall`.

- **C0 (cedar-spec).** This `PLAN.md`. Commit message `phase3: plan (Rust evaluator + validator)`.
- **C1.** New gated `EvaluationError::QuantifierError` variant + payload-free
  `evaluation_errors::QuantifierError` struct, wired into all four `EvaluationError` sites
  (`source_loc()`, `with_maybe_source_loc`, the enum, a constructor). No evaluator use yet — the
  variant is inert, so the matrix stays green. _Satisfies groundwork for 2.5/2.6._
- **C2.** Evaluator `eval_all` + predicate instantiation; replace the `non_value` placeholder.
  Deterministic `QuantifierError`, no `false` short-circuit, empty ⇒ `true`, non-set ⇒ type
  error, residual receiver/element ⇒ residual `All`. Parity unit tests mirroring the 16 Lean
  tests (req 2.1/2.2/2.4/2.5/2.7/2.8), including the false-then-error ⇒ QuantifierError case.
  _Satisfies 2.1, 2.2, 2.4, 2.5, 2.6, 2.7, 2.8 (T3.1)._
- **C3.** Validator type rule: `typecheck_pred` threading `it : τ`; replace the conservative
  `All` arm. Accept/reject unit tests (set receiver + Bool predicate ⇒ Bool; non-set ⇒ error;
  non-Bool predicate ⇒ error; unknown element type behaves like `contains`). _Satisfies 6.1,
  6.2, 6.3 (T3.2)._
- **C4.** Well-formedness in `Expr::try_validate`: reject `it` outside a predicate (1.6), nested
  quantifiers (1.4), set-typed predicates not caught by the construction smart constructors
  (1.5). Plus the per-site subexpression-walk decision (#4). Tests for each reject. _Satisfies
  1.4, 1.5, 1.6 (T3.2)._
- **Cn.** Any review-round fixes (fresh blind reviewer each round, per the standing mandate).

Commits C1–C4 are each independently green; split further if a reviewer wants smaller diffs.

---

## Design decisions (the 5 the brief asks for)

### 1. Rust evaluation — how to evaluate a `PredExpr` with `it` bound, and the error variant

**Instantiation vs. threaded binding.** The Lean side (`phase2` OUTCOMES) chose a threaded
`evaluatePred` that carries `it ↦ Value` rather than `PredExpr.instantiate`. Rust has a cleaner
option the design already names (design "Evaluation is by instantiation with a `Value`"):
`From<Value> for Expr` / `From<ValueKind> for Expr` (`ast/expr.rs:222-244`) reconstructs a
concrete `Expr` from any element `Value` (incl. records/ext/entity UIDs via `RestrictedExpr`).

**Decision: instantiate `PredExpr → Expr` by substituting the element `Value` for `Item`, then
reuse the existing `self.partial_interpret`.** Concretely, a function
`instantiate_pred(pred: &PredExpr, elem: &Value) -> Expr` that walks the predicate once and maps
`PredExprKind::Item ⇒ Expr::from(elem.clone())` and every other variant to its `ExprKind`
counterpart (the variants are 1:1 with `ExprKind` minus `Set`/`Unknown`/`Slot`/`All`). Rationale:
(a) it reuses the whole battle-tested evaluator (operators, errors, short-circuit, residuals) for
free, so semantics automatically match `contains`/`and`/`or`; (b) it needs no new "env" parameter
threaded through `partial_interpret`, which has no local-variable binding concept today
(`ExprKind::Var` resolves only principal/action/resource/context, `evaluator.rs:460-470`); (c) it
mirrors the design's stated preferred Rust path (`From<Value> for Expr`). The cost — rebuilding an
`Expr` per element — is acceptable at O(n) (the no-short-circuit rule already makes `.all` O(n),
req 2.8). _Alternative rejected:_ threading an `it: Option<&Value>` through
`partial_interpret_internal` mirrors Lean but touches the hottest function in the evaluator and
adds a parameter to every recursive call for one feature; not worth it. (Recorded as a minor
decision for DECISIONS.md.)

**The error variant.** New `EvaluationError::QuantifierError`, **payload-free** (an empty
`evaluation_errors::QuantifierError { source_loc }` struct), gated on `anyall`. Rationale:
Lean's `quantifierError` carries no payload (D-10), and req 2.6's bounded/deterministic payload
clause is *conditional* ("WHEN QuantifierError carries diagnostic information…") — carrying none
is trivially bounded and order-independent, and keeps Rust/Lean error shapes identical for the
DRT differential. It follows the `#[cfg(feature="tolerant-ast")] ASTErrorExpr` precedent exactly
(`evaluator/err.rs`): a gated variant on the public `EvaluationError` enum plus a subtype struct
in `evaluation_errors`, with matching `source_loc()` / `with_maybe_source_loc` / constructor
arms. The `source_loc` is the whole-`All`-expression loc.

**Exact Lean-matching semantics** (fold over `set.authoritative.iter()`, which is a
`BTreeSet<Value>` so iteration is already sorted/deterministic — `value.rs:386-388`):
- Evaluate the receiver. If it is a `PartialValue::Residual`, residualize (see decision #2). If
  it is a `Value` that is not a `Set`, return `TypeError` expecting `Type::Set` (mirrors
  `BinaryOp::Contains`'s non-set handling, `evaluator.rs:597-603`). A receiver *error*
  propagates unchanged (it is returned by `?` before the fold).
- For each element `e` (sorted order): instantiate and `partial_interpret` the predicate.
  - Predicate **errors** ⇒ the whole `.all` is `QuantifierError` (may early-exit on first error;
    an error is already the final answer — req 2.8).
  - Predicate yields a non-bool `Value` ⇒ `TypeError` (same as the Lean "non-bool predicate
    result ⇒ quantifier error" is realised here: in Lean a non-bool pred result is folded into
    `quantifierError`; **align with Lean** by treating a non-bool predicate *result* as
    contributing to `QuantifierError`, not a bare `TypeError` — see Discrepancies below).
  - Predicate yields `false` ⇒ record "false seen" but **keep scanning** for a later error
    (req 2.8 / no short-circuit). Only after the whole set is error-free does a recorded `false`
    collapse to `Ok(false)`.
  - Predicate yields a `Residual` ⇒ decision #2.
- Empty set ⇒ `Ok(true)` (req 2.7).
- `.any` never reaches here as its own node: it was lowered to `!all(!p)` at construction
  (`Expr::any`, D-05), so only the single `All` arm exists.

### 2. Partial evaluation (residual receivers / elements)

**Grounding:** `partial_interpret_internal` returns `PartialValue` (Value | Residual) and
residuals flow on the *default* code path, not only under the `partial-eval` cargo feature — the
`partial-eval` feature only gates named-unknown *resolution* (`unknown_to_partialvalue`,
`evaluator.rs:793-811`); `ExprKind::Unknown` always produces a residual otherwise. So the `All`
arm **must** handle residuals regardless of feature. The existing `Set` arm residualizes by
rebuilding `Expr::set(residuals)` when any element is residual (`evaluator.rs` `ExprKind::Set`
arm); `And`/`Or` rebuild `Expr::and/or(...)` (`evaluator.rs:472-531`).

**Decision: conservatively residualize the whole `All` node.** If the receiver partial-interprets
to a `Residual`, return `PartialValue::Residual(Expr::all(residual_receiver, pred.clone()))`
rather than erroring or dropping the predicate — preserving the invariant that a residual
re-evaluated on the remaining input agrees with full evaluation. If the receiver is a *concrete*
set but *some element's instantiated predicate* yields a residual, likewise residualize the whole
node (do **not** partially fold concrete elements and keep others symbolic in Phase 3): the
no-short-circuit rule (2.8) means a residual element could still hide an error on another element,
so a clean "all-or-nothing residual" is the sound conservative choice. (This matches req 7.2's
spirit; the *refined* TPE story — concrete-receiver concrete evaluation, residual-element
per-element PE — is explicitly Phase 6.5 / `tpe` module, req 7.4, and is **out of scope here**.)
Rationale: Phase 3 is the *concrete* evaluator; a conservative residual keeps non-`anyall` and
non-partial callers correct and defers the clever TPE to its own phase without blocking.

### 3. Validator type rule (req 6.1–6.3)

**Grounding:** the typechecker is `Typechecker::typecheck(self, prior_capability, e, type_errors)
-> TypecheckAnswer` (`typecheck.rs:339`). Variables are typed from `self.request_env`
(`typecheck.rs:353-388`) — there is **no general local-variable typing environment**, and `it`
is `PredExprKind::Item`, not a `Var`. Set element types are modelled as `Type::Set { element_type:
Option<Arc<Type>> }` (`types.rs:81-153`); `contains` typechecks arg1 with
`expect_type(.., Type::any_set(), ..)` then extracts `Some(Type::Set { element_type: Some(ty) })`
(`typecheck.rs:1595-1646`). The conservative Phase-1 `All` arm is at `typecheck.rs:1251-1264`.

**Decision: add a `typecheck_pred(&self, pred, it_ty: &Type, prior_capability, type_errors) ->
TypecheckAnswer`** that mirrors `typecheck` over `PredExprKind` and resolves `PredExprKind::Item`
to `it_ty` (the role `Var::Principal` plays via `request_env`). The `All` arm then:
1. `expect_type(prior_capability, recv, Type::any_set(), ..)` — reject non-set receiver (req 6.2),
   reusing the same `UnexpectedTypeHelp` hints as `contains` (`typecheck.rs:1595-1620`).
2. Extract the element type `τ` from the receiver's `Type::Set { element_type }`
   (`typecheck.rs:1628-1631` pattern). For `element_type: None` (empty-set / unknown element),
   **defer to Cedar's existing treatment** (req 6.3) — i.e. type the predicate against an
   `AnyType`/open element exactly as `contains`/`containsAll` do against the same `None`, no
   special-casing. (Confirm the precise behaviour by reading how `contains`'s LUB handles a
   `None` element type at `typecheck.rs:1625-1646`; match it.)
3. `typecheck_pred(pred, τ, ..)` and require the result type is `Bool` (req 6.1); non-`Bool` ⇒
   type error (req 6.2).
4. On success, annotate the `All` node with `Some(Type::primitive_boolean())`.

**Why a `typecheck_pred` mirror rather than mapping `PredExpr → Expr` with a typed placeholder:**
mapping would require inventing an `Expr` leaf that types to `τ` (there is none — `Item` has no
`Expr` counterpart), and a per-element `Value` is not available at validation time. A parallel
`typecheck_pred` is the smaller, more faithful change and matches how the Lean side would need a
`typeOfPred` (D-11). Strict-mode LUB/`enforce_strict_equality` interactions in the predicate are
inherited by reusing the same `expect_type` helpers inside `typecheck_pred`.

**Empty-set / unknown element type:** per req 6.3, no new behaviour — whatever `contains` does
for `Type::Set { element_type: None }` is what `.all` does. Record the observed behaviour in
OUTCOMES once read.

**Lean typechecker rejects `.all` (D-11) — the DRT consequence (stated, not fixed here).** The
Lean `typeOf` still conservatively rejects `.all` (D-11, OPEN). So the Rust validator will
*accept* well-typed `.all` policies that the Lean validator *rejects*. The Phase-6 **validation**
differential (`cedar-drt/fuzz/fuzz_targets/validation-*.rs`) must therefore treat a
Rust-accept / Lean-reject on `.all` as **expected**, not a counterexample — either by excluding
`.all` from the validation generator or by special-casing the divergence. This is a Phase 6
wiring note, surfaced here because the Rust rule we build is what creates the divergence;
resolving D-11 (adding the Lean rule) is the alternative. **Phase 3 does not touch DRT.**

### 4. Subexpression / visitor walks — descend into the predicate? (per site)

**Grounding:** `Expr::subexpressions()` uses `expr_iterator::ExprIterator`, whose `All` arm
pushes only the receiver `expr` (`expr_iterator.rs:89-92`); `expr_visitor::visit_all` default
visits only the receiver (`expr_visitor.rs:254-266`); `level_validate` recurses receiver only
(`level_validate.rs:387-390`). **Key fact:** `PredExpr` has **no `Unknown` and no `Slot` leaf**
(`ast/pred.rs` — the variants are `Item`/`Lit`/`Var`/`If`/`And`/`Or`/`UnaryApp`/`BinaryApp`/
`ExtensionFunctionApp`/`GetAttr`/`HasAttr`/`ExtHasAttr`/`Like`/`Is`/`Record`), so the two things
`Expr`-level walks are usually mined for — `slots()` and `contains_unknown`/`is_projectable`
(`expr.rs:339-380`) — **cannot find anything in a predicate**. Per-site decision:

- **`expr_iterator` / `subexpressions()` / `slots()` / `is_projectable()`:** **do not descend.**
  A `PredExpr` has no `Slot`/`Unknown`, so `slots()` and `contains_unknown` are already complete
  without it, and `subexpressions()` is typed `Iterator<&Expr>` — it *cannot* yield the
  distinct `PredExpr` type anyway. Leaving it receiver-only is correct, not a gap. (Record this
  reasoning so a future reader does not "fix" it.)
- **`expr_visitor::visit_all`:** leave the default receiver-only; it is `#[cfg]`-gated and any
  implementor needing the predicate can override (as the doc comment already says,
  `expr_visitor.rs:256-266`). No Phase-3 consumer needs it.
- **`level_validate`:** the predicate CAN contain `GetAttr`/`In`/entity derefs over `it` or
  `principal`/`resource`, which is exactly what level validation bounds. **Decision: recurse the
  predicate** — add a predicate-aware level check (treat `it` as level-0, the element already
  being in-hand) so a `.all` whose predicate dereferences entities is level-checked. This is the
  one site that genuinely needs to descend. (If req scope for levels is unclear, the fallback is
  to keep receiver-only and record it as a known limitation; prefer descending.)
- **`try_validate`:** must inspect the predicate to enforce 1.5/1.6 (below), so it needs a
  predicate walk regardless; add `PredExpr`-level validation there.

### 5. Tests (non-vacuous)

Per the standing lesson: show the new tests RUN (count > 0) and that they fail if the
implementation is reverted/mutated.

**Evaluator (`evaluator.rs` `#[cfg(all(test, feature="anyall"))]`), mirroring the 16 Lean tests
(`UnitTest/AnyAll.lean`):**
- 2.1 all-true ⇒ `true`; 2.2 one false (no errors) ⇒ `false`; 2.7 empty ⇒ `true` (and `.any`
  empty ⇒ `false` via `!all(!p)`); 2.4 non-set receiver ⇒ `TypeError`.
- 2.5/2.8 **the regression test:** a set with one element that makes the predicate `false` AND
  another that makes it error ⇒ `QuantifierError`, independent of element order (test both
  orders; `BTreeSet` sorts, so construct values whose sorted order puts the error first in one
  case and the false first in the other). Mutating the fold to short-circuit on `false` must
  make this FAIL (non-vacuity).
- element binds a full `Value`: a set of **records**, predicate `it.department == "eng"`
  (design US example) ⇒ exercises `From<Value> for Expr` instantiation of a record element.
- `.any` lowering: `s.any(it == k)` ⇒ `true` iff some element matches.
- receiver error propagated unchanged (e.g. receiver is a get-attr on a missing entity attr).

**Validator (`typecheck.rs` tests):** accept `principal.ports.all(it >= 8000)` where `ports:
Set<Long>` ⇒ `Bool`; reject non-set receiver; reject non-Bool predicate (`it + 1`); reject `it`
outside a predicate (1.6); confirm unknown/empty element type behaves like `contains`.

**Well-formedness:** `try_validate` rejects a hand-built `it` outside a predicate, and a
hand-built predicate whose static type is `Set` (1.5), and (defensively) a nested quantifier.

---

## Green checks (the full feature matrix — all must pass at each commit)

Run from the cedar repo. Environment preamble per host:
`export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"; unset LD_PRELOAD`.

Build/clippy matrix (per the Phase-1 lesson that a single `--features anyall` is insufficient —
exhaustive matches in *other* gated modules only break under feature *combinations*):

- core: `default`, `anyall`, `anyall tolerant-ast`, `experimental`, `--all-features`
- cedar-policy: `default`, `experimental`, `--all-features`

Test counts (non-vacuity):
- `cargo test -p cedar-policy-core --lib` (default) → baseline N.
- `cargo test -p cedar-policy-core --lib --features anyall` → N + (new eval tests) + (new
  validator tests); every new test passes, 0 ignored; record the exact `+K`.
- Confirm new behaviour is non-vacuous by a mutation (short-circuit-on-false ⇒ the 2.8 test
  fails; drop the `it`-binding ⇒ record binding test fails).

Save `brazil`/`cargo` output to a temp log and `tail`/`grep` it (large output).

---

## Risks

1. **Strict-mode typing of the predicate.** `typecheck_pred` must reuse `expect_type` /
   `enforce_strict_equality` so strict-mode LUB rules apply inside the predicate the same way
   they do for `contains` (`typecheck.rs:1621-1646`). Risk: subtle strict/permissive divergence.
   Mitigation: thread `self.mode` unchanged into `typecheck_pred`; add a strict-mode predicate
   test.
2. **Non-bool predicate *result* at eval time.** Lean folds a non-bool predicate result into
   `quantifierError`; a naive Rust port might emit a bare `TypeError` instead. Must match Lean
   (see Discrepancy D-A). Risk: DRT eval divergence in Phase 6.
3. **`EvaluationError` is publicly exported** (`cedar-policy` api.rs:5709). A new variant is
   additive and gated, but `validation-pbt.rs:65-78` has an exhaustive `EvaluationError` match
   that will need an `anyall` arm **once cedar-drt is built with `anyall`** (Phase 6, not now).
   Record as a cross-repo follow-up.
4. **Deterministic witness.** We chose payload-free, so there is no "smallest erroring element"
   witness to compute — removing a whole class of nondeterminism risk. If the owner later wants a
   payload (req 2.6), `Value: Ord` (`value.rs:44`) and the sorted `BTreeSet` iteration give a
   deterministic smallest-element witness for free.
5. **Level validation of the predicate** (decision #4): descending adds a `PredExpr`-aware level
   walker. Risk of over/under-counting `it`'s level. Mitigation: treat `it` as level-0 (the
   element value is in hand) and test a predicate that dereferences `principal` vs `it`.

---

## Discrepancies vs tasks.md

- **D-A (non-bool predicate result).** tasks.md T3.1 says "Mirror the Lean semantics exactly".
  The Lean evaluator maps *both* a predicate error *and* a non-bool predicate result to
  `quantifierError` (phase2 OUTCOMES: "a predicate error or a non-boolean result on any element
  makes the whole expression `quantifierError`"). The Rust evaluator's natural instinct is to
  emit `TypeError` for a non-bool. **Resolution: match Lean** — a non-bool predicate result
  contributes to `QuantifierError`, not a standalone `TypeError`. Flagged because it is easy to
  get wrong and is a likely Phase-6 differential failure if missed. (A reasonable alternative is
  to argue the predicate is *typechecked* to Bool so a non-bool result is unreachable in
  validated policies — but the evaluator runs on *unvalidated* ASTs too, e.g. DRT, so the
  behaviour must be defined. Follow Lean.)
- **D-B (payload-free error, req 2.6).** tasks.md/req 2.6 describes a bounded deterministic
  payload ("smallest erroring element"); we carry **none**, consistent with Lean D-10 and the
  conditional phrasing of 2.6. Noted so the owner sees Rust and Lean agree on payload-free.
- **D-C (TPE scope).** tasks.md lists TPE under Phase 6.5; req 7.x. Phase 3's residual handling
  is the *conservative* "residualize the whole node" (decision #2), **not** the refined
  concrete-receiver evaluation of req 7.1. The `tpe/` module placeholder
  (`AllNotSupportedError`, Phase-1 OUTCOMES) is left untouched.

---

## Minor decisions the owner may want to see (copy into DECISIONS.md)

- **D-14 (Phase 3): predicate evaluation by `Value→Expr` instantiation, not a threaded `it`
  binding.** Rust instantiates `PredExpr → Expr` via `From<Value> for Expr` and reuses the
  existing evaluator, where Lean threads `it ↦ Value` through `evaluatePred`. Same observable
  semantics; chosen to avoid adding a binding parameter to the evaluator's hot path. Reversible:
  swap for a threaded binding if per-element `Expr` rebuild cost ever matters. Status: SETTLED.
- **D-15 (Phase 3): `QuantifierError` is payload-free in Rust too** (matches Lean D-10). Status:
  SETTLED (req 2.6 payload clause is conditional).
- **D-16 (Phase 3): non-bool predicate *result* ⇒ `QuantifierError`, not `TypeError`** (matches
  Lean; see Discrepancy D-A). Status: SETTLED, but flagged for Phase-6 differential attention.
- **D-17 (Phase 3): partial eval residualizes the whole `All` node conservatively** (receiver
  residual, or any element-predicate residual). The refined per-element TPE is Phase 6.5
  (req 7.1/7.3). Status: SETTLED for Phase 3.
- **D-18 (Phase 3): `subexpressions()`/`slots()`/visitors stay receiver-only** because `PredExpr`
  has no `Slot`/`Unknown` leaf (so nothing is missed), but **`level_validate` DOES descend into
  the predicate** (it is the one analysis that bounds attribute/entity derefs the predicate can
  contain). Status: SETTLED; revisit if a later analysis needs predicate leaves.
- **D-19 (Phase 3): validator uses a parallel `typecheck_pred(it_ty)` mirror** rather than
  mapping `PredExpr`→`Expr`, because `Item` has no `Expr` counterpart and no element `Value`
  exists at validation time. Mirrors the Lean `typeOfPred` shape D-11 would need. Status:
  SETTLED.
