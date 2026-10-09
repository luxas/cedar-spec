# Phase 6.5 — Typed partial evaluation (TPE) of `.all` / `.any`

Branch: `phase6.5-anyall-tpe` (cedar-spec @ `d923c63` off `phase6-anyall-drt-differential`;
cedar @ `826cc339` off `phase6-anyall-drt-differential`).
Satisfies: requirements **7.1 / 7.2 / 7.3 / 7.4**, closes the open **D-32** stray-`it` NIT.

> **Rebase note.** Phase 6 is being implemented in parallel in the main worktree. These two
> branches were cut from Phase 6's *base* (`phase6-anyall-drt-differential`), NOT its final
> tip, and MUST be rebased onto Phase 6's final tip before merge (`git rebase` +
> `--force-with-lease`, bottom-up per the stacked-PR rule). Nothing here touches the DRT
> generator / differential targets Phase 6 owns, so the rebase should be text-only; re-run the
> full green-check matrix after it.

---

## 0. State of the world (evidence reviewed)

**Requirements §7** (requirements.md) is the spec: 7.1 concrete receiver ⇒ evaluate concretely
(Concrete bool / QuantifierError, matching §2); 7.2 residual receiver ⇒ emit residual `All`,
never error/discard; 7.3 concrete element whose sub-terms are residual ⇒ the per-element
predicate is itself partially evaluated, preserving the no-short-circuit rule (2.8); 7.4 TPE
MAY land late / conservatively and MUST NOT change non-`anyall` behaviour (3.1).

**Rust TPE** (`cedar/cedar-policy-core/src/tpe/`):
- `residual.rs` — `enum Residual { Partial{kind,ty} | Concrete{value,ty} | Error(ty) }` and
  `enum ResidualKind`. There is **no `All` variant yet**. `Residual::try_from_typed_expr` has a
  gated arm `ExprKind::All { .. } => return Err(AllNotSupportedError.into())` (the placeholder
  this phase replaces). `From<Residual> for Expr` rebuilds an `Expr` for re-authorization.
  `ResidualKind::all_literal_uids` and `Residual::can_error_assuming_well_formed` are the two
  exhaustive `match`es a new variant must extend.
- `evaluator.rs` — `Evaluator::interpret(&Residual) -> Residual` is the fold. `Set`/`Record`
  arms are the template for concrete-folding: interpret each child, then if **all children are
  `Concrete`** fold to a `Concrete` value, else if **any is `Error`** → `mk_error()`, else keep
  a residual. `BinaryApp` etc. delegate to the concrete evaluator via `Expr::from`.
- `err.rs` — `ExprToResidualError::AllNotSupported` + `AllNotSupportedError` (both
  `#[cfg(feature="anyall")]`). Keep the enum variant; drop the throw site once `from_expr`
  handles `All`. (The struct can stay as dead-but-harmless, or be removed — see W1.)
- **No DRT fuzz target exercises TPE** (`grep tpe cedar-drt` = 0 hits). TPE is covered by
  `cedar-policy-core` unit/parity tests only. So the "DRT TPE differential" item below is a
  *decision to confirm*, not a wiring task (see Risk R4 / Fork F3).

**Concrete evaluator `.all`** (`cedar/cedar-policy-core/src/evaluator.rs:780`, Phase 3): non-set
receiver ⇒ `TypeError`; receiver error propagates; per element `pred.instantiate(elem)` is
evaluated — a `RecursionLimit` propagates as-is (D-22), any other error or non-bool ⇒
payload-free `QuantifierError` (`EvaluationError::quantifier_error(loc)`); otherwise the
conjunction, `true` on empty; **no short-circuit on false** (2.8); a residual element ⇒ whole
node stays residual (D-17). `PredExpr::instantiate(&Value) -> Expr` is the instantiation hook;
`Value → Expr` is `From<Value> for Expr` (D-14), so record-valued elements already work.

**Lean TPE** (`cedar-lean/Cedar/TPE/`): a Lean TPE spec **exists** and already carries `.all`:
- `Residual.lean:49` `Residual.all (expr) (pred) (ty)` (added in Phase 5A, D-48), with arms in
  `typeOf`, `errorFree`, `evaluate` (`:170` folds via `evalAll (evaluatePred p · req es)`),
  `allLiteralUIDs`, `decResidual`, `TypedExpr.toResidual` (`:345`).
- `Evaluator.lean:288` the TPE `.all` arm is **conservative**: `.all (evaluate env e …) p ty`
  — it partially-evaluates the receiver and *always keeps the whole node* (D-17/D-43). It never
  folds a concrete receiver.
- Soundness is **already proved** for this conservative arm: `Thm/TPE/Soundness.lean:112`
  (`partial_evaluate_is_sound` `.all` case), `Thm/TPE/WellTyped.lean:185`,
  `Thm/TPE/Conversion.lean:635`. The whole Lean tree is green with these.
- Consequence: on the Lean side Phase 6.5 is **not required to add anything** — 7.4 explicitly
  permits the conservative residual. Refining Lean to fold concrete receivers is **optional**
  and carries real proof cost (Fork F2 below). The default plan is: **Lean unchanged, Rust
  refined, parity asserted by Rust-side tests** — exactly as 7.4 allows.

---

## 1. Work items (ordered)

Each item lists files, the change, and a **non-vacuous** green check (test count that must
grow, or a mutation that must break a named test). Repo build matrix for every commit:
`cedar-policy-core --lib` with **and without** `--features anyall` (0 failures, anyall count
> default count), `cargo clippy --all-features --lib`, and `lake build Cedar` only if a Lean
item was touched. Commits via `git commit -F <file>`, trailer `Co-authored-by: Claude
<noreply@anthropic.com>`.

### W1 — `ResidualKind::All` variant + `from_expr` arm (gated)
*Repo:* cedar `cedar-policy-core`. *Satisfies:* 7.2 (node exists), scaffolds 7.1/7.3.
- `src/tpe/residual.rs`:
  - Add `#[cfg(feature="anyall")] All { expr: Arc<Residual>, pred: Arc<PredExpr> }` to
    `enum ResidualKind` (mirror `TypedExpr.all` / the AST `ExprKind::All { expr, pred }`; store
    the receiver as a `Residual`, the predicate as the *raw* `PredExpr` — predicates carry no
    `Unknown`/`Slot`, D-18, so they stay un-residualized, exactly like Lean's `Residual.all`).
  - Replace the `ExprKind::All { .. } => Err(AllNotSupportedError)` arm in
    `try_from_typed_expr` with: residualize the receiver (`Self::try_from_typed_expr(expr)`),
    carry `pred.clone()`, build `ResidualKind::All`.
  - Extend the two exhaustive `match`es: `ResidualKind::all_literal_uids` (union receiver uids
    with the predicate's literal uids — add a `PredExpr`-literal-uid walk mirroring Lean's
    `PredExpr.litUIDs`, `Residual.lean:200`) and `Residual::can_error_assuming_well_formed`
    (an `.all` **can error** — QuantifierError — so return `true`, or `receiver.can_error ||
    true` = `true`; be explicit that the quantifier itself is an error source like `GetTag`).
  - `From<Residual> for Expr`: add the `ResidualKind::All` arm → `Expr::all(expr.into(),
    pred.clone())` (same `Expr::all` builder the concrete evaluator uses), so re-authorization
    round-trips.
- `src/tpe/err.rs`: once `from_expr` no longer throws it, remove the `AllNotSupported` throw;
  keep or delete the `AllNotSupportedError` struct + enum variant (deleting is cleaner — confirm
  nothing else references it; it is `#[non_exhaustive]` so removal is safe for downstream).
- **Green check:** a new `residual.rs` test `all_to_residual` parsing `principal.set.all(it ==
  "x")` to a `ResidualKind::All` and `Expr::from` round-tripping it back to a shape-equal
  `Expr::all` (mirror the existing `to_expr`/`slot_to_residual` tests). `all_literal_uids` test:
  `[User::"a"].all(it == User::"b")`-style predicate surfaces both uids. Count: `tpe` tests
  91 → ≥ 93.

### W2 — concrete-receiver evaluation in `interpret` (gated)
*Repo:* cedar `cedar-policy-core`. *Satisfies:* **7.1, 7.3**.
- `src/tpe/evaluator.rs`, new `ResidualKind::All { expr, pred }` arm in `interpret`:
  1. `let recv = self.interpret(expr);`
  2. `match &recv`:
     - `Residual::Error(_)` ⇒ `mk_error()` (receiver error propagates, matching the concrete
       evaluator).
     - `Residual::Partial{..}` ⇒ residualize: `mk_residual(ResidualKind::All { expr:
       Arc::new(recv), pred: pred.clone() })` (this is W3's job but the arm must be total; W3
       only adds the residual-element sub-case).
     - `Residual::Concrete{ value, .. }` ⇒ **fold concretely**, mirroring
       `evaluator.rs:780`'s `PartialValue::Value` branch exactly:
       - `value.get_as_set()` — non-set ⇒ `mk_error()` (concrete evaluator returns a TypeError;
         TPE collapses every error to `Residual::Error`, so `mk_error()` is the faithful image).
       - fold over elements with **no short-circuit on false** (2.8): for each `elem`,
         `self.interpret(&Residual::try_from_typed_expr(&pred.instantiate(elem) …))` — **but**
         `instantiate` yields an *un-typed* `Expr`, and `interpret` needs a `Residual` (typed).
         See **Design note D-A** below for the instantiation path. Track `all_true`,
         `any_error`, `any_residual`.
       - `any_error` ⇒ `mk_error()` (payload-free QuantifierError image). A non-bool element
         result ⇒ also `mk_error()`.
       - else `any_residual` ⇒ **W3** (keep node residual, receiver rebuilt from the concrete
         value so it is not re-folded — `ResidualKind::All { expr: Arc::new(recv), pred }`).
       - else ⇒ `mk_concrete(all_true.into())`.
- **Design note D-A (instantiation path — the one real design question of this phase).** The
  concrete evaluator instantiates `pred.instantiate(elem) : Expr` and runs the *concrete*
  evaluator. TPE's `interpret` works on `Residual`, not `Expr`. Two faithful options, pick in
  W2 and record as a decision:
  - **(A, recommended) Delegate to the concrete evaluator per element.** When the receiver is
    `Concrete`, every element `elem` is a concrete `Value`, so `pred.instantiate(elem)` is a
    closed `Expr` with no unknowns — run it through the **concrete** `Evaluator`/restricted
    evaluator already used elsewhere, or simpler: build `Expr::all(Expr::from(value.clone()),
    pred)` and evaluate the *whole* node once via the concrete evaluator path that `From<Residual>
    for Expr` + the concrete `.all` arm already implement, then wrap the `bool`/error. This
    **reuses the Phase-3 fold verbatim** (so 2.5/2.6/2.8/D-22 semantics are automatically
    identical — no re-implementation to drift). Residual elements cannot arise here because the
    receiver value is fully concrete and `pred` has no unknowns ⇒ **7.3's residual-element case
    is vacuous for a concrete receiver** (an element `Value` is concrete by construction).
    *This collapses W3 into "receiver residual ⇒ keep node", because a concrete receiver always
    fully folds.* This is the cleanest reading and should be the default.
  - **(B) Re-implement the fold inside `interpret` over `Residual`.** Only needed if we want TPE
    to *partially* evaluate a per-element predicate whose body references request unknowns while
    the element is concrete — e.g. `ctx.xs.all(it < principal.limit)` where `principal` is
    unknown. Here each instantiated predicate is itself a residual (7.3 proper). This is
    strictly more powerful and is what 7.3 literally describes, but it means re-deriving the
    QuantifierError fold over residual element results. **Decide A vs B explicitly** (Fork F1).
    If B: a concrete element whose predicate stays residual ⇒ `any_residual=true` ⇒ keep the
    whole node residual (D-17 image), which is *sound but imprecise*; genuine per-element
    residual folding (keep only the undecided elements) is a further refinement that 7.4 allows
    to defer.
- **Green check (7.1):** parity tests mirroring the 18 Phase-3 concrete `.all` parity tests, but
  through TPE with a **fully concrete** receiver + request: `[8000,9000].all(it >= 8000)` ⇒
  `Concrete(true)`; `[1,2].all(it >= 8000)` ⇒ `Concrete(false)`; empty set ⇒ `Concrete(true)`;
  an erroring element (e.g. `[1,0].all(1/it ...)` or a non-bool predicate) ⇒ `Residual::Error`
  (QuantifierError image); a **record-element** case `[{n:1},{n:2}].all(it.n >= 1)` ⇒
  `Concrete(true)` (B1 / record elements, 7.1). **Must** assert the false-then-error case ⇒
  Error, not false (2.8). Count: +≥6 tests.
- **Mutation checks (non-vacuous):** (a) short-circuit on first false ⇒ the false-then-error
  test flips to `Concrete(false)` and fails; (b) empty-set ⇒ false ⇒ the empty test fails;
  (c) treat non-bool as false ⇒ the non-bool test fails. Record in OUTCOMES.

### W3 — residual-receiver passthrough + (optional) residual-element handling (gated)
*Repo:* cedar `cedar-policy-core`. *Satisfies:* **7.2, 7.3, 7.4**.
- Under **Design-note-A** this is just the `Residual::Partial` receiver arm from W2:
  `mk_residual(ResidualKind::All { expr: Arc::new(recv), pred: pred.clone() })` — the receiver
  is partially evaluated (so `ctx`-derived sub-structure is simplified) but the quantifier is
  retained. This is the TPE-soundness-preserving image of D-17.
- Under **Design-note-B** additionally: a concrete receiver with ≥1 residual per-element
  predicate ⇒ keep the whole node residual (conservative, 7.4), with the receiver rebuilt from
  its concrete value so it is not re-folded.
- **Green check (7.2):** `principal.set.all(it == "x")` with `principal` **unknown** in the
  partial request ⇒ a `Residual::Partial { kind: ResidualKind::All { .. } }`, and
  `Expr::from(that)` re-authorized against a *completing* concrete entity store **agrees with
  the full concrete evaluator** on that completed input (the TPE soundness invariant, 7.2). Add
  a reauthorization-parity test using the existing `tpe` reauthorization harness
  (`response.rs`/`request.rs` concretization path). Count: +≥2 tests.
- **Green check (7.4 / 3.1):** confirm **non-`anyall`** `cedar-policy-core --lib` test output is
  byte-identical before/after this branch (no `All` symbol reachable without the flag). Diff the
  default-feature test count: unchanged.

### W4 — central stray-`it` guard (D-32), gated
*Repo:* cedar `cedar-policy-core`. *Satisfies:* closes open **D-32** NIT.
- D-32: the stray-`it` (the reserved `IT_SENTINEL` unknown / `item()` leaking outside a
  predicate) is currently rejected at each *entry point* (text `parse_expr`, EST `Clause`, proto
  policy bodies), not centrally; a future entry point that forgets the check would let the
  sentinel reach evaluation as a residual unknown. Phase 6.5 was named as the place to add the
  **central backstop** because TPE is the common choke point that turns typed exprs into
  residuals.
- Add the guard where `try_from_typed_expr` (or the TPE entry `Evaluator::interpret` /
  policy-level TPE) first sees the expression: if a bare `it`/`IT_SENTINEL` reaches TPE **outside**
  an `All` predicate, return a dedicated error (reuse/rename `AllNotSupported` into a
  `StrayItError`, or add `ExprToResidualError::StrayIt`). Because `PredExpr` is never residualized
  (W1), any `it` the TPE walker encounters *is* a stray one by construction — the guard is a
  single check at the `ExprKind`/`ResidualKind` leaf for the sentinel unknown/`item()` node.
- **Scope caution:** confirm this does not reject *legitimate* uses already lowered correctly
  (`principal.it`, `{it: 1}`, `has it` — D-26). The guard targets only the reserved sentinel
  Unknown, not the attribute/key string `"it"`.
- **Green check:** a test feeding a hand-built typed expr containing a stray sentinel (bypassing
  the parser entry guards) ⇒ the new error, and a mutation that removes the guard ⇒ that test
  fails (the sentinel would otherwise residualize). Confirm all existing parser-entry stray-`it`
  tests still pass. Count: +≥1 test.
- **Decision to flag:** if a central guard would duplicate rather than replace the entry-point
  checks, land it as a *backstop* (defence in depth), not a removal of the existing checks
  (removing them widens the trusted surface). Record as a D-32-resolution decision.

### W5 — Lean TPE side: **note-only** (default) OR concrete-fold refinement (fork)
*Repo:* cedar-spec `cedar-lean`. *Satisfies:* 7.1/7.2 on the Lean surface (if done).
- **Default (recommended, matches 7.4):** **no Lean change.** The Lean TPE `.all` arm
  (`Evaluator.lean:288`) already residualizes conservatively and is already proved sound
  (`Soundness.lean:112`). This is a *correct* TPE (7.2/7.4) — it just never folds a concrete
  receiver. Record in OUTCOMES + a DECISIONS entry that the Lean TPE intentionally keeps the
  conservative arm; Rust is strictly more precise, which is sound (a more-reduced residual that
  still re-evaluates to the same value). **No `lake build` risk.**
- **If the owner wants Lean parity (Fork F2):** refine `Evaluator.lean:288` to fold a concrete
  receiver via `evalAll (evaluatePred p · req es)` (the same combinator the *concrete* Lean
  evaluator and `Residual.evaluate` already use), returning a `Residual.val`/error. Then re-prove
  the `.all` case of `partial_evaluate_is_sound`: the fold's soundness is exactly
  "`evalAll (evaluatePred p ·) s` on the concrete `s` equals the concrete evaluator's `.all`",
  which the Phase-5A `type_of_all_is_sound` machinery (`evalAll_bool_or_qerr`, All.lean) gives.
  **Cost:** one new soundness sub-lemma + edits to `Soundness.lean:112`,
  `PreservesTypeOf.lean`, `Conversion.lean`. This is the only Lean-proof risk in the phase and
  is **optional under 7.4** — do it only if the owner wants Lean to match Rust's precision.

### W6 — docs / decisions / tasks
*Repo:* cedar-spec. *Satisfies:* traceability.
- `branches/phase6.5-anyall-tpe/OUTCOMES.md` (new) — commits, as-built, verification counts,
  mutation results, review loop, the A/B and Lean forks' resolutions.
- `DECISIONS.md` — new entries: D-A (instantiation path A vs B), D-32 resolution (central
  backstop vs replacement), Lean conservative-vs-fold decision.
- `tasks.md` — flip Phase 6.5 row to **IN-PROGRESS** with a PLAN pointer (done in this commit;
  see §4).

---

## 2. What review must blind-verify
(Independent fresh-context reviewer; env preamble: `export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"; unset LD_PRELOAD`.)
1. **Non-`anyall` build is byte-unchanged** (3.1/7.4): default `cedar-policy-core --lib` count
   and output identical before/after; no `All`/`ResidualKind::All` symbol reachable without the
   flag; `cargo check --no-default-features` and default both clean.
2. **Concrete-receiver parity (7.1)** is *semantic*, not structural: for a sample of concrete
   `.all`/`.any` policies the TPE result equals the **concrete evaluator**'s result (true /
   false / QuantifierError-image), **including** the false-then-error ⇒ Error case (2.8) and a
   **record-valued element** (B1). Verify the parity tests actually run (count > 0) and fail
   when the fold is mutated (short-circuit / empty-set / non-bool mutations each break a named
   test).
3. **Residual-receiver soundness (7.2)**: the emitted residual `All`, re-authorized on a
   completing concrete store, equals full concrete evaluation on the completed input — not just
   "produces some residual". Confirm the reauthorization-parity test exercises a genuinely
   unknown receiver.
4. **D-A instantiation path**: whichever of A/B was chosen, verify a concrete receiver with a
   predicate that *reads request unknowns* behaves as claimed (A: whole node residual via the
   `Partial` receiver only — note a concrete receiver + unknown-reading predicate under A still
   folds per element against the concrete element but the predicate residualizes, so confirm the
   chosen arm's actual behaviour on `ctx.xs.all(it < principal.limit)` with unknown `principal`).
5. **Stray-`it` guard (D-32)** is a backstop that does **not** loosen the existing entry-point
   checks and does **not** reject legitimate `it`-named attributes/keys (D-26 cases still pass).
6. **Lean**: if W5 default, confirm `lake build Cedar` is untouched/green and the conservative
   arm is still the one in the tree; if W5 fork, `#print axioms` on the refined `.all` soundness
   case shows no new axioms beyond the baseline `{propext, Classical.choice, Quot.sound}`.

---

## 3. Risks & genuine user-decision forks

**Forks (need an owner call):**
- **F1 — instantiation path A vs B (Design-note-A).** A (concrete receiver ⇒ always fully
  folds; 7.3 vacuous) is simpler and is the recommended default. B (re-fold with per-element
  residual retention, enabling per-element partial evaluation when the predicate reads unknowns)
  is literally what 7.3 describes and is strictly more precise, at the cost of re-deriving the
  QuantifierError fold. **7.4 permits A.** Default: **A**; escalate only if the owner wants the
  extra TPE precision of B.
  > **Correction (review round 1, Finding 3):** the planning text here originally said A would
  > "delegate to the verified Phase-3 fold … reused verbatim". As BUILT, A **re-implements** the
  > fold over `Residual` (per-element `instantiate` + `interpret`), it does NOT delegate to the
  > `evaluator.rs:780` concrete arm. The two folds are independent paths pinned to the same
  > answers by `concrete_fold_matches_phase3_evaluator` (parity by tests, not code reuse). Sound
  > because TPE's error algebra is kind-free; the Phase-3 `RecursionLimit` (D-22) distinction is
  > re-created only at re-authorization. See DECISIONS D-80 (corrected).
- **F2 — Lean concrete-fold (W5).** Default: Lean TPE stays conservative (sound, 7.4-permitted,
  zero proof risk). Fork: refine Lean to fold concrete receivers for Rust/Lean parity (one
  soundness sub-lemma + three proof-file edits). Recommend **default** unless the owner wants the
  Lean TPE spec to match Rust's precision.
- **F3 — DRT TPE differential.** The seed asks about "DRT TPE differential wiring under the
  anyall flag", but **there is no TPE differential target in cedar-drt today** (TPE is unit/parity
  tested in `cedar-policy-core`). Options: (i) **no DRT work** — rely on in-crate parity tests
  (recommended; matches how TPE is tested across the whole project); (ii) add a *new* TPE
  differential target comparing Rust TPE vs Lean TPE FFI, which is a sizeable new harness and, if
  Lean stays conservative (F2 default), would only compare the conservative Lean arm against
  Rust's folding — i.e. they'd *disagree* on concrete receivers unless the comparison is
  "re-authorized residual agrees", not "residual shape agrees". **Recommend (i).** Flag (ii) as
  out-of-scope-for-6.5 (a possible Phase-6-style follow-up) unless the owner wants it.

**Risks (handle in-plan, not owner calls):**
- **R1 — totality of the `interpret` arm.** The new arm must cover Error/Partial/Concrete
  receivers; a missing case is a non-exhaustive match (compile error) — caught by the build.
- **R2 — `can_error_assuming_well_formed` for `All`.** Must return `true` (QuantifierError is a
  genuine runtime error source, like `GetTag`/arith). Getting this wrong would let a downstream
  simplification drop a possibly-erroring `.all` — mutation-test it.
- **R3 — `PredExpr` literal-uid walk** (W1) must mirror Lean's `PredExpr.litUIDs` so
  `all_literal_uids` (used by the batched/reauth entity loader) does not miss uids a predicate
  references; otherwise reauthorization could load an incomplete store. Test with a predicate
  containing a literal EntityUID.
- **R4 — rebase onto Phase 6 tip** (see header). Phase 6 touches the generator/differential, not
  TPE, so expected text-only; re-run the matrix after.
- **R5 — D-32 guard false-positives** (W4): must not reject D-26's legitimate `it`
  attribute/key uses. Test those stay green.
- **R6 — anyall gating leaks.** Every new item is `#[cfg(feature="anyall")]`; a stray
  non-gated reference breaks the default build. The default-vs-anyall matrix catches it.

---

## 4. Commit sequence (both repos, bottom-up)
1. cedar-spec: this PLAN.md + tasks.md Phase 6.5 → IN-PROGRESS (this commit; no code).
2. cedar: W1 (`ResidualKind::All` + `from_expr` + exhaustive matches + `From` arm + W1 tests).
3. cedar: W2 (concrete-receiver fold + parity/mutation tests).
4. cedar: W3 (residual-receiver passthrough + reauth-parity test; 3.1 unchanged check).
5. cedar: W4 (central stray-`it` backstop + test) — may land with W1 if the guard sits in
   `try_from_typed_expr`.
6. cedar-spec (+ cedar-lean if F2-fork chosen): W5 Lean decision/refinement.
7. cedar-spec: W6 OUTCOMES + DECISIONS (D-A, D-32-resolution, Lean fork).

Green check after **every** cedar commit: `cedar-policy-core --lib` default + `--features
anyall` (anyall count strictly greater, 0 failures) and `cargo clippy --all-features --lib`
clean; `lake build Cedar` after any cedar-lean commit.
