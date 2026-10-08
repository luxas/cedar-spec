# anyall-set-operators — Decision log

Minor decisions taken autonomously during implementation that the owner may
want to revisit. Each entry: context, the choice, why, and how to reverse it.
Critical (one-way-door) decisions are escalated instead of logged here.

Status legend: **OPEN** = worth a look; **SETTLED** = low risk, recorded for traceability.

| # | Phase | Decision | Status |
|---|---|---|---|
| D-01 | all | "Up to phase 9" interpreted as the end of the branch stack (spec Phase 8, `phase8-anyall-benchmarks`); the spec has no Phase 9. | OPEN |
| D-02 | 0 | Phase 0 branch keeps its historical off-by-one name `1-anyall-feature-flags`; branches from Phase 1 on are `phaseN-anyall-<desc>`. | SETTLED |
| D-03 | 0 | Per-branch PLAN/OUTCOMES docs live only in cedar-spec (layout A); cedar-repo SHAs are referenced by hash. | SETTLED |
| D-04 | 1 | `ExprBuilder` trait gains gated `type Pred` + `all` + `pred_from_ast` (option B2). EST/PST `all()` is `unreachable!` until Phase 4 adds their form. | OPEN |
| D-05 | 1 | `Expr::any` is a free constructor (`!all(!p)`), not a trait default method, because `negate` lives on `PredExpr`. | SETTLED |
| D-06 | 1 | Phase-1 placeholders: evaluator returns `non_value`, typecheck conservatively fails, TPE/entity-manifest/protobuf reject `All` with an "unsupported" error. Each is replaced in its owning phase. | SETTLED |
| D-07 | 1 | Protobuf serialization of `All` is `unimplemented!` until Phase 4 T4.3 adds the proto form (correction: the spec does plan it). | SETTLED |
| D-08 | 2 | Lean `Expr.all` is unconditionally present (Lean has no `#[cfg]`); gating is only on the Rust/DRT side. `Features.anyAll` stays `false` and unused. | SETTLED |
| D-09 | 2 | Lean `PredExpr` is a separate restricted inductive (no `set`, no `all`), not `Expr` + a well-formedness predicate. | SETTLED |
| D-10 | 2 | Lean `quantifierError` carries no payload (req 2.6 is conditional on a payload; none means trivially bounded and deterministic). | SETTLED |
| D-11 | 2 | **Lean typechecker keeps rejecting `.all` (no Lean type rule / soundness proof yet).** See details: needs your call. | RESOLVED by user 2026-10-08: Full type rule (implemented in Phase 5, part A) |
| D-12 | 2 | `Validator.mapOnVars` (action substitution for typing precision) does not descend into the predicate. Only precision is affected. | SETTLED |
| D-13 | 2 | Building the `CedarUnitTests` exe needs `LIBRARY_PATH=<lean toolchain>/lib:<lean toolchain>/lib/lean` on this host (static libc++/gmp/uv). Host quirk, not a code change. | SETTLED |
| D-14 | 3 | Rust evaluates a predicate by instantiating `PredExpr → Expr` (element via `From<Value> for Expr`) and reusing the evaluator; Lean threads `it` instead. Same semantics. | SETTLED |
| D-15 | 3 | Rust `QuantifierError` is payload-free, like Lean (D-10). | SETTLED |
| D-16 | 3 | A non-bool predicate result is a `QuantifierError`, not a `TypeError` (matches Lean). Watch in the Phase 6 differential. | SETTLED |
| D-17 | 3 | Partial evaluation residualizes the whole `All` node if the receiver or any element predicate is residual. Refined per-element TPE is Phase 6.5. | SETTLED |
| D-18 | 3 | `subexpressions()`/`slots()`/visitors stay receiver-only (`PredExpr` has no `Slot`/`Unknown`); `level_validate` descends into the predicate. | SETTLED |
| D-19 | 3 | Validator types predicates with a parallel `typecheck_pred(it_ty)`, which also enforces req 1.5 (no set-typed subterm). | SETTLED |
| D-20 | 3 | Req 1.4 (no nesting) and 1.6 (`it` outside a predicate) are unrepresentable in the Rust AST; they are enforced by the Phase 4 parser / EST→AST conversion, not by `try_validate`. | SETTLED |
| D-21 | 3 | The validator types a predicate by instantiating `it` with a reserved unknown (`__cedar::anyall::it`) that a nested typechecker types as the element type, instead of a parallel `typecheck_pred` (refines D-19). Reuses every existing typing rule; the reserved name cannot be written in policy text. | SETTLED |
| D-22 | 3 | In the Rust evaluator, a `RecursionLimit` error inside a predicate propagates unchanged rather than becoming `QuantifierError` (it is an implementation limit with no Lean counterpart). | OPEN — check in Phase 6 differential |
| D-23 | 3 | Level validation: dereferencing `it` is charged the level of the receiver's elements (max over a set literal's elements). | SETTLED |
| D-24 | 3 | When an `.all` receiver is not a set, the predicate is still typechecked with `it : Never`, which can add cascade errors next to the "expected set" error. Sound (the policy is rejected); diagnostics could be tightened later. | OPEN — diagnostic quality |
| D-25 | 4 | In every builder, `it` is built as `item()`: the reserved unknown `IT_SENTINEL` for AST/PST and a dedicated `{"it": {}}` node for EST. Converting to a predicate turns it into `PredExprKind::Item`. | SETTLED |
| D-26 | 4 | `it` is not a reserved word: under `anyall` a bare `it` used as a value is the element keyword, and is rejected outside a predicate after the whole expression is built (req 1.6). `principal.it`, `{it: 1}`, `has it` still work. Off-build is unchanged. | SETTLED |
| D-27 | 4 | Protobuf: `All { arg, pred: Expr }` (field 17) plus an empty `Item` message (field 18) for `it`; decode re-checks the predicate (untrusted bytes). | SETTLED |
| D-28 | 4 | Printing does not re-sugar `.any`: it prints as `!e.all(!p)`, the lowered normal form req 4.1/4.3 allow. | SETTLED |
| D-29 | 4 | The Lean protobuf decoder (`CedarProto`) gets its `All`/`Item` arms in Phase 6, when DRT first sends `.all` to Lean. | SETTLED |
| D-30 | 4 | The PST `All` node holds the already-checked AST `PredExpr` (keeps PST→AST conversion infallible); the EST holds a full expression, checked on conversion to the AST. | SETTLED |
| D-31 | 4 | **Pre-existing, not caused by this work:** `cedar-drt/fuzz` does not compile against the nested cedar checkout (`proto_gen.rs` expects `BTreeMap` proto records, cedar-spec `4149769`, but cedar's `build.rs` does not configure that). Phase 6 needs the fuzz targets, so it must align the cedar checkout or the generator. | OPEN — blocks Phase 6 fuzzing |
| D-32 | 4 | The stray-`it` check runs at each entry point (text `parse_expr` and policy conditions, EST `Clause`, proto policy bodies), not centrally. A future entry point that forgets it would let the sentinel reach evaluation as a residual unknown instead of an error. Optional hardening: a central guard (e.g. in partial evaluation / TPE). Revisit in Phase 6.5. | OPEN (review NIT) |
| D-33 | 5 | **CRITICAL, go/no-go for Phase 5.** SymCC compiles only well-typed input, and the Lean `typeOf` rejects every `.all` (D-11), so a SymCC arm and its proofs would be unreachable ("green but empty"). Options: (1) implement the full Lean type rule first, then the SymCC encoding (D-34); (2) literal-set-only SymCC arm, still needing some type rule or a test shim; (3) defer Phase 5. See `branches/phase5-anyall-symcc/PLAN.md` §2-§3. | RESOLVED by user 2026-10-08: option 1 (full type rule, then SymCC bounded quantifier) |
| D-34 | 5 | Proposed encoding for symbolic set receivers: first-order bounded quantifier `forall x. x in S => P(x)` under SMT logic `ALL` (measured decidable on cvc5 1.4.1), not higher-order `set.all` (needs `HO_ALL`), not literal-only. Needs a new bound-variable term and quantifier op in the trusted SymCC IR, with semantics and proofs. | SETTLED (user chose option 1) |
| D-35 | 5 | The SymCC `.all` term encodes three outcomes (true / false / quantifierError), matching `evalAll`. | PROPOSED |
| D-36 | 5 | The DRT symcc differential compares Rust and Lean SMT-LIB byte for byte, so the Rust `cedar-policy-symcc` must mirror the chosen encoding (Phase 6). | PROPOSED |
| D-37 | 5 | The Lean type rule for `.all` (originally T2.3) lands at the start of branch `phase5-anyall-symcc` as "part A", before the SymCC work ("part B"), instead of reopening the Phase 2 branch. The branch number still matches the phase that needs it. | SETTLED |
| D-38 | 5A | Type the predicate by reusing `typeOf` on the predicate's expression with `it` as a typed placeholder (as the Rust validator does, D-21), so the existing `type_of_is_sound` covers the predicate body. Fallback: a typed predicate mirror. | SETTLED |
| D-39 | 5A | `.all` returns the enclosing capabilities; capabilities learned inside the predicate (e.g. `it has a`) are dropped at the quantifier boundary. | SETTLED |
| D-40 | 5A | One helper lemma (a `quantifierError` result implies the expression is an `.all`) discharges the new `EvaluatesTo` case in every non-`.all` proof. Later-phase stubs are explicit, never `sorry` or a silent wildcard. | SETTLED |
| D-41 | 5A | Req 1.5 differs in mechanism: Lean excludes set terms structurally (`PredExpr` has none), Rust checks at type-check time (D-19). Verdicts agree; the Phase 6 differential compares accept/reject, not error codes. | SETTLED |
| D-42 | 5A | `.all` soundness assumes the receiver set is well-formed, which holds for every evaluator-produced set; a proof hypothesis, not a runtime assumption. | SETTLED |
| D-43 | 5A | Part A adds only the minimal TPE exhaustiveness arm (whole-node residual, as D-17); per-element TPE stays in Phase 6.5. | SETTLED |
| D-44 | 5A | D-38 locked to option (b): the predicate is typed by `typeOfPred`, which types `PredExpr` by reusing the existing per-operator `typeOf*` helpers with `it` (`.item`) pinned to the element type `τ` — a typed placeholder in the typing world, mirroring Rust's reserved-unknown `it` (D-21). Evidence gathered this session: (i) `evalAll` collapses every per-element predicate error into one `quantifierError` (`Spec/Evaluator.lean`), so `EvaluatesTo` needs exactly ONE new disjunct and the predicate's three allowed errors never thread through the quantifier; (ii) `quantifierError` occurs ONLY in `Spec/Value.lean`+`Spec/Evaluator.lean`, so the ripple helper `quantifierError_implies_all` is provable by cases on `evaluate`; (iii) the per-operator soundness lemmas (e.g. `type_of_unaryApp_is_sound`) are stated over the full `Expr` `typeOf`/`evaluate`, so option (a)'s predicate-world mirror would re-prove each operator (the ~6.5k-line fear) — option (b) reuses the predicate-body soundness via the `evaluatePred`↔`evaluate (p.toExpr …)` bridge (Lemma L3) instead. | SETTLED |
| D-45 | 5A | C1 (TypedExpr.all + typeOfAll) cannot build green alone: adding the constructor makes every exhaustive `TypedExpr` match non-exhaustive and `type_of_is_sound`'s `.all` arm can no longer close vacuously. Therefore C1+C2+C3 (constructor + type rule + `EvaluatesTo` extension + all ripple arms + `type_of_all_is_sound`) land as ONE atomic commit, as PLAN-A §7 anticipated. Foundation lemmas that DO build on their own (`quantifierError_implies_all`, the `evalAll` fold lemma, the `evaluatePred` bridge) land as green commits first. | SETTLED |
| D-46 | 5A | **Soundness simplifier (supersedes D-40 helper + L3 for soundness).** `evalAll` ALWAYS yields `ok (bool _)` or `quantifierError` for ANY per-element function (`evalAll_bool_or_qerr`), because `.as Bool` masks every non-bool/erroring element. So `type_of_all_is_sound` needs only: receiver IH + set-type inversion (`instance_of_set_type_is_set`) + the one new `EvaluatesTo` `quantifierError` disjunct. The predicate's own soundness (L3/`typeOfPred` soundness) is NOT needed for quantifier soundness — the type rule's bool/set checks give Rust-parity rejection only. `quantifierError_implies_all` (D-40) is dropped: it is false (`.set [erroring .all]` yields `quantifierError`). Verified: `#print axioms type_of_is_sound` and `type_of_all_is_sound` = {propext, Classical.choice, Quot.sound}, no `sorryAx`. | SETTLED |
| D-47 | 5A | **Level validation rejects `.all` (sound-conservative), superseding the receiver-only idea.** A predicate can dereference `it` (an entity element) via `getAttr`/`hasTag`/etc., so a slicing-sound level rule must charge those dereferences (D-23). That per-predicate level descent is deferred; until then `checkLevel (.all …) = false` and there is no `AtLevel.all` constructor, so `.all` is never level-valid. This is sound (never deems an unsound policy level-valid) and keeps `level_based_slicing_is_sound`/`level_based_no_dne` honest. The main `type_of_is_sound` rule is unaffected. | SETTLED |
| D-48 | 5A | **TPE: `Residual.all` is a faithful whole-node residual (supersedes the D-43 `.error` stub).** `TypedExpr.toResidual` must preserve evaluation (`conversion_preserves_evaluation`), which the `.error` stub broke. So a `Residual.all (receiver p ty)` constructor was added, mirroring `TypedExpr.all`; `Residual.evaluate`/`.typeOf`/`.allLiteralUIDs`(+`PredExpr.litUIDs`)/`decResidual`/`toResidual`/TPE `evaluate` and the `Residual.WellTyped.all` + TPE soundness/typeof/well-typed proofs all gained `.all` arms. Per-element TPE reduction of `.all` stays Phase 6.5. | SETTLED |
| D-49 | 5A | **SymCC completeness is coupled to Part B and NOT closed in Part A.** Making the Lean `typeOf` accept `.all` makes `.all` a well-typed expression, but SymCC `compile` still rejects it (`unsupportedError`, Part B / D-33/D-34). So every SymCC *completeness* theorem that asserts "SymCC succeeds on well-typed input" (`compile_well_typed`, the verifier `verify*_is_ok` chain, and especially the optimizer biconditionals `compile_ok_iff_welltypedpolic{y,ies}_ok` and the ~24 `*Opt?_eqv_*_ok` theorems in `Thm/SymCC/Opt.lean`) becomes false for `.all`. A `TypedExpr.NoQuantifier` precondition was added and threaded through `compile_well_typed`, `Verifier/WellTypedOk.lean` and `WellTypedVerification.lean` (all green), but it CANNOT be threaded into `Opt.lean`: those theorems' hypothesis is `compile … = .ok` (compilation succeeded), and compile-success does NOT imply quantifier-free (`compileIf` can short-circuit an unforced branch), so `NoQuantifier` is not derivable there. Restoring `Opt.lean` requires Part B's real SymCC `.all` encoding (which makes `compile .all` succeed and the biconditionals hold again). Consequence: with these Part-A changes in the tree, `lake build Cedar` is RED only at `Thm/SymCC/Opt.lean`; everything else — the full `.all` type rule, soundness, well-typedness, levels, TPE, validator, and SymCC verifier API — is green. | OPEN — closed by Part B |
| D-50 | 5 | Because of D-49, part A cannot be committed green alone. It is saved on the side branch `phase5-anyall-symcc-wip-partA` (commit `73eae36`, red only in `Cedar/Thm/SymCC/Opt.lean`). Part B continues there. When the tree is fully green, the work is re-landed on `phase5-anyall-symcc` as logical commits that each build, and the WIP branch is kept only as history. | SETTLED |

## Details

### D-01 — "phase 9"
The tasks.md phases are 0, 1, 2, 3, 4, 5, 6, 6.5, 7, 8 (ten phases). If you
meant something beyond Phase 8, say so; otherwise the stack ends at
`phase8-anyall-benchmarks`.

### D-04 — builder trait surface
`Expr::try_into_expr<B>` is generic over the builder, so an `All` arm must go
through a trait method; this forced the trait change. Reversal cost grows each
phase. Phase 4 replaces the EST/PST `unreachable!` with real forms.

### D-07 — protobuf `All`
Until Phase 4 (T4.3), serializing a policy containing `.all`/`.any` under
`--features protobufs,anyall` panics via `unimplemented!`. Phase 4 replaces
this with the real proto form and a round-trip test.

### D-11 — Lean type rule and soundness for `.all` (req 6.4) — RESOLVED 2026-10-08: Full rule (user), see D-33, D-37
**Where it stands.** Phase 2 landed the Lean node, the evaluator (RFC 0021
semantics, 16 unit tests) and every proof repair, with the Lean `typeOf`
conservatively returning a type error for `.all`. That is sound (the
validator never accepts what it cannot justify), but the Lean validator then
rejects every `.all` policy.

**Why the real rule is large.** `type_of_is_sound` promises a typed expression
evaluates to a value of its type or to an *allowed* error (`EvaluatesTo`:
entityDoesNotExist / extensionError / arithBoundsError). A well-typed `.all`
can produce `quantifierError` (it wraps any predicate error, including the
allowed ones), so (a) `EvaluatesTo` must also admit `quantifierError`, which
touches every proof that destructs it; and (b) typing the predicate needs a
`typeOfPred` over `PredExpr` with its own soundness proof, mirroring about
6.5k lines of existing per-operator lemmas, plus a `TypedExpr.all` mirror and
the Levels/slicing proofs.

**Options.**
1. *Full* (spec as written): add `typeOfPred`, `TypedExpr.all`, extend
   `EvaluatesTo`, prove soundness. Largest; days of proof work.
2. *Receiver-only rule*: `E : Set τ ⇒ E.all(P) : Bool`, predicate unchecked,
   plus `EvaluatesTo` admitting `quantifierError`. Small proof cost, but Lean
   would accept ill-typed predicates that the Rust validator rejects, so the
   validator differential must treat that as expected.
3. *Keep conservative* (current): Lean rejects `.all`; Rust validator (Phase 3)
   implements the real rule; the Phase 6 validation differential excludes
   `.all` (or expects Lean rejection). Req 6.4 stays unmet.

**Choice: 1 (Full)**, chosen by the user on 2026-10-08 when Phase 5 showed
SymCC cannot be non-vacuous without it (D-33). Option 3 was the interim
choice through Phase 4. Implemented as part A of `phase5-anyall-symcc` (D-37).
