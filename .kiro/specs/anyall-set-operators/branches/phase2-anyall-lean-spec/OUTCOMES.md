# Phase 2 Outcomes — Lean spec node + evaluator (`phase2-anyall-lean-spec`)

Scope: `cedar-lean/` only (cedar-spec repo). The cedar repo branch exists with no changes.

## Commits (cedar-spec)

| SHA | What |
|---|---|
| `beeec77` | PLAN.md (fresh plan agent `af789f9b`) |
| `b58a4fd` | C1 — `Error.quantifierError` |
| `ce91a4b` | C2 — `PredExpr` inductive, `Expr.all`, `evaluatePred` + `evalAll`, the `.all` arm in every total `Expr` match (Spec and Thm, about 25 files, no `sorry`) |
| `f7239bf` | C3 — 16 Lean unit tests (`UnitTest/AnyAll.lean`) |
| `ffb0fed` | Review round 1 fixes (doc comment on the well-formed-set precondition, reversed-order test, typeOf comment cites D-11) |
| `363a661`, `cb2b3f0`, `0c23bb5`, `3b31c15` | DECISIONS.md and tasks.md status |

## What the evaluator does
- Receiver must be a set (`Result.as (Set Value)`): a non-set is `typeError`; a receiver error propagates unchanged.
- Every element goes through `evaluatePred` with `it` bound to the full element `Value`; a predicate error or a non-boolean result on any element makes the whole expression `quantifierError` (payload-free, so trivially order-independent).
- Otherwise the result is the conjunction; the empty set is `true`.
- `List.mapM` stops only at an error, never at `false` (req 2.8). Verified by mutation: a version that short-circuits on `false` fails two tests.
- No Lean `any`: the Rust builder lowers `any` to `!all(!p)` before DRT.

## Deviations from the plan / tasks.md
- `typeOf` conservatively rejects `.all`; the sound type rule (T2.3, req 6.1/6.4) is deferred — **D-11, open for the owner**.
- The constructor broke more total matches than the plan listed: `Concretizer`, `Validator` (`checkEntities`, `mapOnVars`), `Enforcer.footprint`, `SymCCOpt.compile`, and `UnitTest/CedarProto` (`mkWf`), plus about 20 Thm proofs. Each got a faithful arm or a vacuous case justified by the conservative `typeOf`/`compile`.
- `evaluatePred` (threading `it`) was used instead of `PredExpr.instantiate`.
- New supporting definitions: `PredExpr.ValidRefs`, `Expr.ValidRefs.all_valid`, `PredExpr.entityUIDs`, `checkPredEntities`, `PredExpr.mkWf`, `evalAll_ok_bool`, `all_produces_bool`.

## Verification
- `lake build Cedar` green (586 jobs); `lake build DiffTest UnitTest CedarProto CedarFFI SymTest CedarUnitTests` green.
- `CedarUnitTests`: 464 tests, 0 failures (447 before; 17 anyall tests).
- Host quirk: linking `CedarUnitTests` needs `LIBRARY_PATH` pointing at the Lean toolchain libs (D-13).

## Review loop
| Round | Agent | Verdict |
|---|---|---|
| 1 | `ccd4f50d` | No blockers; 2 SHOULD-FIX + 1 NIT, fixed in `ffb0fed` |
| 2 | `5e06442b` | **NO ACTIONABLE FINDINGS** — also confirmed Lean `PredExpr` matches the Rust `PredExprKind` one-to-one (Rust `Like`/`Is` map to Lean `unaryApp (.like/.is)`) |

## Follow-ups for later phases
- Phase 3: Rust evaluator must match these semantics exactly (payload-free quantifier error, no `false` short-circuit, receiver error unchanged).
- Phase 5: SymCC `compile`/footprint for `.all` (currently reject / empty).
- Phase 6: `cedar-lean-ffi` decoders (`datatypes.rs`, `messages.rs`, `tpe.rs`) need an `All`/`PredExpr` arm; the validation differential must expect the Lean typechecker to reject `.all` while D-11 stands.
- Any future soundness lemma for `evalAll` needs a well-formed-set hypothesis.
