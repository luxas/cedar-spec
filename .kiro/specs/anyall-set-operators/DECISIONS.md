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
| D-07 | 1 | Protobuf serialization of `All` is `unimplemented!` (mirrors the existing `Error` arm). No phase in the spec adds a protobuf `All` message; it stays unsupported unless you want one. | OPEN |
| D-08 | 2 | Lean `Expr.all` is unconditionally present (Lean has no `#[cfg]`); gating is only on the Rust/DRT side. `Features.anyAll` stays `false` and unused. | SETTLED |
| D-09 | 2 | Lean `PredExpr` is a separate restricted inductive (no `set`, no `all`), not `Expr` + a well-formedness predicate. | SETTLED |
| D-10 | 2 | Lean `quantifierError` carries no payload (req 2.6 is conditional on a payload; none means trivially bounded and deterministic). | SETTLED |
| D-11 | 2 | **Lean typechecker keeps rejecting `.all` (no Lean type rule / soundness proof yet).** See details: needs your call. | **OPEN — needs decision** |
| D-12 | 2 | `Validator.mapOnVars` (action substitution for typing precision) does not descend into the predicate. Only precision is affected. | SETTLED |
| D-13 | 2 | Building the `CedarUnitTests` exe needs `LIBRARY_PATH=<lean toolchain>/lib:<lean toolchain>/lib/lean` on this host (static libc++/gmp/uv). Host quirk, not a code change. | SETTLED |

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
Policies containing `.all`/`.any` cannot be protobuf-serialized under
`--features protobufs,anyall` (panic via `unimplemented!`). Options: keep as is,
return an error instead of panicking, or add a proto message (schema change).

### D-11 — Lean type rule and soundness for `.all` (req 6.4) — NEEDS DECISION
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

**Current choice: 3**, because it is sound and reversible and blocks nothing
in Phases 3–5. Phases 3–8 proceed on it unless you pick 1 or 2.
