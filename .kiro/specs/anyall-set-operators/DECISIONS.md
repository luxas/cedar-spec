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
