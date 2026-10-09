# Phase 3 Outcomes — Rust evaluator + validator (`phase3-anyall-rust-eval-validator`)

Scope: cedar repo (`cedar-policy-core`, `cedar-policy`); cedar-spec only docs.

## Commits

| Repo | SHA | What |
|---|---|---|
| cedar-spec | `a07efc5` | PLAN.md (fresh plan agent `4916e70b`) |
| cedar | `a409133e` | C1 — gated, payload-free `EvaluationError::QuantifierError` |
| cedar | `911ee3ea` | C2 — evaluator `All` arm with the Lean semantics; `PredExpr::instantiate`; 18 parity tests |
| cedar | `78c79bc5` | C3 — validator type rule (`it` typed as the element type), `ValidationError::SetTermInQuantifier` (req 1.5, mirrored in cedar-policy), 12 tests |
| cedar | `05adec3d` | C4 — level validation descends into the predicate; validator entity/text walks see predicate leaves; 6 tests |
| cedar | `c65d955a` | Review round 1 NITs (comments only) |
| cedar-spec | `7e19d3f`, `5044b73` | DECISIONS D-14..D-23 |

## As built
- **Evaluation:** receiver non-set → `TypeError`; receiver error unchanged; any element whose instantiated predicate errors or is not boolean → `QuantifierError`; otherwise conjunction, `true` on empty; no short-circuit on `false`. `RecursionLimit` inside a predicate propagates as is (D-22). Residual receiver or element → the whole node stays residual (D-17).
- **Typing:** receiver must be a set; the predicate is instantiated with a reserved placeholder for `it` and typechecked by a nested typechecker whose `it_type` is the element type (`Never` if unknown), so every existing typing rule, capability and strict-mode check applies inside the predicate (D-21). The typed predicate is stored on the annotated node (`PredExpr::from_instantiated`). Any set-typed sub-expression of the predicate, including `it` itself, raises `SetTermInQuantifier`.
- **Levels:** dereferencing `it` is charged the level of the receiver's elements (max over a set literal's elements) (D-23).
- **Walks:** `subexpressions()`/`slots()` stay receiver-only (nothing to find: `PredExpr` has no slot/unknown, D-18); the validator's entity-UID, entity-type and text walks include predicate leaves (parity with Lean `checkPredEntities`).
- Not in scope, unchanged: entity manifest (unsupported error), TPE (Phase 6.5), protobuf/EST (Phase 4).

## Verification
- Build matrix 8/8: core default / anyall / anyall+tolerant-ast / experimental / all-features (with `--tests`); cedar-policy default / experimental / all-features.
- `cargo clippy --all-features` (lib, which is what CI runs) clean for core and cedar-policy.
- `cedar-policy-core --lib`: 1562 tests (default) → **1610** with `anyall` (+48), 0 failures. cedar-policy: 429.
- Mutation checks: short-circuit-on-false fails 3 evaluator tests; disabling the set-term check fails 2 validator tests; charging `it` level 0 fails 2 level tests.

## Review loop
| Round | Agent | Verdict |
|---|---|---|
| 1 | `0bd2c9d0` | **NO ACTIONABLE FINDINGS**; 3 optional NITs (2 comments applied in `c65d955a`; NIT-1 logged as D-24) |

## Follow-ups
- Phase 4: parser for `.all(...)`/`.any(...)` and `it`; reject `it` outside a predicate and nested quantifiers at CST/EST→AST (req 1.4/1.6, D-20); EST/PST/protobuf `All` forms replace the `unreachable!`/`unimplemented!` placeholders.
- Phase 6: `cedar-drt/fuzz/fuzz_targets/validation-pbt.rs` has an exhaustive `EvaluationError` match that needs a `QuantifierError` arm under `anyall`; the validation differential must expect Rust-accept / Lean-reject on `.all` while D-11 stands; check D-22 (recursion limit) in the eval differential.
