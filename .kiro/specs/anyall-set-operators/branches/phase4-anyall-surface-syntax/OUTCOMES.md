# Phase 4 outcomes — Rust surface syntax + roundtrip (`phase4-anyall-surface-syntax`)

## Result
DONE. Review converged in 1 round (reviewer `d3563724`: NO ACTIONABLE FINDINGS, 2 NITs).

## Commits
cedar (nested repo):
- `408ced71` C1/C2: EST `all`/`it` nodes, PST `All`, builder `item()` / `pred_from_expr()`,
  `PredExpr::try_from_expr` with precise errors (nesting, set term, unsupported). Replaces the
  Phase 1 EST/PST `unreachable!` placeholders.
- `0ee7bc97` C3: parser. `e.all(p)` / `e.any(p)` via `UnreservedId::to_meth` (no grammar
  change); `any` lowered to `!e.all(!p)`; bare-value `it` lowers to `item()`; stray `it`
  rejected at `parse_expr` and both policy-condition conversions. 15 + 2 off-build tests.
- `23056938` C5: protobuf `All` (field 17) and `Item` (field 18); untrusted decode re-checks the
  predicate and rejects stray `it` in policy bodies. Replaces the proto `unimplemented!` (D-07).

cedar-spec:
- `66d4721` PLAN; `b784ad2` generators residual `All` arm; `1418003` D-25..D-31;
  `cd0fd1a` tasks.md; this commit: OUTCOMES, D-32, PLAN matrix NIT.

## Evidence
- Build (0 errors, `--tests`): core default / `anyall` / `anyall,tolerant-ast` /
  `experimental` / all-features; cedar-policy default / `experimental` / `protobufs` /
  `protobufs,anyall` / all-features; formatter, CLI; cedar-drt with and without `anyall`.
- Clippy (lib, all features): 0 errors in core and cedar-policy.
- Lib tests: core 1564 default / 1625 `anyall` / 1842 all-features; cedar-policy 429 default /
  557 `anyall,protobufs` / 649 all-features. All pass.
- Mutations: dropping the `.any` negation fails 2 tests; disabling the stray-`it` check fails
  1 test.
- Off-build behaviour identical to Phase 3 (`[1].all(..)` gives `UnknownMethod`; `it == 1`
  gives `ArbitraryVariable`) — verified by the reviewer against `c65d955a`.

## Review NITs
- NIT-1: stray-`it` is enforced at each entry point rather than centrally. Logged as D-32.
- NIT-2: PLAN matrix listed `protobufs` as a core feature. Fixed in PLAN.md.

## Carried forward
- D-29: Lean `CedarProto` `All`/`Item` decoder arms in Phase 6.
- D-31: `cedar-drt/fuzz` does not compile (pre-existing `BTreeMap` proto-record mismatch); must
  be resolved before Phase 6 fuzzing.
- D-32: consider a central guard against a surviving `IT_SENTINEL` (relevant for TPE, 6.5).
