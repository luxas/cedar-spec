# Phase 0 — `1-anyall-feature-flags` — OUTCOMES

**Status:** ✅ COMPLETE, green on both repos, review loop converged (2 rounds).

## What landed
Inert `anyall` Cargo feature (off by default) across all five Rust crates + an inert Lean
marker. Zero behavioral code paths. Default build unchanged; `--features anyall` builds and
enables nothing yet.

### cedar repo (`/local/home/luxask/code/cedar-spec/cedar`, branch `1-anyall-feature-flags`)
- `e40e6d8d` — `anyall = []` on cedar-policy-core; `anyall = ["cedar-policy-core/anyall"]` on cedar-policy.
- `e181a796` — (review fix) added `anyall` to the `experimental` meta-feature in both crates.

### cedar-spec repo (branch `1-anyall-feature-flags`, off `0-anyall-plan`)
- `f427ffc` — `anyall` passthrough on cedar-drt, cedar-drt/fuzz, cedar-policy-generators.
- `9964ab0` — inert Lean marker `Cedar.Spec.anyAll : Bool := false` (`Cedar/Spec/Features.lean`), imported by `Cedar/Spec.lean`.
- `9e35bad` — this branch's PLAN.md.
- `a814b11` — (review fix) forward `cedar-policy-generators/anyall` from `cedar-drt`.

## Green checks (non-vacuous)
- `cedar-policy-core`: **1571** tests pass, identical with and without `--features anyall`.
- `cedar-policy`: **471** tests pass, identical with and without `--features anyall`.
- Identical counts both ways = direct evidence of behavioral inertness (req 3.1).
- Lean `lake build Cedar`: green (586 jobs); `Features.olean` built and imported (req 3.2).
- `cedar-drt` `cargo check` green no-flag and `--features anyall` (build with `LD_PRELOAD` unset).
- Feature propagation proven at compile level (`compile_error!` probe) for all three edges:
  `cedar-drt --features anyall` → core/anyall, policy/anyall, generators/anyall.

## Review loop
- **Round 1** (agent `d91b5cbb`, blind): 0 BLOCKER, 2 SHOULD-FIX —
  (1) `cedar-drt` passthrough missing the generators edge (would silently disable the Phase-6
  generator arm); (2) `anyall` omitted from the `experimental` meta-feature (convention break).
  Both fixed (`e181a796`, `a814b11`) and re-verified.
- **Round 2** (agent `673336d3`, fresh/blind, on the fixed state): **NO ACTIONABLE FINDINGS.**
  Re-verified inertness, all three propagation edges (independent probes), non-vacuous test
  counts, Lean build, and that the round-1 fixes introduced no default-on leak or cycle.
- Loop converged: a freshly-spawned agent found nothing actionable → Phase 0 closed.

## Deviations from PLAN.md
- Added `anyall` to the `experimental` meta-feature (not in the original plan) — review-driven
  consistency fix; still off by default since `experimental ∉ default`.
- Added the `cedar-policy-generators/anyall` edge to `cedar-drt` (plan only listed core+policy)
  — review-driven, prevents a silently-off generator arm in Phase 6.

## Environment facts established (apply to all later phases)
- Toolchain: cargo `~/.cargo/bin`, lean/lake `~/.elan/bin`, cvc5 `/home/linuxbrew/.linuxbrew/bin/cvc5`, protoc `/home/linuxbrew/.linuxbrew/bin/protoc`.
- Lean build on this glibc-2.26 host REQUIRES `LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar`.
- DRT: `source cedar-drt/set_env_vars.sh`, but BUILD with `LD_PRELOAD` UNSET (it breaks linuxbrew
  protoc); the preload is only for RUNNING Lean-linked binaries.
- `cedar-drt` bare `cargo test` runs 0 unit tests (its real tests are fuzz + corpus integration);
  meaningful Rust coverage is in cedar-policy-core (1571) and cedar-policy (471). Each later phase
  must add its own `#[test]`s / Lean theorems and show them RUN (count > 0).

## Residual risks carried forward
- None blocking. Phase 1 (`2-anyall-rust-ast`) adds `ExprKind::All` + `PredExpr`, all `#[cfg(feature="anyall")]`.
