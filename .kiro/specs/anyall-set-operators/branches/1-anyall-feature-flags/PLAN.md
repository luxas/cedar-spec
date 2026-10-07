# Phase 0 — `1-anyall-feature-flags`

**Branch:** `1-anyall-feature-flags` (both repos), off `0-anyall-plan` (cedar-spec) / `main` (cedar).
**Spec tasks:** T0.1, T0.2. **Satisfies:** req 3.1, 3.2.
**Goal:** Introduce the `anyall` feature gate across both repos, **completely inert** — no new
code paths, no new AST/Lean constructors. The default build must be byte-for-byte unchanged;
`--features anyall` must also build and simply enable nothing yet.

## Why first
Everything downstream is `#[cfg(feature = "anyall")]`-gated. Landing the flag inert first means
every later phase is additive under a flag that already exists, and the default build never
changes (req 3.1/3.2). This is the safest possible first commit.

## Files to touch

### `cedar/` repo (Rust)
- `cedar-policy-core/Cargo.toml` — add `anyall = []` to `[features]` (experimental group).
- `cedar-policy/Cargo.toml` — add `anyall = ["cedar-policy-core/anyall"]` (passthrough), add to
  `experimental`.

### `cedar-spec/` repo
- `cedar-drt/Cargo.toml` — add `anyall = ["cedar-policy-core/anyall", "cedar-policy/anyall"]`.
- `cedar-drt/fuzz/Cargo.toml` — add `anyall = ["cedar-drt/anyall", ...]` passthrough.
- `cedar-policy-generators/Cargo.toml` — add `anyall = ["cedar-policy-core/anyall"]`.
- `cedar-lean/Cedar/Spec/Features.lean` — NEW: `def anyAll : Bool := false` inert marker +
  doc-comment explaining the real gating is the absence of the `all` constructor until Phase 2,
  and that the Rust `anyall` flag controls whether DRT ever sends an `All` node to Lean. (Lean
  has no `#[cfg]`; a bool marker is the honest representation of "flag exists, inert".)
- `cedar-lean/Cedar/Spec.lean` (or the umbrella import) — import `Features` so it is built.

## Logical commits (multiple per branch encouraged)
1. cedar repo: core + cedar-policy `anyall` feature (inert).
2. cedar-spec repo: drt + fuzz + generators `anyall` passthrough feature.
3. cedar-spec repo: Lean `Features.lean` inert marker + import.

## Green checks (all must pass before review loop)
- cedar: `cargo check -p cedar-policy-core` and `-p cedar-policy`, with and without
  `--features anyall`.
- cedar-spec: `cargo check` in `cedar-drt/` and `cedar-policy-generators/`, with and without
  `--features anyall`.
- Lean: `LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar lake build Cedar` unchanged-green.

## Risks
- A passthrough feature referencing a non-existent sub-feature fails resolution — mitigated by
  adding the core feature first (commit 1) before referencing it (commits 2–3).
- Lean import of a new file can perturb the build graph — verified by a full `lake build`.

## Review loop
After green: spawn a fresh review agent (correctness/cohesiveness/consistency), fix actionable
findings, re-green, repeat with a NEW agent until no actionable findings. Then write OUTCOMES.md.
