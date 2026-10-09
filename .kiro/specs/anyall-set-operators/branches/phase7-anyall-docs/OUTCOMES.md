# Phase 7 Outcomes — Docs & open questions (`phase7-anyall-docs`)

**Status:** IMPLEMENTED, review pending. Docs-only phase (no behavior change, no new `pub`
API). Satisfies T7.1 (feature docs + Mohamed et al. FMCAD 2025 citation) and T7.2 (OQ-1
sets-of-sets out of scope). Decisions **D-84 / D-85 / D-86**.

Scope: nested cedar repo (rustdoc + CHANGELOGs + `cedar-drt` README) and cedar-spec repo
(spec docs). Branch `phase7-anyall-docs` cut from `phase6.5-anyall-tpe` (cedar-spec `23edc0d`,
cedar `4b365ea4`); rebase onto Phases 6/6.5 final tips before merge.

## Commits

### cedar (nested repo, branch `phase7-anyall-docs`)
| SHA | What |
|---|---|
| `a9f8b9bc` | T7.1 rustdoc: `anyall` in `cedar-policy-core` + `cedar-policy` `lib.rs` experimental-features; enriched `Expr::all`/`Expr::any` rustdoc; runnable gated doctest on `ValidationError::SetTermInQuantifier` |
| `6a065e2b` | T7.1 CHANGELOGs: `### Added` entries under `## [Unreleased]` in `cedar-policy` and `cedar-policy-symcc` |

### cedar-spec (branch `phase7-anyall-docs`)
| SHA | What |
|---|---|
| `7ca545f` | (prior turn) PLAN.md + tasks.md IN-PROGRESS |
| _(this batch)_ | `cedar-drt` README `anyall` section; `docs/language-reference-anyall.md`; `docs/CEDAR-DOCS-HANDOFF.md`; design.md Phase-7 section + OQ-1 cross-link; DECISIONS D-84/85/86; PLAN Q-resolution; tasks.md → IMPLEMENTED |

## As built (A1–E1)

- **A1/A2 (rustdoc feature list):** `anyall` bullet added to the `## Experimental features` block
  of `cedar-policy-core/src/lib.rs` and `cedar-policy/src/lib.rs` — syntax, keyword `it`,
  set-free/non-nested restriction, FMCAD-2025 analyzability, off-by-default + `experimental`.
  Uses no intra-doc `[...]` links (so adds zero rustdoc link diagnostics).
- **A3 (constructor rustdoc + doctest):** `Expr::all`/`Expr::any` docs now state empty-set
  results, deterministic `QuantifierError`, no-short-circuit, and the `.any → !all(!p)`
  lowering. A runnable doctest (D-85) parses `resource.ports.all(it > 0)` via
  `cedar_policy::Policy::from_str`, attached to the `#[cfg(feature="anyall")]`
  `SetTermInQuantifier` variant so it is feature-gated.
- **A4 (`ast::pred` module doc):** verified already complete and accurate (set-free fragment,
  Condition 1, structural + smart-constructor enforcement) — no edit needed.
- **A5 (`SetTermInQuantifier` public doc):** extended (now carries the doctest + restriction
  note); the rendered text matches the `#[error(...)]` string.
- **B1/B2 (CHANGELOGs):** `### Added` entries under the existing `## [Unreleased]` in
  `cedar-policy` and `cedar-policy-symcc`, Keep-a-Changelog format. **B3:** `cedar-policy-core`
  intentionally gets none (no CHANGELOG.md; its changes ride `cedar-policy`'s).
- **C1 (Lean doc comments):** verified already thorough and accurate — `PredExpr`, `Expr.all`,
  `Error.quantifierError`, `evalAll` (incl. the no-short-circuit rule), and the SymCC `.all`
  arm (D-70/D-71/D-65 inline) all documented; the D-74-interim caveat is already written at the
  `TypedExpr.SymCCSupported` definition. **No Lean source edit was made**, so no `lake build`
  risk was introduced (see "Verification" for why the full build was not re-run).
- **C2 (`cedar-drt` README):** new "Experimental: the `anyall` feature" section — the feature
  gate + `ABACSettings::enable_anyall`, the generated `.any` lowered shape and low-weight
  SymCC-unsupported shape, and the `LD_PRELOAD`-unset build note.
- **D1/D2 (design.md Phase-7 section, D-86):** feature summary with the verbatim error strings
  (parser/validator/evaluator), the supported-vs-unsupported SymCC verdicts, the D-74-interim
  completeness caveat, and the Phase 8/9 deferred-items table.
- **D-84 (paste-ready user docs):** `docs/language-reference-anyall.md` (full policy-author
  reference) + `docs/CEDAR-DOCS-HANDOFF.md` (target `cedar-docs` website pages).
- **E1 (T7.2 / OQ-1):** `requirements.md` already records OQ-1 as out-of-scope-by-design;
  design.md Analyzability now cross-links it (Condition 1 + §III-D undecidability).

## Verification

- **V1 rustdoc (`cargo doc --no-deps --features anyall -p cedar-policy -p cedar-policy-core
  -p cedar-policy-symcc`, `CARGO_TARGET_DIR=target-p7`):** my edits add **zero new** rustdoc
  diagnostics (diagnostic set identical base-vs-edited: 11 = 11, all in untouched files /
  pre-existing feature-gated intra-doc links). Plain `cargo doc` builds OK.
  **Caveat:** `RUSTDOCFLAGS="-D warnings"` does NOT pass on this tree — but it fails on
  PRE-EXISTING repo-wide doc-lint debt (`ast/policy.rs`, `partial_response.rs`, `est/expr.rs`,
  and the `tpe` feature-gated intra-doc links in `lib.rs`), demonstrated by stashing my edits
  and reproducing the identical 11-error failure on clean HEAD. Phase 7 introduces none of them.
- **V4 doctests (`cargo test --doc --features anyall -p cedar-policy`):** **34 → 35** doctests,
  all pass; the new one is
  `api::err::ValidationError::SetTermInQuantifier (line 496) ... ok`. Non-vacuous: the +1 delta
  is exactly the feature-gated doctest (absent at 34 without `anyall`).
- **V5 Lean (`lake build Cedar`):** NOT re-run — zero Lean source changes were made (C1 was a
  verification; the doc comments already existed), so there is nothing for a doc edit to break.
  (The tree's current green/red state at `Thm/SymCC/Opt.lean` is governed by the parallel
  Phase-5/6 finalization under the D-74-interim, not by this docs work.)
- **V6 error-string audit:** every error string in the language reference and the design.md
  table was copied verbatim from `parser/err.rs`, `validator/diagnostics/validation_errors.rs`,
  and `evaluator/err.rs` (quoted in this phase's investigation).
- **V7 CHANGELOG format:** entries sit under the existing top `## [Unreleased]`, use
  `### Added`, additive-only diff — matches the surrounding Keep-a-Changelog entries.
- **V8 markdown links:** no link checker installed in-sandbox → manual audit. The two external
  URLs in HANDOFF (docs.cedarpolicy.com, github.com/cedar-policy/cedar-docs) are well-formed;
  the language-reference page uses inline-code paths (no markdown links); every spec file
  referenced by inline-code path in the new design.md section exists.

## What a blind reviewer must verify

1. Every error string in `language-reference-anyall.md` and the design.md Phase-7 table is
   verbatim from the cited source (`grep -F`).
2. The doctest runs (count>0) and is non-vacuous (34→35 with the feature; absent without).
3. Supported/unsupported claims match code: SymCC rejects `it`-dependent `in` with
   `unsupportedError`; the D-74-interim completeness caveat matches
   `TypedExpr.SymCCSupported (.all _ _ _) := false`; `QuantifierError` is core-internal (not a
   public `cedar_policy` evaluation-error variant).
4. No invented user-language-docs tree in these repos beyond the explicit `docs/` drafts; the
   website hand-off note is present.
5. Default build unaffected: all rustdoc edits are on `#[cfg(feature="anyall")]` items or
   feature-scoped prose; plain `cargo doc` is clean of new diagnostics.

## Follow-ups
- When `anyall` graduates, port `docs/language-reference-anyall.md` to the `cedar-docs` website
  per `docs/CEDAR-DOCS-HANDOFF.md`.
- Re-run V1/V4/V8 after the Phase 6/6.5 rebase (doc claims are pinned to code that may move).
- If the repo later gates CI on `-D warnings` rustdoc, the pre-existing doc-lint debt (unrelated
  to anyall) must be cleaned separately.

## Review loop
| Round | Agent | Verdict |
|---|---|---|
| 1 | — | pending |
