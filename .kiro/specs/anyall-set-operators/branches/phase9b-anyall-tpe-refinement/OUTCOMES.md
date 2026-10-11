# Phase 9b Outcomes — req 7.3: TPE per-element `.all` refinement (`phase9b-anyall-tpe-refinement`)

**Status:** DONE — review converged (round 1: NO ACTIONABLE FINDINGS). Sub-branch 2 of 4 of Phase 9
(`branches/phase9-anyall-completion/PLAN.md` §3 + §3.1). Completes D-80 (full) under D-92 / FORK-3
(`AllPartial` shape). Rust-only; the Lean TPE `.all` arm stays conservative (D-81).

## Commits
| Repo | Hash | What |
|---|---|---|
| cedar | `88763028` | M1: `ResidualKind::AllPartial { decided_false, pending }`; the concrete-receiver `.all` fold drops decided-`true` elements, pins a decided `false`, errors immediately on a concrete element error / non-bool (no short-circuit, req 2.5/2.8), keeps residual elements in `pending`, emits `Concrete(!decided_false)` when nothing is pending; idempotent `AllPartial` re-interpret arm (D-P9b-2); `From<Residual> for Expr` re-expands as `[<pending bools>, !decided_false].all(it)` (D-P9b-1); `can_error_assuming_well_formed(AllPartial) = true`. |
| cedar | `bf5c09b3` | M2: parity tests (refined residual re-authorized against completed input == full evaluation, incl. error-after-pinned-false and `.any` via its lowering), non-vacuity, three deterministic mutation checks. |
| cedar-spec | `25e0756` | PLAN §3.1 D-P9b-1..3; tasks.md T9b. |

## Verification
- Feature matrix, whole lib: `tpe,anyall` 1743; default 1564; `anyall` 1625; `tpe` 1660; all-features 1864;
  0 failures. `tpe::` under `tpe,anyall` 109 → 115 (+6); non-anyall `tpe::` 93 → 93 byte-unchanged
  (req 3.1). `cargo clippy --all-features --lib` clean (D-P9b-3).
- Reviewer's independent harness (not committed): 8/8 shapes over a completion grid including the decisive
  req 2.8 case (a pending element erroring at re-authorization with `decided_false` already pinned ⇒ both
  sides error, never `false`).
- Stray-`it` capture is impossible: `instantiate_with` substitutes every `Item` before interpretation and
  `PredExpr` is set-free and non-nested, so pending residuals have no free `it` to rebind inside the new
  `.all(it)`. Set-literal dedup is harmless for a conjunction, and an erroring duplicate still errors because
  the set literal is evaluated before dedup. Zero-pending + `decided_false` collapses before the `From` arm.
- Mutations (drop the pinned false; short-circuit on first false; drop error-outranks) each turn
  deterministic tests red; reverted byte-exact.

## Follow-ups (reviewer nits, non-blocking)
- Add a one-line comment that the non-bool element arm is validator-unreachable (defensive, D-16).
- Mutation tests B/C pin behaviour via surrogate literals; mutating the fold directly (as A does) would make
  their non-vacuity self-evident.

## Review loop
| Round | Verdict | Notes |
|---|---|---|
| 1 | NO ACTIONABLE FINDINGS | Parity 8/8 incl. req 2.8; re-expansion and stray-`it` argued from code; `can_error` guard and `&& false` interplay; idempotent arm; counts reproduced; Lean untouched; docs truthful; trailers present. |
