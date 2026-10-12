# Phase 9a Outcomes — D-78: gate `HO_ALL` on a `set.all` term (`phase9a-anyall-ho-all-logic`)

**Status:** DONE — review converged (round 1: NO ACTIONABLE FINDINGS). Sub-branch 1 of 4 of Phase 9
(`branches/phase9-anyall-completion/PLAN.md` §2). Closes the Phase 5B follow-up D-78.

## Commits
| Repo | Hash | What |
|---|---|---|
| cedar-spec | `7365b05` | Lean: `Term.containsSetAll` (structural, mirrors `Term.mentionsAnyAllIt`; the Boolean complement of `Term.NoSetAll`); `encode` selects `HO_ALL` iff some asserted term contains `set.all`, else the pre-Phase-5B `ALL` (introduced in `82b32d4`). Build-time checks in `SymTest/AnyAll.lean` (`#guard`s + an `#eval` asserting the emitted `(set-logic …)` line). PLAN §2 D-P9a-1..4, tasks.md T9a. |
| cedar | `400292dc` | Rust `cedar-policy-symcc`: `Term::contains_set_all` (the `Op::SetAll` arm `anyall`-gated), `logic_for` at both `set_logic` call sites; unit test `d78_logic_selection_ho_all_only_for_set_all`. |

## Verification
- `lake build Cedar SymCC SymTest CedarSymTests` green; `CedarSymTests` 1216/1216 (count unchanged — the
  new Lean checks run at build time and fail the build when wrong).
- Rust `cargo test -p cedar-policy-symcc --features anyall --lib` 145/145 (incl. the D-78 test); cvc5-backed
  `--test anyall` 3/3; `cargo check` default / `anyall` / all-features clean.
- Byte-match (D-36): both engines emit the identical `(set-logic HO_ALL)` / `(set-logic ALL)` line per query;
  `symcc-smt-script-drt` 60k runs + `symcc-cex-drt` 42k runs (implementer) and 16.7k runs (reviewer),
  0 mismatches — after rebuilding the Lean FFI static library (D-P9a-4: a stale FFI lib shows up as a false
  Rust-vs-Lean logic mismatch).
- Soundness of the gate: the only higher-order construct either encoder emits is the `set.filter` lambda at
  the single `set.all` encode arm; the Enforcer footprint grounding emits none. So no `set.all`-free query
  needs HO.
- Mutations: forcing `needsHO`/`logic_for` to either constant breaks a deterministic check in both engines
  (reviewer re-applied and reverted).

## Follow-ups
- Phase 9d (D-70 B) will add `set.filter` groundings for set-typed footprint entries; the gate must then
  include those terms (or 9d emits them only alongside a `set.all`). Re-check D-78 at 9d.

## Review loop
| Round | Verdict | Notes |
|---|---|---|
| 1 | NO ACTIONABLE FINDINGS | Walk completeness (7/7 constructors in both engines), historical `ALL` literal confirmed in both repos, byte-match verified directly and by differential, HO reachable only via `set.all`, mutations re-applied, counts reproduced, docs truthful, trailers present. |
