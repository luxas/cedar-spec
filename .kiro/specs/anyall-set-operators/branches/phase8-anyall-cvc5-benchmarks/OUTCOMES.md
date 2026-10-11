# Phase 8 Outcomes — cvc5 runtime benchmarks (`phase8-anyall-cvc5-benchmarks`)

**Status:** DONE — review converged (round 1: 2 LOW findings fixed; round 2: 2 provenance findings
fixed; round 3: NO ACTIONABLE FINDINGS). Satisfies req **5.4** (empirical tractability) and T8.x.
Decisions **D-87**, **D-88**, and the D-P8-* lines in `PLAN.md`. The numeric body lives in
`RESULTS.md`; raw data in `data/*.json` (provenance `cedar_spec_sha` = `97515ec`, on this branch).

Scope: cedar-spec only (`cedar-drt/fuzz` harness + spec docs). The nested cedar (Rust) repo is
unchanged by this phase (its tip stays the Phase 7 tip), so there is no cedar-side PR. Branch cut
from `phase6.5-anyall-tpe`, rebased onto `phase7-anyall-docs` before review round 2.

## Commits (bottom-up, on top of `phase7-anyall-docs`)
| Hash | What |
|---|---|
| `a4ca474` | PLAN + hand-measured cvc5 data point (symbolic `context.ports.all(it > 0)` vs `all(it >= 0)`: SAT ≈0.03 s) |
| `d800cad` | D-87: per-query timeout 300 s (DRT `TIMEOUT_DUR`), first `--full` sweep capped at ~90 min wall |
| `affdec0` | P1: harness skeleton + the D-P8-nonvac `set.filter`/`HO_ALL` assertion; `local_solver()` made `pub` |
| `d6f563e` | P2–P7: outcome model (sat/unsat/unknown/timeout/oom/encode_error), 7 dimension families, quantifier-free baseline, CSV/JSON + RunMeta, median/p90 summarizer, `--smoke`/`--full`/`--selftest` |
| `38bde06` | P7 refinement: `--sizes` cliff knob + baseline depth cap (N ≤ 64, parser overflow beyond) |
| `5e8f6da` | P8: RESULTS.md + committed sweep data + D-P8-* decisions |
| `7cab992` | Review R1 F-1: no absolute local paths in PLAN.md |
| `571efb2` | Review R1 F-2: abrupt mem-cap solver kill classified `oom`; deterministic classifier table in `--selftest` |
| `33c256e` | Review R1 N-1: default `--full` set-size axis extended to N = 128 (cliff onset in headline data) |
| `94e7206` | Review R1 N-2: scaling prose gives the real local-exponent curve instead of one power law |
| `ec369d1` | D-88: the `cedar-lean-ffi` prerequisite moved down to Phase 6.5; duplicate rows from the restack dropped |
| `97515ec` | Review R2 F-2: tasks.md counts synced (117 rows, ≈25 s) |
| `2e37376` | Review R2 F-1: data regenerated on this branch + RESULTS.md re-synced by script |

## As built
- `cedar-drt/fuzz/fuzz_targets/anyall_symcc_bench.rs`: `anyall`-gated, `bench = false` bin (refuses to
  build without the feature). Reuses `symcc.rs`'s `local_solver()` (cvc5, 1 GiB `setrlimit`), the
  generator schema helpers, and the **unoptimized** `CedarSymCompiler::check_*` verbs (D-77: SymCCOpt
  excludes `.all` under the D-74 interim), including for the SMT-text capture (`WriterSolver`).
- Non-vacuity gate (D-P8-nonvac): every quantified row's emitted SMT must contain `set.filter` under
  `(set-logic HO_ALL)` or the harness aborts; a literal receiver (D-68 fold) or a quantifier-free
  policy is refused. The UNSAT family uses `all(it>0)` vs `all(it>=1)` (equivalent but distinct), since
  identical policy sets fold `check_equivalent` to a constant (D-P8-eqfold).
- Dimensions: set size (symbolic `Set<Long>` with N membership-pinned candidates), predicate shape,
  element type, quantifier count, verb (6), `.all`/`.any`, sat/unsat. Baseline = the same `.all` unrolled
  over the N members (quantifier-free), sharing the verdict at every N.

## Results (RESULTS.md; medians of 3 repeats)
- **Set size is the only steep axis.** Quantified solve 7 → 1048 → 4462 ms for N = 0 → 64 → 128; the
  `set.filter` encoding delta over the baseline grows 7 → 96 ms through N = 64, a modest fraction of the
  total. Local exponent rises 0.29 (N 1→2) → ~1.85 (32→64) → 2.09 (64→128); the baseline tracks the same
  shape (0.74 → 1.95), so the acceleration is membership/arithmetic reasoning, not the comprehension.
- **Cliff:** N = 128 ≈ 4.6 s; N = 192 and 256 exhaust the 1 GiB cap (`oom`; "killed, no exit status"
  and `std::bad_alloc` respectively). cvc5 fails by memory, never by time: no `timeout`/`unknown`
  anywhere in the committed data.
- **Other six dimensions are flat:** ≤ 15 ms across predicate shape, element type, quantifier count,
  verb, `.all`/`.any`, sat/unsat.
- Full sweep: 117 rows, 0 vacuous, wall ≈ 25 s (D-87's 90-minute budget not exhausted; paper-scale runs
  remain a documented `--sizes` / `--max-wall-secs 0` knob). Smoke: 27 rows, ≈ 1 s.

## Verification
- `--selftest`: timeout handled first-class (1 ms query → `timeout`), 31 quantified families non-vacuous,
  baseline verdict parity, 10-case classifier table (+ `SolverUnknown`); flipping one expected label
  makes it fail (reviewer R2).
- Mutation checks: literal receiver with the gate on → panic "must be non-vacuous"; gate defanged +
  literal receiver → the vacuous row is visible as `has_set_filter=false` (gate is load-bearing).
- Reproduction by three independent reviewers: all set-size medians within 3–8 % (loaded host); cliff
  reproduced exactly; every RESULTS.md number recomputed from the committed JSON by the reviewers' own
  scripts (R2, R3) matches.
- Green bar: `lake build Cedar` green; `cedar-drt` and `cedar-drt/fuzz` build and test with and without
  `--features anyall`; all existing fuzz targets build; the bin is clippy-clean (the 7 `-D warnings`
  errors are pre-existing `cedar-drt-inner` lib lints, R1 N-3). The DRT/fuzz crates carry no `#[test]`
  units (libfuzzer harnesses), so the 0/1-test counts there are expected and are not claimed as coverage.

## D-88 — prerequisite moved down the stack
`cargo build --features anyall` in `cedar-drt` failed on the Phase 6.5 tip: `ResidualKind::All`
(Phase 6.5) had no arm in `cedar-lean-ffi/src/messages.rs` (E0004). Phase 8 fixed it; review R1 (Q6)
confirmed the fix is correct and a genuine prerequisite, so the commit was cherry-picked onto
`phase6.5-anyall-tpe` (`10d8981`), Phases 7 and 8 rebased onto it, and the duplicate dropped here.

## Follow-ups
- Deeper envelope (paper-scale: larger `--sizes`, uncapped wall) if the RFC 0021 performance discussion
  needs it; the harness supports it, Phase 8 did not run it (D-87).
- A `--cap` knob for the solver memory limit would let the cliff be probed above 1 GiB.
- Re-run `--full` after Phase 9 (D-70 B set-typed footprints add `set.filter` grounding; D-78 changes
  the logic line) — the headline numbers are pinned to the Phase 5–7 encoding.

## Review loop
| Round | Verdict | Findings |
|---|---|---|
| 1 | ACTIONABLE FINDINGS: 2 (LOW) | F-1 absolute paths in PLAN.md; F-2 cliff classifier labelled the N=192 mem-cap kill `encode_error`. Nits: envelope depth (taken: N=128 in the default sweep), `N^1.6` label (taken), pre-existing clippy debt. Also confirmed non-vacuity bites on both break vectors, unopt verbs everywhere, numbers reproducible, baseline fair, and Q6b: Phase 6.5 had shipped a red `anyall` DRT build (→ D-88). |
| 2 | ACTIONABLE FINDINGS: 2 | F-1 (MEDIUM) committed data `cedar_spec_sha` were pre-rebase orphans; F-2 (LOW) tasks.md counts stale. Fixes verified real; classifier selftest fails on a flipped label; fresh `--full` within 3 %. |
| 3 | NO ACTIONABLE FINDINGS | Provenance SHAs are ancestors of HEAD with harness source identical; every RESULTS.md number recomputed from JSON; only docs/data changed since `ec369d1`; fresh smoke 27 rows / 0 vacuous. |
