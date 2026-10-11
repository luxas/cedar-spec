# Phase 8 — cvc5 runtime benchmarks — PLAN (`phase8-anyall-cvc5-benchmarks`)

> **Status: PLAN only.** This branch has one hand-measured data point committed (below);
> implementation items P1–P9 are not yet started. Satisfies req **5.4** and documents the
> RFC 0021 performance drawback. Runs LAST — needs the full SymCC `.all` pipeline (Phase 5B)
> and the generator arm (Phase 6), both DONE.
>
> **Branches.** cedar-spec `phase8-anyall-cvc5-benchmarks` cut from `phase6.5-anyall-tpe`
> @ `5e1b3ee`; nested cedar `phase8-anyall-cvc5-benchmarks` cut from `phase6.5-anyall-tpe`
> @ `9fd7bcf5`. Phase 7 (docs) runs in parallel on another branch; **this branch gets rebased
> onto Phase 7's final tip later** (the write-up in §8 may touch the same docs area, so expect
> a small DECISIONS.md / docs rebase, same mechanics as the recurring D-74/D-75/D-76 row merges).

---

## 0. What this phase measures, and why decidability is not enough

Phase 5B proved cvc5 *terminates* on `.all` (the D-52 `set.filter`/`HO_ALL` encoding is in the
decidable fragment, Mohamed et al. FMCAD 2025). RFC 0021 was rejected partly because the
operators "will likely have a negative impact on analysis performance." Termination is not
tractability: this phase measures **how cvc5 actually scales** — solve wall-time, outcome
(sat / unsat / unknown / timeout / oom), and SMT term size — across the req-5.4 dimensions, and
documents the practical envelope (where cvc5 degrades or times out).

### 0.1 The load-bearing measurement constraint — SYMBOLIC receivers only (D-68)

**A literal-set receiver folds at compile time (D-68): the per-element predicate is evaluated
and `.all` collapses to a constant `conj`/`anyErr` fold BEFORE any `set.all`/`set.filter` term
is emitted.** So a benchmark over `[1,2,3].all(it > 0)` measures the Rust folder, not cvc5 — it
emits no `set.all` at all. Every benchmarked policy MUST therefore use a **symbolic receiver**:
a set-typed **`context` or entity attribute** (`context.ports`, `resource.owners`) whose value is
an SMT unknown, so compilation emits the real two-`set.filter` `HO_ALL` term and cvc5 must decide
it. The hand-measured data point (below) uses `context.ports : Set<Long>` for exactly this reason.
**P-nonvac (§9) makes this a hard, asserted invariant of the harness, not a convention.**

### 0.2 "Set size" has no static Cedar cardinality — how the axis is realised

Cedar sets have **no static cardinality bound** (a `Set<Long>` attribute is one SMT set unknown,
not N element unknowns), and the SMT set is unbounded. So "set size" (req 5.4 / T8.2 dim 1) is
**not** a schema knob. It is realised by **constraining the symbolic receiver's membership in the
query** so the solver reasons about exactly N candidate elements:

- **Chosen realisation (membership-constrained symbolic set).** Keep ONE symbolic `Set<τ>`
  attribute, and in the benchmark *shape* add a conjoined guard that pins N distinct symbolic
  elements into (or out of) it — e.g. compare a policy whose guard also asserts
  `context.ports.contains(e_1) && … && context.ports.contains(e_N)` for N fresh symbolic
  `e_i : τ` drawn from other context attributes. The `.all` still ranges over the whole symbolic
  set, but the sat/unsat search is driven over N named members, which is the quantity the paper's
  Fig. 3 x-axis ("elements") actually varies. N ∈ {1,2,4,8,16,32,64,128,…} until cliff.
  - *Why not "a set literal of N symbolic elements collected from N context attributes":* a set
    **literal** `[context.a, context.b, …]` whose elements are symbolic still has a literal set
    SHAPE, and the receiver fold (D-68) folds the `.all` over the literal's known arity into an
    N-way `conj` of per-element predicates — so it measures an N-way boolean conjunction in SMT,
    **not** the `set.filter` comprehension. P1 MUST verify which path a candidate "set size"
    construction takes (assert a `set.filter`/`set.all` term is present — §9) before trusting its
    numbers; **D-P8-size records the chosen realisation and the check that it does not fold.** If
    the membership-constrained form proves to also partially fold, fall back to the paper's own
    construction (a symbolic set plus an explicit cardinality assumption `(= (set.card S) N)` added
    to the asserts via a benchmark-only hook) and record that as D-P8-size option B.
- The other six dimensions (§ below) are varied by the *predicate* and *query*, which do not fold.

---

## 1. Harness location and shape (decision + justification)

**Decision (D-P8-loc): the benchmark is a new `anyall`-gated binary in `cedar-drt/fuzz`
(`cedar-drt-inner`), `cedar-drt/fuzz/src/bin/anyall_symcc_bench.rs`, with `bench = false`,
`test = false`, `doc = false`, `required-features = ["anyall"]`.** It reuses the existing SymCC
plumbing in `cedar-drt/fuzz/src/symcc.rs` (`local_solver()` — the 1 GB `setrlimit` + `CVC5` env
binary + `--lang smt`; the tokio `RUNTIME`; `get_cex`'s timeout pattern) and the generator
(`cedar-policy-generators`, `enable_anyall`). Driving APIs come from `cedar-policy-symcc`:
`Validator` → `WellTypedPolicies::from_policies` → `SymEnv::new` → `CedarSymCompiler::new(LocalSolver)`
→ the **un-optimized** check verbs.

**Why `cedar-drt/fuzz` and NOT the alternatives:**

| Candidate | Verdict | Why |
|---|---|---|
| **`cedar-drt/fuzz` new bin** (chosen) | ✅ | The ONLY place where cvc5 + the Rust SymCC compiler + the generator + the 1 GB-cap `LocalSolver` are already wired together. `local_solver()` (1 GB `setrlimit`, `CVC5` env) and `RUNTIME` already exist in `symcc.rs`; `cedar-policy-symcc`, `libc`, `tokio` full, and the `anyall` feature are already deps. The `symcc-check-*-ok` bins already set the `bench=false`/`test=false`/`doc=false` precedent for non-libfuzzer binaries here. Zero new solver glue. |
| `cedar-drt` bench target (`cedar-drt/benches/…`) | ❌ | `cedar-drt` (the lib, crate `cedar-drt`) does **not** depend on `cedar-policy-symcc`, `libc`, or `tokio` — the whole SymCC + 1 GB-cap solver stack lives one level down in `cedar-drt/fuzz`. A `benches/` target here cannot reach cvc5 without duplicating `local_solver()` and adding three deps. T8.1 lists this option; rejected on reachability. |
| `cedar-benchmarking` | ❌ | Measures the **authorization engine** (authorizer/validator wall-time in µs over a corpus; `BenchmarkOutput`/`TimingInfo`), has **no** `cedar-policy-symcc` / cvc5 dependency at all, and its `--trials/--corpus/--compare/--regression-threshold` model is built for deterministic in-process timing, not for spawning a solver subprocess with timeout/oom outcomes. Wrong harness for SMT solve-time. We DO borrow its output conventions (see §7). |
| `cedar-policy-symcc` example binary | ❌ | Lives in the nested cedar repo, which has the generator only as a dev/optional path and no 1 GB-cap solver wrapper; would re-implement the DRT solver plumbing and split the benchmark from the generator it needs. |

The binary is a normal `main()` using the existing `RUNTIME` (or its own
`tokio::runtime::Builder`) — not a `#[libfuzzer_sys::fuzz_target]`, because it runs a fixed
parameterized sweep, not a byte-stream fuzz loop.

---

## 2. Ordered work items (exact paths + non-vacuous green checks)

Each commit keeps the three surfaces green per the repo rule (Lean `lake build Cedar`; DRT
`cargo test` default + `--features anyall`; Rust core both ways). This phase adds no code to the
default build path — all of it is `#[cfg(feature = "anyall")]` and in a `bench=false` binary — so
"non-`anyall` byte-unchanged" is the dominant green check.

- **P0 — plan + hand data point (THIS commit).** `branches/phase8-…/PLAN.md` (this file) +
  tasks.md Phase 8 → IN-PROGRESS with a PLAN pointer. Hand data point recorded in §10. No code.
  _Green check:_ docs only; `git diff` touches only `.kiro/specs/**`.

- **P1 — harness skeleton + the "cvc5 is really invoked" assertion.**
  `cedar-drt/fuzz/src/bin/anyall_symcc_bench.rs` (new) + `[[bin]]` entry in
  `cedar-drt/fuzz/Cargo.toml` (`bench=false,test=false,doc=false,required-features=["anyall"]`).
  Build the smallest symbolic-`.all` policy (`context.ports.all(it > 0)` over `Set<Long>`), compile
  via `CompiledPolicySet`/`WellTypedPolicies`, and run ONE verb through `LocalSolver`.
  **Non-vacuity assertion (the central guard):** before timing, serialize the compiled asserts to
  SMT-LIB (via the `WriterSolver` path already in `symcc.rs::smtlib_of_check_asserts`) and
  **assert the script contains a `set.filter` / `set.all` term and the `(set-logic HO_ALL)`
  header** — i.e. the receiver did NOT fold (D-68) and the policy was NOT rejected (D-70). A run
  whose SMT has no `set.filter` is a measurement bug and MUST fail the harness, not be recorded.
  _Green check:_ `cargo run --features anyall --bin anyall_symcc_bench -- --smoke` emits ≥1 row
  with `encoding_has_set_filter=true`; `cargo build` (no `anyall`) does not build the bin
  (gated); clippy clean on the `anyall` feature.
  _Satisfies:_ 5.4, and the review's "harness measures what it claims".

- **P2 — outcome model + per-query timeout + 1 GB cap, first-class unknown/timeout/oom.**
  Define `enum SolveOutcome { Sat, Unsat, Unknown, Timeout, Oom, EncodeError }` and a
  `QueryResult { dims: Dims, verb, outcome: SolveOutcome, solve_ms: u128, term_size: usize,
  smt_bytes: usize }`. Timeout = `tokio::time::timeout(per_query_timeout, …)` around the check
  (the `get_cex` pattern), classified `Timeout` not panic. Memory = reuse `local_solver()`'s 1 GB
  `setrlimit`; an allocation-failure solver exit is classified `Oom` (detect via solver stderr /
  non-graceful exit), not a crash. `Unknown` = cvc5 returns `unknown` (`Error::SolverUnknown`).
  `solve_ms` wraps ONLY the `check_*` await (compile time measured separately as `compile_ms`),
  so the solver time is isolated. `term_size` = node count of the compiled `Term` (add a cheap
  recursive size over `cedar_policy_symcc::term::Term`, or count from the SMT string as a
  fallback); `smt_bytes` = length of the serialized script.
  _Green check:_ a deliberately tiny timeout (e.g. 1 ms) on a non-trivial query yields a recorded
  `Timeout` row (unit-style assertion in the bin's `--selftest` mode), proving the outcome is
  first-class, not an error. A unit asserts `Unknown`/`Oom` variants are reachable in the match
  (compile-time exhaustiveness) — no silent `_ => panic`.
  _Satisfies:_ 5.4 (first-class non-sat outcomes), T8.1 (timeout + 1 GB cap).

- **P3 — policy-family generators per dimension (T8.2).** `cedar-drt/fuzz/src/bin/…` module
  `families.rs` (or inline): deterministic constructors (fixed `StdRng` seed, like the Phase-6
  F-1 fix) that emit a symbolic-receiver `.all`/`.any` policy for each dimension point. Prefer
  **hand-built policy text** over the `arbitrary` generator for the swept policies, so each
  dimension point is EXACTLY controlled and reproducible (the generator is non-deterministic in
  shape); reuse `cedar-policy-generators` only if a dimension needs structural variety the text
  builder cannot give. Each family is a `fn(n|depth|…) -> (Schema, PolicySet[, PolicySet2])`.
  The seven dimensions (each varied against a fixed baseline, others held at the baseline point):
  1. **Set size** — N candidate members (§0.2 realisation), N ∈ {1,2,4,8,16,32,64,128,256} until
     the cliff. Baseline predicate `it > 0`, verb `check_always_allows`, element `Long`, 1
     quantifier, `.all`, unsat shape.
  2. **Predicate complexity** — predicate AST depth/op-count: `it > k` → `it > a && it < b` →
     nested `if it > a then it < b else it == c` chains → `it like "p*"` / `it is T` /
     attribute-access on a record `it`. Still set-free, non-nested.
  3. **Element type** — `Long` (LIA), `String`, `Bool`, `EntityUID` (+ a record element with
     attribute access). Element theory = the paper's Condition 2.
  4. **Quantifier count** — 1 vs several **sibling** (non-nested) `.all`/`.any` conjoined
     (`a.all(..) && b.all(..) && …`), k ∈ {1,2,3,4}. Nesting stays excluded (not a dimension).
  5. **Check verb** — all six: `check_always_allows`, `check_always_denies` (1 pset);
     `check_equivalent`, `check_implies`, `check_disjoint` (2 psets); `check_never_errors`
     (1 policy). **Use the UN-OPTIMIZED verbs** (`check_always_allows`, not `_opt`): the SymCCOpt
     path rejects `.all` under the D-77 interim (confirmed by `tests/anyall.rs`'s note). A row for
     an `_opt` verb on `.all` would error, not measure — so the harness pins the un-opt path and
     records `pathway=unopt` in every row.
  6. **`.all` vs `.any`** — same shape, `.any` as its `!all(!p)` lowering (via `Expr::any` /
     policy text), to confirm no surprising asymmetry.
  7. **SAT vs UNSAT shape** — a satisfiable (counterexample-bearing) vs an unsatisfiable query per
     family (e.g. `all(it>0)` vs `all(it>=0)` equivalence: identical ⇒ unsat; differing ⇒ sat),
     mirroring the paper's split.
  _Green check:_ a unit per family asserts (a) the built policy **validates** (`Validator`,
  Strict), (b) it **compiles** (no `unsupportedError`), and (c) P1's `set.filter`-present
  assertion holds for N≥1 — i.e. every generated point is a real symbolic solver query. Count the
  families instantiated (>0) so coverage is non-vacuous.
  _Satisfies:_ 5.4, T8.2 (all seven dimensions).

- **P4 — baseline comparison (isolate the encoding cost).** For each swept policy, ALSO build an
  **equivalent quantifier-free** policy — the `.all` manually unrolled over the N candidate
  members (`context.ports.contains(e_i) => pred(e_i)` conjunction) OR the `.all` dropped — and run
  the same verb. Record both rows tagged `shape=quantified|baseline`. The delta
  (`solve_ms_quantified − solve_ms_baseline`) is the cost attributable to the `set.filter`
  encoding, which is the number the write-up reports (not raw `.all` time, which conflates fixed
  compile/solver-spawn overhead).
  _Green check:_ a unit asserts the baseline policy is semantically the intended unroll for a
  small N (the quantified and baseline queries return the SAME sat/unsat verdict for that N), so
  the baseline is a fair comparand, not an unrelated policy.
  _Satisfies:_ 5.4 (practical envelope attributable to the encoding).

- **P5 — CSV + JSON output.** `--format {csv,json}` (default json), `--out <path>`. One record per
  (family, dimension-point, shape, verb) with all `QueryResult` fields + a `RunMeta` header:
  cvc5 version (shell `cvc5 --version`, recorded verbatim — 1.4.1 here), cedar sdk version
  (`cedar_policy::get_sdk_version()`), host (reuse `cedar-benchmarking`'s `SystemInfo::collect`
  pattern: CPU model/count, RAM), git SHAs of both repos, the fixed RNG seed, per-query timeout,
  the 1 GB cap, and `pathway=unopt`. Serde structs mirror `cedar-benchmarking/src/output.rs`
  conventions (serde `Serialize`, `serde_json::to_writer_pretty`).
  _Green check:_ `--format json --out /tmp/x.json` round-trips through serde (a unit deserializes
  it back); CSV has a stable header asserted by a unit.
  _Satisfies:_ 5.4, T8.1 (CSV/JSON for plotting).

- **P6 — summarizer (median / p90 per dimension).** A tiny `--summarize <results.json>` mode (or a
  sibling bin `anyall_symcc_summary`) that reads the JSON and prints, per dimension and per verb,
  median / p90 `solve_ms` and the sat/unsat/unknown/timeout/oom counts — reusing the percentile
  logic shape from `cedar-benchmarking/src/output.rs::TimingInfo::from_runs` (p50/p95 → here
  p50/p90). OPTIONAL `--plot <dir>` emits a `cactus.py`/`gnuplot` script (NOT run in CI) that
  draws the paper's Fig.-3-style cactus plot (instances solved under a time budget). The plot
  script is a text artifact; generating the PNG is a manual step.
  _Green check:_ `--summarize` on a 2-row fixture prints the correct median/p90 (unit with a known
  fixture).
  _Satisfies:_ 5.4, T8.1 (summarizer + optional plot).

- **P7 — smoke config (<2 min, CI/review) + full sweep config.**
  - `--smoke` (default): the baseline point of each dimension + set sizes {1,2,4,8}, one verb per
    family, generous per-query timeout (e.g. 10 s). Target wall < 2 min on this host (the hand
    point is ~0.03 s/query, so a few hundred smoke queries fit easily). This is the config a
    reviewer / a loose CI gate runs.
  - `--full`: the entire sweep (all N up to the cliff, all verbs, all element types, all predicate
    depths, both shapes), per-query timeout = **the sweep-budget fork, see §risks** (default
    proposal 300 s to match the DRT `TIMEOUT_DUR`).
  _Green check:_ `cargo run --features anyall --bin anyall_symcc_bench -- --smoke` completes under
  2 min and every row has `encoding_has_set_filter=true` (non-vacuity holds across the smoke set);
  recorded in OUTCOMES later with the actual wall time + a count of rows.
  _Satisfies:_ 5.4, T8.1 (off the default `cargo test` path), T8.3 (CI smoke-bench option).

- **P8 — results write-up (T8.3).** `branches/phase8-anyall-cvc5-benchmarks/RESULTS.md`: tables of
  median/p90 solve time per dimension, the sat vs unsat split, the quantified-vs-baseline delta,
  and the **cliff** — the set size / predicate depth / element type at which cvc5 starts returning
  `unknown`/`timeout`, documenting the practical envelope (the RFC 0021 drawback, quantified). The
  cactus plot (if generated) is referenced here. Keep the numeric body in RESULTS.md; the plan
  stays in this file.
  _Green check:_ RESULTS.md exists with ≥1 real table from a `--full` (or a bounded `--full`) run;
  the cvc5 version + host + seed from `RunMeta` are quoted so the numbers are reproducible.
  _Satisfies:_ 5.4, T8.3 (documents the envelope).

- **P9 — docs rebase + OUTCOMES.** After Phase 7 lands, rebase this branch onto its tip (expect the
  usual DECISIONS.md row conflict; resolve by keeping HEAD + appending this branch's new D-P8-*
  rows). Write `branches/phase8-…/OUTCOMES.md` (branch heads, per-item commit map, the smoke wall
  time + row count, the full-sweep headline numbers + the cliff, open questions). Update the
  status table (Phase 8 → DONE) and D-01 (the stack's end is reached).
  _Green check:_ three surfaces green post-rebase; non-`anyall` build byte-unchanged.

---

## 3. Gating (never in default `cargo test`)

- The bin is `required-features = ["anyall"]` + `bench=false,test=false,doc=false`, so a plain
  `cargo test`/`cargo build` in `cedar-drt/fuzz` never compiles or runs it (mirrors the
  `symcc-check-*-ok` bins).
- All new code is `#[cfg(feature = "anyall")]`; the non-`anyall` build is byte-unchanged (req 3.1)
  — asserted by the standard feature-matrix check used in prior phases.
- The optional CI smoke-bench (P7) is a separate, explicitly-invoked job (`--smoke`), never wired
  into the default test target; a reviewer runs it by hand or a nightly invokes it.

---

## 4. Driving APIs (confirmed from the tree)

- **Env (D-13 host quirk) for building/running in the OUTER worktree's DRT:**
  `export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"`;
  `unset LD_PRELOAD`; `export CVC5=/home/linuxbrew/.linuxbrew/bin/cvc5`;
  for the nested Rust: `CARGO_TARGET_DIR=/local/home/luxask/code/wt/p8/cedar/target-p8`;
  for cedar-drt builds in the outer worktree: a separate target dir
  `/local/home/luxask/code/wt/p8/target-p8` (both added to each worktree's `.git/info/exclude`).
- **Compile + solve (un-optimized, the `.all`-supported path):**
  `Validator::new(schema)` → `WellTypedPolicies::from_policies(&pset, &req_env, schema)` (1-pset
  verbs) or `WellTypedPolicy::from_policy` (single policy) → `SymEnv::new(schema, &req_env)` →
  `CedarSymCompiler::new(local_solver())` → `compiler.check_always_allows(&typed, &symenv).await`
  / `check_equivalent` / `check_implies` / `check_disjoint` / `check_always_denies` /
  `check_never_errors`. (`CompiledPolicySet::compile` is the `_opt`-path input and MUST NOT be
  used for `.all`.)
- **SMT-LIB capture for the non-vacuity assert:** `symcc.rs::smtlib_of_check_asserts` already
  renders a `WellFormedAsserts` to a String via `WriterSolver`; grep it for `set.filter`/`HO_ALL`.
- **1 GB cap + timeout:** `symcc.rs::local_solver()` (1 GB `setrlimit`, `CVC5` env, `--lang smt`);
  `tokio::time::timeout` as in `get_cex`.

---

## 5. Reproducibility

Fixed `StdRng` seed per family (recorded in `RunMeta`), cvc5 version captured verbatim
(`cvc5 --version` → "cvc5 1.4.1 [git 2b2e844 …]"), cedar SDK version, both git SHAs, host info,
per-query timeout and the 1 GB cap all in the JSON header. Hand-built policy text (P3) over the
non-deterministic `arbitrary` generator for the swept points, so a rerun reproduces the exact
same queries.

---

## 6. What the blind review must verify

1. **cvc5 is really invoked and really decides** — the P1 `set.filter`+`HO_ALL`-present assertion
   holds for every recorded quantified row; no row was short-circuited by the D-68 literal fold or
   silently dropped by a D-70 `unsupportedError`. (Reviewer: pick a row, re-emit its SMT, confirm a
   `set.filter` term, run cvc5 on it by hand, match the recorded outcome.)
2. **Outcomes counted non-vacuously** — `unknown`/`timeout`/`oom` are first-class and reachable
   (the tiny-timeout selftest row), not folded into "error" or dropped; the recorded sat/unsat
   counts match re-running a sample.
3. **The baseline is a fair comparand** — the quantifier-free baseline returns the same verdict as
   the quantified policy for the sampled N (P4 unit), so the delta is the encoding cost, not an
   artifact of comparing unrelated policies.
4. **Un-opt pathway is pinned** — no `.all` row uses an `_opt` verb (would hit the D-77 interim
   rejection); every row records `pathway=unopt`.
5. **Gating** — non-`anyall` build byte-unchanged; the bin does not build or run under default
   `cargo test`.
6. **Set-size axis is honest** (§0.2 / D-P8-size) — the "set size" construction emits a real
   `set.filter` comprehension and is not partially folded into an N-way boolean conjunction; the
   recorded N is the quantity actually varied.

Fold the §4 env preamble (PATH, `unset LD_PRELOAD`, `CVC5`, `CARGO_TARGET_DIR`, the D-13
`LIBRARY_PATH` if the reviewer also builds the Lean FFI) directly into the reviewer's brief so
they do not re-derive it.

---

## 7. Output conventions borrowed from `cedar-benchmarking`

serde `Serialize`/`Deserialize` records; `serde_json::to_writer_pretty`; a `SystemInfo`-style host
block; percentile logic shaped like `TimingInfo::from_runs` (sorted vec, index-based p50/p90). We
do NOT reuse its `--trials/--corpus/--compare/--regression-threshold` CLI or its in-process µs
timer — those are for the authorization engine, not a solver subprocess. (A loose
regression-threshold gate on the smoke summary is a possible later add, but not required by T8.3.)

---

## 8. Risks

- **R1 — the "set size" axis folds (D-68).** The single biggest measurement trap: if the chosen
  construction lets any part fold at compile time, the primary scaling curve is wrong. Mitigated by
  the P1/P3 `set.filter`-present assertion as a HARD failure, and by D-P8-size recording the
  construction + its non-fold check. **This is the risk the blind review must hammer (§6.6).**
- **R2 — SymCCOpt rejects `.all` (D-77 interim).** Only the un-optimized verbs work; the harness
  must never call `_opt` on `.all`. Pinned in P3 (dim 5) + §6.4. If D-74 lands before this phase
  finishes and lifts the interim, the opt path becomes measurable too — a bonus dimension, noted
  but not assumed.
- **R3 — full sweep wall-clock.** The cliff could be deep (hand point is 0.03 s at the smallest
  size); a `--full` run with large N and 300 s timeouts could take hours. Mitigated by `--smoke`
  for CI/review and a bounded `--full` (cap total queries / stop a family after the first two
  consecutive timeouts). The absolute budget is the user fork below.
- **R4 — `oom` detection is heuristic.** The 1 GB `setrlimit` causes cvc5 to fail allocation; mapping
  its exit/stderr to `Oom` vs a generic solver error is best-effort. Mitigated by recording the raw
  solver exit alongside the classified outcome so a misclassification is auditable.
- **R5 — host variance.** Single-host wall-time is noisy; mitigated by median/p90 over repeats per
  point (a `--repeats k` knob, default 3 in `--full`) and by reporting the delta vs baseline rather
  than absolute ms.
- **R6 — Phase 7 rebase.** Expected, low-risk; same DECISIONS.md row-merge mechanics as prior
  phases (keep HEAD, append this branch's D-P8-* rows).

---

## 9. Decisions this plan introduces (to be logged in DECISIONS.md as D-P8-* on implementation)

- **D-P8-loc** — harness is a `bench=false` `anyall`-gated bin in `cedar-drt/fuzz` (§1).
- **D-P8-size** — "set size" realised as a membership-constrained symbolic set (§0.2), with a
  non-fold assertion; option B (explicit `set.card` assumption) recorded as fallback.
- **D-P8-unopt** — benchmark pins the un-optimized check verbs for `.all` (D-77 interim); no `_opt`.
- **D-P8-nonvac** — every quantified row MUST assert a `set.filter`/`HO_ALL` term is present, or the
  harness fails; a folded or rejected policy is never silently recorded.

## User-decision fork — RESOLVED as D-87

- **FORK-1 (sweep budget / wall-clock cap for the FULL run) — RESOLVED (user 2026-10-09, D-87):**
  option **(b)** with a wall-clock cap. Per-query timeout = the repo's DRT `TIMEOUT_DUR` =
  **300 s**; the first `--full` sweep is bounded to **~90 min total** via `--max-wall-secs` (default
  5400 for `--full`), with sweep sizes chosen so the worst case fits, and the harness stops cleanly
  on budget exhaustion recording exactly which rows it covered (a partial sweep is a first-class
  result). Paper-scale runs stay a config knob (`--max-wall-secs 0` = uncapped, larger `--sizes`),
  not run this phase.

Everything else (harness location, set-size realisation, un-opt pinning, output format, smoke
shape) is decided above as D-P8-* and does not need the owner.

---

## 10. Hand-measured data point (proves the pipeline end-to-end — P0)

Measured on this host (`cvc5 1.4.1 [git 2b2e844]`, env per §4), two independent ways on a
**symbolic** `.all` receiver (`context.ports : Set<Long>`, so no D-68 fold):

1. **Production Rust solve path** — `cedar-policy-symcc` `tests/anyall.rs`
   `symbolic_all_different_guard_is_not_equivalent`: compile
   `permit(...) when { context.ports.all(it > 0) }` vs `… all(it >= 0) }`, then
   `CedarSymCompiler::check_equivalent` (un-optimized) over `LocalSolver`/cvc5 → **SAT (not
   equivalent)**, counterexample a set containing `0`. **Wall ≈ 0.032 s** (compile + cvc5 spawn +
   solve + teardown; the harness reports `finished in 0.03s`). Companion identical-guard case →
   **UNSAT (equivalent)**, ≈ 0.017 s; entity-set case (`resource.owners.all(it == principal)`) →
   SAT, ≈ 0.023 s.
2. **Raw cvc5 on the D-52 encoding** — `(set-logic HO_ALL)`, receiver as a symbolic `(Set Int)`,
   `.all` as `(= (set.filter (lambda ((it Int)) (> it 0)) S) S)`, asserted together with
   `(set.member 0 S)` → **unsat** (correctly: `all(it>0)` contradicts `0 ∈ S`), **cvc5 wall ≈
   0.029 s**. This confirms cvc5 genuinely decides the `set.filter`/`HO_ALL` comprehension — the
   term the harness must emit — rather than the pipeline folding it away.

Both confirm: a symbolic `.all` compiles to the two-`set.filter` `HO_ALL` term, cvc5 is invoked,
and it decides sat/unsat in tens of milliseconds at the smallest size. The sweep (P1–P8) scales N
and the other six dimensions from this proven baseline to find the cliff.
