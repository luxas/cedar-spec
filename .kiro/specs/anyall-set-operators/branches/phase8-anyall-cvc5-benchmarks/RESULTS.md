# Phase 8 — cvc5 runtime benchmark RESULTS (`phase8-anyall-cvc5-benchmarks`)

Satisfies req **5.4** (empirical tractability) and T8.3. This file holds the
numeric body; the harness design and decisions live in `PLAN.md` and
`DECISIONS.md` (D-52, D-68, D-70, D-77, D-87, D-P8-*).

> **Decidability is not tractability.** Phase 5B proved cvc5 *terminates* on the
> `.all`/`.any` encoding (the D-52 two-`set.filter` `HO_ALL` comprehension). This
> phase measures how it actually **scales**, and documents the practical envelope
> — the RFC 0021 "negative impact on analysis performance" drawback, quantified.

## Reproducibility (from the committed `RunMeta`)

| field | value |
|---|---|
| cvc5 | `1.4.1 [git 2b2e844]` |
| cedar SDK | `4.13.0` |
| cedar-spec SHA | `b684099` (harness commit) |
| cedar (Rust) SHA | `9fd7bcf5` |
| per-query timeout | 300 s (DRT `TIMEOUT_DUR`, D-87) |
| memory cap | 1 GiB (`setrlimit`, via `local_solver()`) |
| pathway | `unopt` (D-P8-unopt / D-77 — SymCCOpt rejects `.all`) |
| seed | `0x0a110a11` (hand-built policy text is deterministic; seed only labels the run) |
| host | 24 logical CPUs, ~92 GiB RAM |
| main sweep | `--full`, repeats = 3, 114 rows, wall ≈ 10 s, budget not exhausted |

Every quantified row's emitted SMT was asserted to contain a `set.filter` term
under `(set-logic HO_ALL)` before timing (D-P8-nonvac): **0 vacuous rows**, so no
number here is a compile-time fold (D-68) or a silently-rejected policy
(D-70/D-77). Raw data: `data/full-sweep.json`, `data/cliff-setsize.json`,
`data/smoke.json`. Regenerate with
`cargo run --features anyall --bin anyall_symcc_bench -- --full` (env per
PLAN.md §4).

## 1. Headline — set size is the only steep axis

Median cvc5 solve time (3 repeats) for the symbolic `.all` query
`context.ports.all(it > 0)` (`check_always_allows`), the `.all` ranging over a
symbolic `Set<Long>` with **N** membership-pinned candidate elements (§0.2 /
D-P8-size). The **baseline** is the same `.all` unrolled over those N members
(quantifier-free), so `Δ = quantified − baseline` is the cost attributable to the
`set.filter` encoding rather than to fixed compile/spawn overhead.

| N | quantified (ms) | baseline (ms) | Δ encoding (ms) |
|---:|---:|---:|---:|
| 0 | 7 | 0 | 7 |
| 1 | 9 | 3 | 6 |
| 2 | 11 | 5 | 6 |
| 4 | 16 | 8 | 8 |
| 8 | 30 | 20 | 10 |
| 16 | 81 | 66 | 15 |
| 32 | 280 | 242 | 38 |
| 64 | 1049 | 981 | 68 |

Both curves grow super-linearly in N (≈ N^1.6 over this range), and the encoding
delta grows with N (7 → 68 ms): the two-`set.filter` comprehension costs cvc5
progressively more as the number of reasoned-about members rises, but it is a
*modest fraction* of the total — most of the cost is the membership/arithmetic
reasoning the baseline also pays.

## 2. The cliff — where cvc5 degrades (`data/cliff-setsize.json`)

Pushing N past the main sweep (`--full --sizes 64,128,192,256`, repeats = 1,
quantified only — the baseline unroll overflows the Cedar parser past N = 64, so
it is capped there):

| N | outcome | solve (ms) | note |
|---:|---|---:|---|
| 64 | sat | 1046 | — |
| 128 | sat | 4545 | — |
| 192 | **encode_error** | 5842 | cvc5 process killed by the 1 GiB cap before `bad_alloc` |
| 256 | **oom** | 6051 | `std::bad_alloc` under the 1 GiB cap |

**The practical cliff is N ≈ 128 → 192.** cvc5 decides N = 128 in ~4.5 s, then at
N ≥ 192 the 1 GiB memory cap is exhausted. (`encode_error` vs `oom` is the R4
heuristic classifier splitting on the solver's termination signature — both are
the same 1 GiB-cap exhaustion; the raw solver text is kept in each row's `note`
for audit.) No row ever returned `unknown` or hit the 300 s time budget: on this
encoding, cvc5 fails by **running out of memory, not time**.

## 3. The other six dimensions are flat and cheap

All medians below are the symbolic `.all` query at the baseline set size
(no membership pins), 3 repeats, un-opt verbs:

| dimension | point | median (ms) |
|---|---|---:|
| predicate complexity | `it > 0` → range → `if` → nested `if` | 7 → 8 → 9 → 10 |
| element type | Long / String / Bool / EntityUID | 7 / 4 / 4 / 3 |
| quantifier count | k = 1 / 2 / 3 / 4 sibling `.all`s | 7 / 8 / 11 / 15 |
| verb | always_allows / always_denies / equivalent / implies / disjoint / never_errors | 7 / 5 / 12 / 7 / 11 / 4 |
| `.all` vs `.any` | — | 7 / 6 (no asymmetry) |
| sat vs unsat shape | sat / unsat (via `check_equivalent`) | 13 / 10 |

Takeaways: predicate AST depth, element theory, quantifier count (sibling, not
nested — nesting is excluded by the feature), the specific check verb, the
`.all`/`.any` choice, and sat-vs-unsat all move solve time only within a few
milliseconds. **Set size is the dimension that matters**; everything else is
noise against it.

## 4. Verdict on the RFC 0021 performance concern

For realistic policies — a `.all`/`.any` over a context/entity set attribute with
a modest number of constrained members — cvc5 solves in **tens of milliseconds**,
and stays sub-second through N = 32. The analyzability "drawback" only bites when
a single query forces reasoning over ~128+ named members of one symbolic set, and
even then cvc5 fails by exhausting a 1 GiB cap rather than hanging — a limit that
rises with the memory budget. The un-optimized pathway is pinned because SymCCOpt
rejects `.all` under the D-77 interim; the optimized path becomes measurable once
D-74 lands (noted, not assumed).

## 5. Deviations recorded this phase (see DECISIONS.md D-P8-*)

- **D-P8-eqfold** — two syntactically-identical compiled policy sets make
  `check_equivalent` reduce to a constant-true assert that SymCC never encodes (a
  vacuous, un-solved query). The sat-vs-unsat UNSAT shape therefore uses a
  genuinely-equivalent-but-distinct pair (`all(it > 0)` vs `all(it >= 1)` over
  `Long`) so cvc5 actually decides a `set.filter` term.
- **D-P8-impl** — harness items P2–P7 share one file and interdepend; they landed
  as one green commit rather than six that would not individually compile.
- Baseline shape capped at N ≤ 64 (its N-way unroll overflows the parser past
  that); the fixed-shape quantified `.all` row carries the cliff probe. Recorded
  in the P7-refinement commit.
