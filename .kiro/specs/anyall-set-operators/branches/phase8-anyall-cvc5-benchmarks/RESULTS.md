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
| cedar-spec SHA | `da231bf` (F-2 commit — the full sweep is regenerated from it) |
| cedar (Rust) SHA | `9fd7bcf5` |
| per-query timeout | 300 s (DRT `TIMEOUT_DUR`, D-87) |
| memory cap | 1 GiB (`setrlimit`, via `local_solver()`) |
| pathway | `unopt` (D-P8-unopt / D-77 — SymCCOpt rejects `.all`) |
| seed | `0x0a110a11` (hand-built policy text is deterministic; seed only labels the run) |
| host | 24 logical CPUs, ~92 GiB RAM |
| main sweep | `--full`, repeats = 3, 117 rows, wall ≈ 25 s, budget not exhausted |

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
| 0 | 8 | 0 | 8 |
| 1 | 9 | 3 | 6 |
| 2 | 11 | 5 | 6 |
| 4 | 16 | 9 | 7 |
| 8 | 31 | 21 | 10 |
| 16 | 82 | 66 | 16 |
| 32 | 285 | 239 | 46 |
| 64 | 1049 | 956 | 93 |
| 128 | 4494 | — | — |

The baseline unroll is capped at N ≤ 64 (its N-way conjunction overflows the
Cedar parser past that, D-P8-size), so N = 128 carries a quantified row only; it
is the cliff onset now folded into the headline sweep (N-1).

Both curves grow super-linearly in N, but **not as a single power law — the
curve accelerates.** The quantified median has no one clean exponent; its *local*
exponent (the slope between consecutive points, `log(t₂/t₁) / log(N₂/N₁)`) rises
monotonically across the range:

| N interval | quantified (ms) | local exponent |
|---|---|---:|
| 1 → 2 | 9 → 11 | 0.29 |
| 2 → 4 | 11 → 16 | 0.54 |
| 4 → 8 | 16 → 31 | 0.95 |
| 8 → 16 | 31 → 82 | 1.40 |
| 16 → 32 | 82 → 285 | 1.80 |
| 32 → 64 | 285 → 1049 | 1.88 |
| 64 → 128 | 1049 → 4494 | 2.10 |

So cvc5's solve time is **sub-linear at small N (~N^0.3 near N=1..2), crosses
~N^1 around N≈4..8, and steepens to ~N^1.9 by N=32..64 and ~N^2.1 by
N=64..128** — a cost that grows faster the larger the set, not the fixed `N^1.6`
a single label would suggest. The baseline tracks the same accelerating shape
(local exponent 0.74 → 2.00 across N=1..64), so the acceleration is the
membership/arithmetic reasoning both shapes pay, not an artifact of the
`set.filter` encoding. The encoding delta `Δ = quantified − baseline` grows with
N (8 → 93 ms through N=64): the two-`set.filter` comprehension costs cvc5
progressively more as the number of reasoned-about members rises, but it stays a
*modest fraction* of the total — most of the cost is the membership/arithmetic
reasoning the baseline also pays.

## 2. The cliff — where cvc5 degrades (`data/cliff-setsize.json`)

Pushing N past the main sweep (`--full --sizes 64,128,192,256`, repeats = 3,
quantified only — the baseline unroll overflows the Cedar parser past N = 64, so
it is capped there):

| N | outcome | solve (ms) | note |
|---:|---|---:|---|
| 64 | sat | 1036 | — |
| 128 | sat | 4458 | — |
| 192 | **oom** | 5920 | cvc5 process killed under the 1 GiB cap, no exit status |
| 256 | **oom** | 6111 | `std::bad_alloc` under the 1 GiB cap |

**The practical cliff is N ≈ 128 → 192.** cvc5 decides N = 128 in ~4.5 s, then at
N ≥ 192 the 1 GiB memory cap is exhausted and both N = 192 and N = 256 classify
`oom`. The two rows are the same mem-cap death surfaced two ways: at N = 192 the
process is killed abruptly with no exit status (`terminated unexpectedly with
status: None` — the `RLIMIT_AS`/OOM-killer signature), and at N = 256 cvc5
reports `std::bad_alloc` before it dies. The F-2 fix makes `classify_err` label
both as `oom`; each row keeps the raw solver text in its `note` for audit. No row
ever returned `unknown` or hit the 300 s time budget: on this encoding, cvc5
fails by **running out of memory, not time**.

## 3. The other six dimensions are flat and cheap

All medians below are the symbolic `.all` query at the baseline set size
(no membership pins), 3 repeats, un-opt verbs:

| dimension | point | median (ms) |
|---|---|---:|
| predicate complexity | `it > 0` → range → `if` → nested `if` | 7 → 8 → 9 → 10 |
| element type | Long / String / Bool / EntityUID | 7 / 4 / 3 / 3 |
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
