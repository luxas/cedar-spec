# Phase 6 outcomes — DRT generator + differential wiring (`phase6-anyall-drt-differential`)

## Result
IMPLEMENTED; review round 2 pending. Blind review round 1 raised 5 findings (F-1..F-5);
all fixed (see below). Branches cut from Phase 5B (`phase5-anyall-symcc` @ `bf97fa2`, green).

## Branch heads
- cedar-spec `phase6-anyall-drt-differential` — HEAD is this OUTCOMES-update commit
  (the F-7 doc commit); see `git log -1 phase6-anyall-drt-differential`. The last
  *code* commit before it is F-1 `2113ecf` / F-2 `fd093b3`.
- cedar (nested) `phase6-anyall-drt-differential` @ `d34291f8` (final: F-6).

## What landed, per work-item, with commits

| W | What | cedar-spec | nested cedar |
|---|---|---|---|
| — | PLAN + verify D-31 | `4d15adb` | — |
| W1 | D-31 fix: `proto_gen.rs:300` `BTreeMap`→`HashMap` so `cedar-drt/fuzz` compiles (default+anyall); `QuantifierError` arms in `validation-pbt{,-type-directed}.rs` | `b2e870b` | — |
| W2 | `anyall` feature through `cedar-policy-symcc`; `ABACSettings.enable_anyall` (default false) + fuzz→symcc forward | `e6102b3` | `839ee581` |
| W3 | Rust `cedar-policy-symcc` `.all` compile arm (D-68 literal fold / D-69 `.none` short-circuit / D-70-A guard / symbolic `set.all`) | — | `826cc339` |
| W4 | Lean `CedarProto` `All`(17)/`Item`(18) decoder (parallel `PredExpr` decoder, nested `Item`→`.item`); round-trip tests; D-29 DONE | `9912d43`, `245debb` | — |
| W5 | gated `.all`/`.any` generator arm (`generate_all_expr`/`generate_pred_body`, incl. lowered `.any` and D-76 low-weight `it`-in shape) | `72f53df` | — |
| W6/W7 | eval + validation differentials wired (`enable_anyall = cfg!(feature="anyall")`); D-41 verdict-only validation | `14ba93e` | — |
| W8 | Rust `set.all` SMT encoder (two `set.filter` under HO_ALL); FFI `Op` bridge; symcc fuzz `enable_anyall` | `1cfa9a5` | `d20a3850` |

### Review round-1 fixes

| F | What | cedar-spec | nested cedar |
|---|---|---|---|
| F-1 | `generates_all_and_any_nodes` made deterministic (fixed-seed `StdRng`, `type_directed()`, 400 iters). Ran **30×/30** here (and a 5×/5 re-confirm); round-2 reviewer independently reproduced **20×/20**. | `2113ecf` | — |
| F-2 | deterministic tests for the 3 uncaught mutations: 3a-i (value/error filter-body swap), 3b (literal-fold value), 3d (FFI `Op::SetAll` bridge+serde) — each re-run and now CAUGHT | `fd093b3` | `d296f223` |
| F-3 | DONE notes appended to D-75 + PLAN OQ-1 | (DECISIONS/PLAN) | — |
| F-4 | Rust solve path `set-logic ALL`→`HO_ALL` (match Lean, unconditional); added the missing `footprint` `.all` arm (`footprint_pred`/`footprint_all_pred`, D-70-A/D-71 — a real panic the review surfaced); cvc5-backed `check_equivalent` proof (`tests/anyall.rs`) | — | `5aae930d` |
| F-5 | SUPERSEDED-by-D-52 notes on D-51 + D-34 | (DECISIONS) | — |

### Review round-2 fixes
Round 1 all confirmed RESOLVED (incl. the footprint `.all` arm confirmed an exact Lean mirror,
arm-by-arm). Round 2 raised 2 LOW findings, both fixed:

| F | What | cedar-spec | nested cedar |
|---|---|---|---|
| F-6 | the F-4 footprint `.all` code had no deterministic test (its only exerciser, `tests/anyall.rs` over `Set<Long>`, has an empty entity footprint). Added `anyall_footprint_tests` in `enforcer.rs` over a `Set<User>` schema — `resource.owners.all(it == principal)`'s footprint is the receiver ∪ the predicate's `it`-free `principal` term; `it.manager == it` (it-dependent) contributes none. Mutation-checked: drop receiver footprint → union test fails; drop pred footprint → it-dependent test fails. Added an entity-set cvc5 case to `tests/anyall.rs`; documented why a "missing footprint flips the verdict" cvc5 case is infeasible (D-70-A rejects the only footprint-sensitive op, `it`-dependent `in`). | — | `d34291f8` |
| F-7 | OUTCOMES branch-heads bumped (cedar-spec head made relative to this commit; nested → `d34291f8`); F-1 "30×" claim corrected (30×/30 here + 5×/5 re-confirm; reviewer 20×/20). | (this commit) | — |

## Non-vacuity (reviewer-measured, `type_directed()` md=3, `enable_anyall=true`)
- `arbitrary_static_policy`: **~6.18%** of policies carry a `.all`/`.any` (103/1666; 116 `.all`
  nodes, 52 lowered `.any` `!all(!p)` shapes) — well above the 1% actionable floor.
- The D-76 `it`-dependent-`in` SymCC-unsupported shape is generated at **~3% of quantifiers**
  (entity-element branch, weight 1/7), so the lockstep-rejection path is reached.
- Default build (`enable_anyall=false`): **0** `.all`/`.any` nodes (req 3.1), unit-asserted.

## Fuzz runs (nightly `cargo-fuzz`; `ASAN_OPTIONS=detect_leaks=0` to suppress the libleanshared
one-time-global leak false-positive — crash hash `da39a3ee…` = `sha1("")`, the empty first exec)
- `eval-type-directed` — 56030 runs / 181s — 0 mismatch (W6)
- `validation-drt-type-directed` — 39545 runs / 181s — 0 mismatch (W7)
- `symcc-cex-drt` — 37490 runs / 181s (pre-F-4) + 24436 runs / 121s (post-F-4, HO_ALL) — 0 mismatch, no logic error (W8/F-4)
- `symcc-term-drt-always-allows` — 25557 runs / 121s — 0 mismatch (W8, 2nd verb)
Total ≈ 183k executions, 0 Rust/Lean mismatches.

## F-4 coverage boundary (Phase 9 follow-up)
`symcc-cex-drt` DOES invoke cvc5 (`get_cex`→`check_sat`), and with the F-4 `HO_ALL` fix it runs
clean. Whether the fuzz corpus hit a *solved SYMBOLIC* `set.all` (as opposed to a literal-fold or a
D-70-A `unsupportedError` rejection) is NOT directly countable from libFuzzer stats. The direct
proof that such a query decides under `HO_ALL` is the cvc5-backed `tests/anyall.rs`
(`check_equivalent`: identical guard ⇒ unsat, `it>0` vs `it>=0` ⇒ sat). A targeted
symbolic-`set.all` corpus seed + a solved-count metric are a Phase 9 follow-up.

## D-31
Pre-existing `cedar-drt/fuzz` compile break (`proto_gen.rs:300` `BTreeMap` vs the current proto's
`HashMap`) — FIXED in W1 (one line); every sibling collector already used `HashMap`.

## Carried to Phase 9 (not in Phase 6 scope)
- D-70 option B: set-typed footprint entries grounded via `set.filter`, lifting the D-70-A
  `it`-dependent-`in` restriction (currently rejected with `unsupportedError`).
- D-74: the honest predicate-normalization + predicate type-soundness path; the Phase-6/5B interim
  is `TypedExpr.SymCCSupported(.all)=false` (completeness-only restriction; `compile` compiles `.all`).
- D-78: narrow the `HO_ALL` logic to only-when-a-`set.all`-is-present on both engines (currently
  unconditional, matching Lean).
- A solved-symbolic-`set.all` fuzz-coverage metric (F-4 boundary above).
