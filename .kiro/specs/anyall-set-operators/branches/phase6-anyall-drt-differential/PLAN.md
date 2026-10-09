# Phase 6 PLAN — DRT generator + differential wiring (`phase6-anyall-drt-differential`)

**Scope (tasks.md T6.1 / T6.2):** turn on the DRT coupling for `.all`/`.any`. Add the gated
AST **generator arm** (`cedar-policy-generators`) that produces `ExprKind::All` with a set-typed
receiver and a set-free, non-nested `PredExpr` over `it` — plus the lowered `!all(!p)` `.any`
shape — and wire the `anyall` flag through every differential target so the Rust engine, the Lean
definitional engine (via `cedar-lean-ffi`), the validator, and the SymCC targets are compared on
`.all`/`.any` policies. The generator arm is the **last** surface turned on by design (req 3.3):
it is the only change that makes the two engines actually compare the new node, so it must not be
enabled until every engine understands it.

> **Deliverable of THIS plan agent:** this `PLAN.md` + the tasks.md Phase 6 status flip, both
> committed on `phase6-anyall-drt-differential` in cedar-spec. **No implementation.**

---

## 0. Branch heads (STEP 1 done)

- **cedar-spec** `phase6-anyall-drt-differential` cut from `phase5-anyall-symcc-wip-partA`
  @ `1e5d4bd` (Phase 5B D-72 WIP: `SymCCSupported` rename + `compile_well_typed` `.all` arm up to
  the D-74 obligation). Phase 5's Lean work lives on this WIP branch; per D-50 it will be
  **re-landed onto `phase5-anyall-symcc` as green logical commits later, and Phase 6 then rebased**
  onto that re-landed tip. Note this coupling: Phase 6's Lean-touching items (T6.3 proto decoder)
  assume the Phase 5B Lean tree, which is currently red only at `Thm/SymCC/Opt.lean` (D-49) and
  carries the open D-74 obligation.
- **cedar** (nested) `phase6-anyall-drt-differential` cut from `phase5-anyall-symcc`
  @ `23056938` (= Phase 4 C5 tip; Phase 5 had no Rust diff — the branch equals Phase 4's tip).

## 0b. Unavailable tooling this session
`@kirocrew-computer` MCP server was declared by the agent spec but **not configured**; its tools
were unavailable. Nothing else was blocked — all investigation used shell/read/git and live
`cargo check`.

---

## 1. D-31 verification result (STEP 2 — the hard blocker)

**D-31 is REAL and the root cause is now exact.** Measured this session with the env preamble +
`source cedar-drt/set_env_vars.sh; unset LD_PRELOAD`:

| crate | features | result |
|---|---|---|
| `cedar-drt` (lib) | default | **check OK** |
| `cedar-drt` (lib) | `anyall` | **check OK** (3 warnings, no errors) |
| `cedar-drt/fuzz` | default | **FAILS to compile** |

The fuzz crate fails on the **default** build (not only under `anyall`), so it blocks *every*
Phase 6 fuzz target, not just the `.all` ones. The single error:

```
error[E0308]: mismatched types
  --> src/proto_gen.rs:301:55
   | expr::ExprKind::Record(expr::Record { items })
   |                                       ^^^^^ expected `HashMap<String, Expr>`, found `BTreeMap<String, Expr>`
```

Root cause (verified): `cedar-drt/fuzz/src/proto_gen.rs:300` collects the record items into a
`std::collections::BTreeMap<_, _>`, but the current cedar checkout's generated proto type
`cedar_policy::proto::models::Expr`'s `Record.items` field is now a `HashMap<String, Expr>` —
cedar's `cedar-policy/build.rs` no longer configures prost `btree_map` for that message. **Every
other** record collection in the same file (lines 382, 458, 474, 482, 531, 557, 591) already uses
`HashMap`; line 300 is the lone straggler. So the fix is a **one-line type change** at that
`.collect::<...BTreeMap<_,_>>()` → `HashMap<_,_>`. This is exactly the "align the cedar checkout
or the generator" that D-31 anticipated — here the generator (`proto_gen.rs`) must align to cedar.
Must land as **the first Phase 6 commit** (W1), before any fuzz target can build.

---

## 2. Evidence reviewed (STEP 2)

- **Spec:** requirements.md (§3.3 generator-gated differential, §2.3 `.any` lowering, §2.5–2.8
  QuantifierError + no-short-circuit, §5.3 SymCC/eval agree, §1.4/1.5 nesting/set-free), design.md
  Surface 3 (`cedar-policy-generators/src/expr.rs`, `eval-type-directed.rs`, the `symcc-*`
  targets), tasks.md Phase 6, DECISIONS.md.
- **Relevant decisions:** **D-29** (Lean `CedarProto` `All`/`Item` decoder arms deferred to
  Phase 6), **D-31** (fuzz compile break — verified above), **D-32** (stray-`it` central-guard NIT,
  relevant to 6.5 not 6), **D-16/D-22** (non-bool-pred ⇒ `QuantifierError`; `RecursionLimit` not
  special-cased — watch in the eval differential), **D-70/D-72/D-73/D-74** (SymCC's `.all` support
  is RESTRICTED: `compile` rejects an `it`-dependent left operand of `in` with
  `.unsupportedError`, and `compile_well_typed` is guarded by `TypedExpr.SymCCSupported`; D-74 is
  still OPEN). The SymCC differential targets must treat those restrictions as **expected
  non-support**, not as Rust-vs-Lean mismatches.
- **Prior outcomes:** Phase 4 OUTCOMES (EST/PST/parser/proto landed; carried forward D-29, D-31,
  D-32). Phase 5 has **no OUTCOMES.md yet** (Part B in progress); Phase 5 PLAN established the
  SymCC `.all` encoding (`set.filter`, D-52) and the `SymCCSupported` guard.
- **Phase 4 protobuf (cedar `23056938`):** proto `All` = field 17, `Item` = field 18; the Rust
  decoder re-checks the predicate. The **Lean** side of that proto (CedarProto) has no `All`/`Item`
  arm yet (D-29) — confirmed: `cedar-lean/CedarProto/Expr.lean` has no field-17/18 handling.
- **Generator (`cedar-policy-generators/src/expr.rs`):** the Bool-producing arm of
  `generate_expr_for_type` is a `gen!(u, weight => …)` block holding `contains`/`containsAll`/
  `like`/`is`/`has`/… — this is exactly where a weighted `.all`/`.any` arm slots in. Receivers of
  `Type::set_of(ty)` are already produced here (e.g. the `contains` arm). `residual.rs:133-136`
  already has an `#[cfg(feature="anyall")] ExprKind::All` arm (whole-node residual, from Phase 4).
- **`it` injection:** core exposes `IT_SENTINEL = "__cedar::anyall::it"`, `is_it_sentinel`, and
  `PredExpr::try_from_expr(&expr, &is_it_sentinel)` plus a `PredExprBuilder`. So the generator can
  build an ordinary Bool `ast::Expr` whose `it` leaf is `Expr::unknown(Unknown::new_with_type(
  IT_SENTINEL, elem_ty))`, then convert with `try_from_expr` and wrap via `Expr::all`/`Expr::any`
  — reusing the whole existing generator + the construction-time set-free/nesting validation.
- **Harnesses:** `eval-type-directed.rs` builds `FuzzTargetInput{ schema, entities, expression,
  request }` and calls `cedar_drt::tests::run_eval_test` (`cedar-drt/src/tests.rs:38`), which
  compares the Rust evaluator against the Lean FFI (`cedar_lean_ffi::CedarLeanFfi`). The `symcc-*`
  targets consume `symcc.rs::{Single,Two}PolicyFuzzTargetInput`, whose `settings()` is
  `ABACSettings::type_directed()`-derived. The Lean `Expr.all` is **unconditionally present**
  (D-08), so the Lean FFI engine evaluates `.all` already; the gating is purely Rust/DRT-side.
- **`ABACSettings`** (`settings.rs`) has `enable_like`, `enable_unknowns`, … but **no
  per-feature `anyall` toggle** — Phase 6 adds one (`enable_anyall`, default `false`).
- **Rust `cedar-policy-symcc`:** its `Cargo.toml` has **no `anyall` feature** at all, and the Rust
  `compile` has no `All` arm. Because the `symcc-*` differential asserts byte-identical Rust/Lean
  SMT (Phase 5 §1.4, D-36), the Rust `.all` compile arm + the `anyall` feature pass-through
  (core → cedar-policy → cedar-policy-symcc → cedar-drt) are **Phase 6 preconditions** for turning
  the generator on for the SymCC targets.

---

## 3. Ordered work items (file paths + non-vacuous green check)

Repos: **(C)** = nested cedar, **(S)** = cedar-spec. Each commit keeps all three surfaces green;
`git commit -F <file>` with the `Co-authored-by: Claude <noreply@anthropic.com>` trailer.

- **W1 (C) — Fix D-31 so `cedar-drt/fuzz` compiles.** `cedar-drt/fuzz/src/proto_gen.rs:300`:
  change the record-items `.collect::<…BTreeMap<_,_>>()` to `HashMap<_,_>` (match the sibling
  record collectors). _Green:_ `cargo check` in `cedar-drt/fuzz` succeeds on **default** features
  (currently errors); re-run with `--features anyall` too. This unblocks all fuzz targets.

- **W2 (C) — Wire the `anyall` feature through the SymCC crate + generators `enable_anyall`.**
  Add `anyall = ["cedar-policy-core/anyall", …]` pass-through to `cedar-policy-symcc/Cargo.toml`
  (and confirm the chain `cedar-policy` → `cedar-policy-symcc` → `cedar-drt` / `cedar-drt/fuzz`
  forwards it — `cedar-policy-generators/Cargo.toml` already has it). Add `enable_anyall: bool`
  to `ABACSettings` (`cedar-policy-generators/src/settings.rs`), default **`false`** in both
  `type_directed()` and `undirected()`. _Green:_ `cargo check -p cedar-policy-symcc` and
  `cedar-drt` with and without `--features anyall`; a unit assert that the default settings have
  `enable_anyall == false` (so the default build never generates `.all`).

- **W3 (C) — Rust `cedar-policy-symcc` `.all` compile arm (byte-match the Lean encoding).**
  `cedar/cedar-policy-symcc/src/symcc/compiler.rs`: add the `#[cfg(feature="anyall")]`
  `ExprKind::All` arm mirroring the Lean D-52/D-68/D-69/D-70-A encoding **exactly**: `set.filter`
  twice (value + error) wrapped in the `Option` tri-value, concrete-literal fold when the receiver
  is a literal set (D-68), short-circuit a `.none` receiver (D-69), and **reject an `it`-dependent
  left operand of `in` with `unsupportedError`** (D-70 A / D-72). Add the matching encoder arm if
  the Rust encoder is separate. _Green:_ `cargo test -p cedar-policy-symcc --features anyall`
  (count>0 new arm tests); a focused test that a tiny `.all` policy compiles to SMT **byte-equal**
  to the Lean FFI's output for the same policy (this is the invariant the differential will
  assert). _Risk:_ this is the largest Rust item; see §4 R-1.

- **W4 (S) — Lean `CedarProto` `All`/`Item` decoder arms (D-29).**
  `cedar-lean/CedarProto/Expr.lean`: decode proto field 17 (`All{ arg, pred }`) and field 18
  (`Item`) into `Expr.all` / `PredExpr.item`, re-checking the predicate's set-free/non-nested
  side-conditions on the untrusted bytes (mirror the Rust decoder, cedar `23056938`). This is what
  lets DRT ship a `.all` AST to the Lean FFI over proto. _Green:_ `lake build Cedar`; add a
  `UnitTest/CedarProto` round-trip: a `.all` policy encoded by Rust decodes in Lean to the
  shape-equal `Expr.all` (count>0), and a malformed predicate (set term / nested) is rejected.
  _Dependency:_ sits on the Phase 5B Lean tree (D-50); land after it is re-landed green, or on the
  WIP branch if Phase 6 proceeds in parallel (flag in the final report).

- **W5 (C) — The gated generator arm `arbitrary_all_expr` (T6.1).**
  `cedar-policy-generators/src/expr.rs`: in the `Type::Bool` branch of `generate_expr_for_type`,
  add an `#[cfg(feature="anyall")]` weighted `gen!` arm, guarded by `self.settings.enable_anyall`,
  that: (a) picks an element type `τ` over **primitives, entities, and records** (per the B1
  Value-instantiation fix — elements are `Value`s, not just literals); (b) generates a receiver
  of `Type::set_of(τ)`; (c) generates a Bool-typed predicate body with a new helper
  `arbitrary_pred_expr(τ, …)` that injects `it` as `Expr::unknown(Unknown::new_with_type(
  IT_SENTINEL, τ))` and is **structurally set-free and non-nested** (never recurses into the
  `.all` arm, never emits `Set`/`contains`/`containsAll`/`containsAny`/`isEmpty`); (d) converts
  the body with `PredExpr::try_from_expr(&body, &is_it_sentinel)` and wraps with `Expr::all`;
  (e) **sometimes emits the lowered `.any` shape** via `Expr::any` (= `!all(!p)`) so the `.any`
  surface and its lowering identity (req 2.3) are actually exercised, not assumed. Also handle
  `generate_expr` (the undirected generator) and `generate_const_expr` consistently if `.all`
  should appear there. _Green:_ `cargo test -p cedar-policy-generators --features anyall`
  (count>0); a unit test that a seeded `Unstructured` yields at least one `ExprKind::All` **and**
  at least one `!all(!·)` (the `.any` shape), that every generated predicate passes
  `PredExpr::try_from_expr` (set-free/non-nested by construction), and that with
  `enable_anyall=false` **no** `All` node is ever produced (req 3.1/3.3).

- **W6 (C) — Eval differential on `.all` AND `.any` (T6.2).**
  No new target file needed: `eval-type-directed.rs` + `run_eval_test` already consume whatever the
  generator emits once W5 + the harness `SETTINGS.enable_anyall = true` (under `#[cfg(feature=
  "anyall")]`) are set. Add a **targeted** differential unit test (in `cedar-drt/tests/` or as a
  seeded corpus case): a set with a **record element** whose predicate reads an attribute of `it`
  (`owners.all(it.dept == "eng")`), a `false`-then-error set (req 2.8 ⇒ `QuantifierError`, not
  `false`), an empty set (req 2.7 ⇒ `true`/`false`), and a `.any` case. _Green:_ `cargo test`
  and `cargo test --features integration-testing` from `cedar-drt/` (confirm the Lean-FFI path
  runs — count>0 `.all` cases actually reaching `run_eval_test`, not skipped). _Watch:_ D-16
  (non-bool predicate ⇒ `QuantifierError` on both engines) and D-22 (`RecursionLimit` has no Lean
  counterpart — must not surface as a mismatch).

- **W7 (C) — Validation differential on `.all` (T6.2).**
  Ensure the validation targets (`validation-drt-type-directed.rs`,
  `validation-pbt-type-directed.rs`) accept/reject `.all` **consistently** with Lean. Per D-41 the
  mechanism differs (Lean set-free is structural; Rust checks at type-check), so the differential
  must compare the **accept/reject verdict**, not the error code. Because the Lean type rule is the
  Phase-5B Part A rule (D-11 resolved to Full), a well-typed `.all` is now accepted on both sides.
  _Green:_ DRT validation targets `cargo test` with `anyall`; a seeded case for a set-term
  predicate (rejected both sides) and a well-typed `.all` (accepted both sides).

- **W8 (C) — SymCC differential on `.all`, with D-70/D-72 restrictions as EXPECTED non-support.**
  Turn on the generator for the `symcc-*` targets (`symcc.rs::settings()` → `enable_anyall=true`
  under `#[cfg(feature="anyall")]`). The targets assert byte-identical Rust/Lean SMT (D-36) and
  that SymCC's verdict matches the concrete evaluator (req 5.3). **Crucially**, a `.all` whose
  predicate has an `it`-dependent left operand of `in` is rejected by `compile` with
  `unsupportedError` on **both** engines (D-70 A / D-72) — the target must treat a matched
  `unsupportedError` as **expected agreement**, not a failure, and must not count such a case as a
  SymCC/eval mismatch. (If W5's `arbitrary_pred_expr` is made to *avoid* generating the
  `it`-dependent-`in` shape, that is a cheaper route to green but LOSES coverage of the rejection
  path — see OQ-2.) _Green:_ `cargo test --features integration-testing` on the `symcc-*` targets;
  a seeded case for each of: a supported `.all` (compiles, SymCC verdict = eval), a `.any`, and an
  `it`-dependent-`in` `.all` (both engines return `unsupportedError`). _Dependency:_ W2+W3 (Rust
  arm + feature wiring) and the Phase-5B Lean SymCC tree.

- **W9 (S) — OUTCOMES.md + DECISIONS/tasks updates.**
  Write `branches/phase6-anyall-drt-differential/OUTCOMES.md`; append any new decisions (e.g. the
  OQ resolutions below) to DECISIONS.md; flip tasks.md Phase 6 to DONE when review converges.
  _Green:_ docs only.

**Non-vacuous rule (applies to every W-item test):** report the count of tests *run* (>0) for the
new behavior, and for W5/W6 show a mutation (drop the `.any`-shape branch, or flip the generator
weight to 0) makes a `.all`/`.any`-specific test fail — a suite that runs 0 `.all` cases proves
nothing.

---

## 4. Risks

- **R-1 (largest): Rust/Lean SMT byte-equality for `.all` (W3/W8).** The `symcc-*` differential
  asserts byte-identical SMT between Rust `cedar-policy-symcc` and Lean. The Lean `.all` encoding
  is intricate (D-52 two `set.filter` lambdas, D-68 literal-fold vs symbolic split, D-69 `.none`
  short-circuit, HO_ALL logic). The Rust arm (W3) must reproduce it to the byte — including the
  **same** literal-fold-vs-symbolic decision and the same reserved bound-var name
  (`!anyall!it`). Any divergence surfaces as a differential failure in W8. Mitigation: build W3
  against a byte-diff unit test (one tiny policy, Rust SMT vs Lean-FFI SMT) *before* W8.
- **R-2: Phase 5B is not green on `main`/`phase5-anyall-symcc` yet (D-49/D-50/D-74).** Phase 6
  branches off the WIP branch (`1e5d4bd`), which is red at `Thm/SymCC/Opt.lean` and carries the
  open D-74 obligation. W4/W8's Lean-touching work assumes a green Phase-5B tree. If Phase 5B
  re-lands with a changed SymCC encoding (e.g. D-74 resolved via option C' widening
  `SymCCSupported`), the W3 Rust arm and W8 expectations must track it. Mitigation: sequence W4/W8
  **after** Phase 5B re-lands green, or pin the exact WIP commit and rebase (note in OUTCOMES).
- **R-3: generator starves the shared fragment.** If the `.all` weight is too high, type-directed
  generation spends its budget on quantifiers and under-covers the rest. Mitigation: a modest
  weight (comparable to `contains`), and `max_depth` discipline so predicates stay shallow.
- **R-4: record/entity-element predicates hit entity-store footprint rules (D-70).** A predicate
  reading `it`'s ancestors (`in`) over a symbolic set is the exact case option A rejects; the
  generator must either avoid it or expect the rejection (OQ-2). Over-generating it inflates the
  "expected unsupported" ratio and weakens the useful (compiled-and-solved) coverage.
- **R-5: fuzz-target proto path (D-31 scope).** W1 fixes the one compile error, but Phase 6 fuzz
  targets that round-trip through proto to the Lean FFI exercise the W4 decoder; a mismatch
  between the Rust proto encoder (field 17/18) and the Lean decoder shows up only once both W1 and
  W4 are in. Mitigation: W4's round-trip unit test uses the Rust-encoded bytes directly.

---

## 5. Open questions — RESOLVED by user 2026-10-09 (D-75 / D-76); OQ-3 noted

- **OQ-1 → RESOLVED (D-75): proceed Rust-only now.** Do W1, W2, W3, W5, W6, W7 against the nested
  cedar branch (green). DEFER W4 (Lean proto decoder, D-29) and W8 (SymCC differential) until
  Phase 5B re-lands green on `phase5-anyall-symcc` AND D-74 is resolved.
- **OQ-2 → RESOLVED (D-76): yes, emit the SymCC-unsupported shape at low weight.**
  `arbitrary_pred_expr` sometimes produces the `it`-dependent left operand of `in` (the D-70 A
  rejection path), at low weight, so W8 fuzzes the lockstep `unsupportedError` rejection.
- **OQ-3 — noted (not a Phase-6 decision).** D-74 is still OPEN and defines the
  `TypedExpr.SymCCSupported` set W8's expected-support must match. Phase 6 proceeds through W7 and
  holds W8's final expectations until D-74 lands.

---

### 5-line summary
1. **D-31 verified** — `cedar-drt/fuzz` fails to compile on *default* features; exact cause is
   `proto_gen.rs:300` collecting record items into `BTreeMap` where cedar's current proto wants
   `HashMap` (every sibling collector already uses `HashMap`). One-line fix = W1, first commit.
2. The generator arm (W5) reuses the existing Bool-type generator + `IT_SENTINEL` +
   `PredExpr::try_from_expr`, is gated on a new `ABACSettings.enable_anyall` (default false), and
   **must emit the lowered `!all(!p)` `.any` shape** and vary element type over primitives /
   entities / **records**, not just assume `.any`.
3. Differential wiring threads `anyall` through eval (W6), validation (W7, verdict-not-error-code),
   and SymCC (W8) — the SymCC targets must treat D-70/D-72's `unsupportedError` (it-dependent `in`)
   as **expected agreement**, not a mismatch, and the Rust `cedar-policy-symcc` `.all` arm (W3) +
   feature wiring (W2) must byte-match the Lean encoding.
4. Phase 6 is cut from the Phase 5B **WIP** branch (red at `Thm/SymCC/Opt.lean`, open D-74), so
   Lean-dependent items (W4 proto decoder, W8 SymCC) depend on Phase 5B re-landing green and on
   D-74's resolution.
5. Open forks for the user: OQ-1 (make Rust-only progress now vs block on Phase 5B), OQ-2
   (generate the SymCC-unsupported `it`-in `.all` shape for coverage, or avoid it for a cleaner
   green), OQ-3 (D-74 defines the `SymCCSupported` set W8 must match — flag, not a Phase-6 call).
