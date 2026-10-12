# Phase 7 — Docs & open questions (`phase7-anyall-docs`) — PLAN

> Satisfies tasks **T7.1** (feature docs, keyword `it`, set-free restriction, Mohamed et al.
> citation) and **T7.2** (record OQ-1 sets-of-sets out of scope). Branch
> `phase7-anyall-docs` cut from `phase6.5-anyall-tpe` — cedar-spec @ `23edc0d`, nested cedar @
> `4b365ea4`. **Docs-only phase: no behavior change, no new `pub` API.** Every code touch is a
> doc comment, a CHANGELOG entry, or a spec/markdown doc.
>
> **Rebase note:** Phases 6 and 6.5 are being finalized in parallel; this branch gets rebased
> onto their final tips before merge. The Phase 6.5 close-out may add one more commit to each
> phase6.5 branch — ignore it. Re-run every verifiable check in this plan after the rebase,
> because doc claims (error-message strings, counts, "supported/unsupported" verdicts) are
> pinned to code that may move.

---

## STEP 1 — Evidence survey (DONE in this plan agent; recorded so the implementer need not re-derive)

### What the feature actually is (from `requirements.md` / `design.md` / `DECISIONS.md`)
- Non-nested bounded set quantifier `E.all(P)` / `E.any(P)`; element keyword `it`; predicate
  `P` is a **set-free** `PredExpr` (no set literal, no `contains`/`containsAll`/`containsAny`,
  no `isEmpty`, no `it` used as a set). `.any` has **no AST node** — it lowers to `!E.all(!P)`
  at the `ExprBuilder` layer, exactly as `>=` lowers to `!(e1 < e2)` (D-05, D-28).
- Analyzability source: **Mohamed, Feng, Barrett, Tinelli, Reynolds, Chechik (2025),
  _Solving Set Constraints with Comprehensions and Bounded Quantifiers_, FMCAD 2025**
  (link in `requirements.md`). Set-free `PredExpr` = the paper's **Condition 1**.
- Error semantics: single deterministic, order-independent `QuantifierError` if any element's
  predicate errors; **no short-circuit on `false`** (reqs 2.5/2.6/2.8).
- Feature gate `anyall` (off by default) on every Rust crate + a Lean marker
  (`Cedar.Spec.anyAll`, documentation-only — Lean has no `#cfg`, D-08).

### Phase status actually shipped (from `tasks.md` + `branches/*/OUTCOMES.md`)
- Phase 0–4, 6.5: DONE & review-converged. Phase 5 (SymCC) & 6 (DRT): IN-PROGRESS/finalizing.
- **D-74 is OPEN.** The `well-typed ⇒ compiles` completeness fragment for `.all` is under the
  **D-74-interim**: `TypedExpr.SymCCSupported (.all _ _ _) := false`, which temporarily
  excludes **every** `.all` from the SymCC completeness lane (soundness, compile, interpret,
  evaluate, footprint of `.all` are all proven and unaffected). **The docs MUST state the
  completeness caveat as it stands under the interim, not the eventual A/C' state.**
- D-70 option A shipped: SymCC **rejects** an `.all` predicate whose `in` has an `it`-dependent
  left operand, with `.error .unsupportedError` (Lean) / the Rust `cedar-policy-symcc` mirror.
  Option B is **Phase 9** (out of this phase; `branches/phase9-anyall-set-footprint/PLAN.md`).
- D-80: TPE folds a concrete receiver, else residualizes `All` (req 7.4). D-81: Lean TPE stays
  conservative. D-82: TPE parity is in-crate, no DRT TPE harness.

### Documentation surfaces that EXIST (verified by reading both repos)
Nested cedar repo (`cedar/`):
- Per-crate `README.md`: root, `cedar-policy`, `cedar-policy-core`, `cedar-policy-symcc`,
  `cedar-policy-cli`, `cedar-policy-formatter`, `cedar-wasm`, `cedar-testing`.
- `CHANGELOG.md` exists for `cedar-policy`, `cedar-policy-cli`, `cedar-policy-symcc`,
  `cedar-wasm` — **Keep-a-Changelog format, `## [Unreleased]` heading at top.**
  **`cedar-policy-core` has NO CHANGELOG.md** (changes ride `cedar-policy`'s).
- Crate-level feature docs live in `//!` module docs of each `src/lib.rs`.
  `cedar-policy-core/src/lib.rs` has a `## Experimental features` block listing
  `experimental` / `tpe` / `partial-eval` / etc.; `#![warn(missing_docs)]` is on;
  the docsrs `#[cfg_attr(docsrs, doc(cfg(feature = "…")))]` convention is used (e.g. `tpe`).
  **`anyall` is NOT yet listed in either `cedar-policy-core/src/lib.rs` or
  `cedar-policy/src/lib.rs` feature docs** (it IS wired into the `experimental` meta-feature in
  `cedar-policy/Cargo.toml:64`).
- RFC 0021 reference file: the archived `0021-any-and-all-operators.md` from the cedar-policy
  RFCs repository, available locally OUTSIDE both worktrees (reference by title+URL, do not copy
  into the repo).

cedar-spec repo (`cedar-lean/`, `cedar-drt/`):
- `cedar-lean/README.md`, `cedar-lean/GUIDE.md` (GUIDE does not enumerate operators).
- Lean `.all`/`PredExpr`/`quantifierError` ALREADY carry doc comments
  (`Cedar/Spec/Expr.lean:68,99`, `Cedar/Spec/Value.lean:39`) — audit/extend, don't invent.
- `cedar-drt/README.md`; the fuzz settings flag is `ABACSettings.enable_anyall`
  (`cedar-policy-generators/src/settings.rs:101`, default `false`), set from
  `cfg!(feature = "anyall")` in `eval-type-directed.rs:58` and `validation_drt.rs:50`.

### Public API surface the feature adds (what rustdoc must cover — verified via grep)
Deliberately THIN. The user-facing `pub` items added under `#[cfg(feature = "anyall")]`:
- `cedar_policy_core::ast::Expr::all(expr, pred) -> Expr` and `Expr::any(expr, pred) -> Expr`
  (`cedar-policy-core/src/ast/expr.rs:802,810`).
- The `cedar_policy_core::ast::pred` module: `PredExpr` / `PredExprKind` + smart constructors
  (`ast/pred.rs`).
- Public validation error `cedar_policy::ValidationError::SetTermInQuantifier`
  (`cedar-policy/src/api/err.rs`, `.../validation_errors.rs`) — already has a doc comment.
- `cedar-policy-symcc` internal: `factory::anyall_it_var`, `factory::set_all` (crate-internal
  SymCC IR; rustdoc only if the crate renders them).
- **`QuantifierError` is core-internal only** — NOT re-exported in the public
  `cedar_policy` error enum. Document it in core rustdoc; do not claim a public surface.

### Where USER-FACING LANGUAGE DOCS actually live (decides T7.1 scope)
`cedar/README.md:136` states general Cedar documentation is at **docs.cedarpolicy.com**, source
in the separate **`cedar-policy/cedar-docs`** GitHub repo — **NOT in either of these two
worktrees.** → **The policy-author language reference for `.all`/`.any` is OUT OF SCOPE for
Phase 7 in these repos.** Phase 7's in-repo docs are: rustdoc on the public API, per-crate
CHANGELOG entries, Lean doc comments, the DRT settings doc, and the spec's own `design.md`
(OQ-1). Phase 7 WRITES A HAND-OFF NOTE for the cedar-docs website rather than inventing a docs
tree here. (This is the one genuine user-decision fork — see Open Questions Q1.)

---

## STEP 2 — Ordered work items

Each item: exact file path(s) + a verifiable check. Items are grouped T7.1 (feature docs) and
T7.2 (OQ-1). Commit granularity: one commit per crate-group for CHANGELOG/rustdoc, one for the
spec docs, one for `tasks.md`. All commits via `git commit -F <file>` with a blank line then
`Co-authored-by: Claude <noreply@anthropic.com>`.

### Group A — T7.1 crate feature docs (rustdoc, nested cedar repo)

- **A1. List `anyall` in `cedar-policy-core/src/lib.rs` `## Experimental features`.**
  Add a bullet mirroring the `tpe` bullet's style: name the feature, the operators
  `e.all(p)` / `e.any(p)`, keyword `it`, the set-free/non-nested restriction, and that it is
  experimental + off by default. One sentence on analyzability with the FMCAD-2025 cite.
  _File:_ `cedar-policy-core/src/lib.rs` (the `//!` block ~line 48–62).
  _Check:_ `cargo doc --no-deps -p cedar-policy-core --features anyall` builds **warning-free**
  (`#![warn(missing_docs)]` is on — a doc warning fails the gate); `grep -q anyall` on the
  rendered `target/doc/cedar_policy_core/index.html` crate-doc.

- **A2. List `anyall` in `cedar-policy/src/lib.rs` feature docs** (same content, pass-through
  framing: "enables `cedar-policy-core/anyall`; included in `experimental`").
  _File:_ `cedar-policy/src/lib.rs`.
  _Check:_ `cargo doc --no-deps -p cedar-policy --features experimental` warning-free.

- **A3. Rustdoc on the public constructors `Expr::all` / `Expr::any`.**
  Audit/extend the `///` on `ast/expr.rs:802,810`: state the `.any` → `!all(!p)` lowering
  (D-05/D-28), that `pred` is a set-free non-nested `PredExpr`, and the empty-set result
  (`all`⇒true, `any`⇒false, req 2.7). Add `#[cfg_attr(docsrs, doc(cfg(feature = "anyall")))]`
  if not already present (match the `tpe` items' convention).
  _File:_ `cedar-policy-core/src/ast/expr.rs`.
  _Check:_ doc builds warning-free; a `///` example that constructs `Expr::all(...)` compiles as
  a **doctest** IF the public API makes a one-liner feasible (see Q2 — `PredExpr` construction
  may be too verbose for a clean doctest; if so, use a non-running ```text``` example and say so
  in the commit message, do NOT fake a passing doctest). `cargo test --doc -p cedar-policy-core
  --features anyall` reports the doctest count (must be >0 for any ```rust``` block added, and
  must RUN, not be `ignore`d — a vacuous doctest is a lie, per the project's non-vacuous rule).

- **A4. Module rustdoc on `ast::pred`** (`PredExpr`): the analyzable fragment, what is excluded
  and why (set-free = Condition 1), the `Item`/`it` leaf, the smart-constructor rejections and
  their exact behavior. Audit the existing `//!`/`///`; extend, don't duplicate.
  _File:_ `cedar-policy-core/src/ast/pred.rs`.
  _Check:_ doc warning-free; the stated excluded ops (`contains`/`containsAll`/`containsAny`/
  `isEmpty`) match the smart-constructor code in the same file (reviewer diff-checks).

- **A5. Audit the public `SetTermInQuantifier` doc comment** (`cedar-policy/src/api/err.rs` +
  `.../validation_errors.rs`) — already present; confirm it names the set-free restriction and
  reads correctly. No change if accurate; this is a verification item, not necessarily an edit.
  _Check:_ the rendered doc text matches the actual `#[error("…")]` string
  `"for policy \`{policy_id}\`, the predicate of a set quantifier contains a set-typed
  expression"` (core `validator/diagnostics/validation_errors.rs:518`).

### Group B — T7.1 CHANGELOG entries (nested cedar repo)

- **B1. `cedar-policy/CHANGELOG.md` — under the existing top `## [Unreleased]`**, add an
  `### Added` subsection (create it if absent) with a bullet:
  "(experimental, `anyall`) Non-nested set quantifiers `e.all(p)` / `e.any(p)` over the element
  keyword `it`, behind the `anyall` feature (included in `experimental`). Set-free predicates
  only; see spec `anyall-set-operators`." Keep the file's star-convention in mind — this is a
  **new experimental feature off by default**, so it is NOT a language-breaking `*` change.
  _File:_ `cedar-policy/CHANGELOG.md`.
  _Check:_ markdown-lint / link-check passes (see D-check below); the entry sits under
  `## [Unreleased]`, not under a released version; `git diff` shows only an addition.

- **B2. `cedar-policy-symcc/CHANGELOG.md` — under `## [Unreleased]`**, add an `### Added`
  bullet: "(experimental, `anyall`) Symbolic compilation of `.all`/`.any` set quantifiers over
  set-free predicates (decidable `set.filter` encoding, Mohamed et al. FMCAD 2025). Predicates
  with an `it`-dependent `in` are rejected as unsupported (see spec D-70)." **Only add this if
  the Rust `cedar-policy-symcc` `.all` arm is present on the rebased tip** — it is present now
  (commit `826cc339`, Phase 6 W3). If a rebase drops it, drop this entry (reviewer re-checks).
  _File:_ `cedar-policy-symcc/CHANGELOG.md`.
  _Check:_ `grep -q "fn.*set_all\|anyall" cedar-policy-symcc/src/symcc/compiler.rs` confirms the
  arm exists before the entry is written; markdown-lint passes.

- **B3. `cedar-policy-core` has NO CHANGELOG** — do NOT create one (convention: core changes
  ride `cedar-policy`'s CHANGELOG). Record this explicitly in the commit message so a reviewer
  does not flag the absence as a miss.
  _Check:_ `test ! -f cedar-policy-core/CHANGELOG.md` (still absent).

### Group C — T7.1 Lean + DRT docs (cedar-spec repo)

- **C1. Audit/extend Lean doc comments** on `PredExpr` (`Cedar/Spec/Expr.lean:68`), `Expr.all`
  (`:99`), `Error.quantifierError` (`Cedar/Spec/Value.lean:39`), and the evaluator fold
  (`Cedar/Spec/Evaluator.lean` `evalAll`): the no-short-circuit rule (2.8), empty-set result,
  and the `.any` = `!all(!p)` note (already partly present). Add a short doc comment on the
  SymCC `.all` compiler arm referencing the `set.filter` encoding + D-52/D-70-A/D-74-interim.
  _Files:_ `cedar-lean/Cedar/Spec/{Expr,Value,Evaluator}.lean`,
  `cedar-lean/Cedar/SymCC/Compiler.lean` (the `.all` arm).
  _Check:_ `lake build Cedar` stays green (doc comments must not break the build);
  `LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar` per D-13. Doc comments are `/-- … -/` and attach to
  the following declaration — reviewer confirms they attach to the right decl.

- **C2. `cedar-drt/README.md` — document the `anyall` fuzz settings.** Add a short subsection:
  the `anyall` cargo feature + `ABACSettings.enable_anyall` (default off) gate `.all`/`.any`
  generation; the generator also emits the lowered `.any` (`!all(!p)`) shape and, at low weight,
  the SymCC-unsupported `it`-dependent-`in` shape (D-76); build with `LD_PRELOAD` unset.
  _File:_ `cedar-drt/README.md`.
  _Check:_ the names `enable_anyall` and `anyall` in the doc match
  `cedar-policy-generators/src/settings.rs:101` and the targets' `cfg!(feature="anyall")`;
  markdown link-check passes.

### Group D — T7.1 spec-level feature doc + decisions summary (cedar-spec repo)

- **D1. Add a reviewer-facing "Feature summary & doc map" to `design.md`** (new short section,
  or a `branches/phase7-anyall-docs/` doc if `design.md` should stay as-is — see Q3): one place
  that states, with the EXACT strings/claims a blind reviewer verifies against code:
  - syntax `e.all(p)` / `e.any(p)`, keyword `it`; the set-free + non-nested restriction;
  - the exact error messages (copy verbatim, these are the doc-claim anchors):
    - parser: ``invalid `.all`/`.any` predicate: {0}`` (+ help "a predicate may use `it`,
      request variables, literals and non-set operators, but no set literals, set operators, or
      nested `.all`/`.any`"), and ``` `it` can only be used inside the predicate of `.all(..)`
      or `.any(..)` ``` (`ItOutsidePredicate`);
    - validator: "for policy `{policy_id}`, the predicate of a set quantifier contains a
      set-typed expression" (`SetTermInQuantifier`);
    - evaluator: "the predicate of a set quantifier errored on at least one element"
      (`QuantifierError`);
  - evaluation semantics: deterministic `QuantifierError`, no short-circuit (2.5/2.6/2.8),
    empty-set (2.7);
  - validation typing: `E : Set<τ>`, `P : Bool` under `it:τ` ⇒ `Bool` (6.1);
  - **SymCC analyzability**: supported iff predicate set-free (Condition 1, Mohamed et al.
    2025); the `set.filter` encoding (D-52); the **D-70-A unsupported shape**
    (`it`-dependent `in` ⇒ `unsupportedError`); the **D-74-interim completeness caveat**
    (`well-typed ⇒ compiles` currently excludes all `.all`; soundness/compile/interpret/
    evaluate/footprint of `.all` are proven);
  - **TPE behaviour (D-80)**: concrete-receiver fold, else residual `All` (7.4);
  - **feature-flag gating** per crate + how to enable (`--features anyall`, or `experimental`);
  - **DRT/fuzz settings** (`enable_anyall`).
  _File:_ `.../design.md` (or `branches/phase7-anyall-docs/FEATURE-DOC.md` per Q3).
  _Check:_ every error string in the doc is `grep`-findable verbatim in the cited source file
  (reviewer runs the greps); every "supported/unsupported" claim matches the code arm.

- **D2. DECISIONS/open-items summary table for reviewers.** A compact table: **D-74 OPEN**
  (completeness; interim excludes all `.all`), **D-01 OPEN** (phase-9 meaning — now resolved to
  the D-70-B follow-up), and the Phase 9 follow-up list (D-70-B set-footprint; D-80 full
  per-element-residual TPE; D-81 optional Lean concrete fold; D-82 optional DRT TPE
  differential; Phase 8 benchmarks). State plainly what is NOT done.
  _File:_ same doc as D1 (a "Open items / deferred to Phase 8–9" section).
  _Check:_ each row's status matches `DECISIONS.md`'s current Status column (reviewer diffs the
  two); no row claims DONE for anything `DECISIONS.md` marks OPEN.

### Group E — T7.2 OQ-1 (sets-of-sets) explicitly out of scope

- **E1. Confirm OQ-1 is recorded as out-of-scope-by-design in `requirements.md`** (it already
  is — "RESOLVED (negatively) by Mohamed et al. 2025 … out of scope by design, not merely
  deferred") and **cross-link it from the design.md analyzability section** so a docs reader
  reaches it. T7.2 is mostly a verification + cross-reference item, not new prose: the content
  exists; Phase 7 ensures it is reachable from the feature doc (D1) and the SymCC rejection
  (5.2) narrative.
  _Files:_ `requirements.md` (verify, no change expected), `design.md` Analyzability section
  (add a one-line cross-reference to OQ-1 and Condition 1 if absent).
  _Check:_ the OQ-1 text names Condition 1 and the §III-D undecidability (Hilbert's Tenth);
  the design.md Analyzability section links to it. `grep -q "OQ-1\|Condition 1" design.md`.

### Group F — tasks.md status

- **F1. Flip Phase 7 to IN-PROGRESS with a PLAN pointer** in `tasks.md` (status table row +
  the Phase 7 section), mirroring how Phase 6 / 6.5 point at their `branches/*/PLAN.md`.
  _File:_ `.../tasks.md`.
  _Check:_ the table row for Phase 7 reads IN-PROGRESS and names
  `branches/phase7-anyall-docs/PLAN.md`.

### Commit & publish
- Commit PLAN.md + tasks.md in the **cedar-spec worktree** now (this plan agent's deliverable:
  PLAN + the tasks.md flip). The Group A–E edits are IMPLEMENTATION — **do NOT do them in this
  phase's plan step** (the seed says "Do NOT implement").
- Later implementation commits: one per group, each with the blank-line `Co-authored-by`
  trailer, via `git commit -F`.

---

## Verifiable checks — consolidated (run after any rebase)

| # | Command (from the stated worktree) | Pass condition |
|---|---|---|
| V1 | `cargo doc --no-deps -p cedar-policy-core --features anyall` (cedar) | 0 warnings (missing_docs gate) |
| V2 | `cargo doc --no-deps -p cedar-policy --features experimental` (cedar) | 0 warnings |
| V3 | `cargo doc --no-deps -p cedar-policy-symcc --features anyall` (cedar) | 0 warnings |
| V4 | `cargo test --doc -p cedar-policy-core --features anyall` (cedar) | doctests RUN, count>0 for any ```rust``` block, 0 fail |
| V5 | `lake build Cedar` (cedar-lean, `LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar`, `LD_PRELOAD` unset) | green |
| V6 | error-string audit: `grep -F "<exact message>" <source>` for each of the 4 messages in D1 | each found verbatim |
| V7 | CHANGELOG lint: entries under `## [Unreleased]`, Keep-a-Changelog shape; `git diff` additive-only | pass |
| V8 | markdown link check on every touched `.md` (e.g. `lychee` or `markdown-link-check` if available; else manual) | no dead links; the FMCAD-2025 PDF URL + docs.cedarpolicy.com resolve as written |
| V9 | `test ! -f cedar/cedar-policy-core/CHANGELOG.md` | still absent (B3) |
| V10 | non-vacuity: for any added doctest, reverting the doc example body makes V4 fail | demonstrated |

> If `markdown-link-check`/`lychee` is not installed in-sandbox, V8 degrades to a manual URL
> audit — state that in the commit message rather than claiming an automated pass.

---

## What the BLIND review must verify (doc claims vs code)

1. **Every stated error message** (parser `InvalidQuantifierPredicate` + help, `ItOutsidePredicate`,
   validator `SetTermInQuantifier`, evaluator `QuantifierError`) is reproduced VERBATIM from the
   `#[error("…")]` / `#[diagnostic(help(…))]` strings in the cited files — no paraphrase.
2. **Every count** (doctest count, any "N tests" claim) is the actual runner output, non-vacuous.
3. **Every "supported / unsupported" claim** matches a real code arm:
   - SymCC rejects `it`-dependent `in` with `unsupportedError` (D-70-A) — not "supported";
   - the D-74-interim completeness caveat is stated as *currently excludes all `.all`*, matching
     `TypedExpr.SymCCSupported (.all _ _ _) := false` in the Lean source — NOT the eventual
     A/C' state;
   - TPE folds concrete receivers / residualizes otherwise (D-80), not "fully reduces".
4. **No over-claim of public API**: `QuantifierError` is core-internal; docs must not imply a
   public `cedar_policy` evaluation-error variant that does not exist.
5. **No invented user-language-docs tree** in these repos (that lives in `cedar-docs`); the
   hand-off note is present instead (Q1 resolution).
6. **Default build unaffected**: all doc edits are under `#[cfg(feature="anyall")]`-gated items
   or feature-scoped prose; no `missing_docs` warning appears on the default `cargo doc`.

---

## Open questions (genuine user-decision forks only)

> **RESOLVED (user 2026-10-09), recorded as D-84/D-85/D-86 in `DECISIONS.md`:**
> - **Q1 → D-84 — BOTH.** In-repo rustdoc/CHANGELOG/Lean/DRT docs AND a paste-ready
>   user-language reference at `docs/language-reference-anyall.md`, plus
>   `docs/CEDAR-DOCS-HANDOFF.md` naming the target `cedar-docs` website pages.
> - **Q2 → D-85 — runnable one-liner via the public `Policy` parse path**
>   (`Policy::from_str("… resource.ports.all(it > 0) …")`), gated on the
>   `SetTermInQuantifier` variant so it runs under `cargo test --doc --features anyall`.
> - **Q3 → D-86 — the feature-summary + open-items table lives in `design.md`.**

The original fork analysis is retained below for traceability.

- **Q1 — Docs website hand-off vs in-repo markdown (the one real fork).** Policy-author
  LANGUAGE docs for `.all`/`.any` belong in the separate `cedar-policy/cedar-docs` website repo
  (per `cedar/README.md`), which is NOT in these worktrees. **Recommended:** Phase 7 writes
  rustdoc + CHANGELOG + Lean/DRT docs IN-REPO, and adds a **hand-off note** (a short
  `branches/phase7-anyall-docs/CEDAR-DOCS-HANDOFF.md` listing exactly what the website needs:
  syntax, `it`, set-free rule, error messages, examples, the experimental caveat) rather than
  inventing a user-docs tree here. _Decision needed:_ accept the hand-off-note approach, or
  does the owner want the user-language reference drafted into these repos anyway (e.g. an
  expanded crate README section)?

- **Q2 — Doctest for `Expr::all` / `Expr::any`.** Constructing a `PredExpr` through the public
  API may be verbose enough that a clean, runnable doctest is awkward. **Recommended:** add a
  runnable doctest only if it stays a readable one-liner; otherwise a non-running ```text```
  snippet (and say so). _Decision needed only if_ the owner wants a guaranteed runnable doctest
  regardless of verbosity (would mean exercising/clarifying the public builder path).

- **Q3 — Where the reviewer "feature summary + decisions table" (D1/D2) lives.** Either append a
  section to `design.md`, or keep `design.md` frozen and put it in
  `branches/phase7-anyall-docs/FEATURE-DOC.md`. **Recommended:** a new `design.md` section
  ("Phase 7 — feature summary & open items"), since `design.md` is the natural home for a
  reader and OQ-1 already lives there; fall back to the branch doc if the owner prefers
  `design.md` immutable post-authoring.

- **Non-fork (stated, not a question):** `cedar-policy-core` gets no CHANGELOG (B3), the
  user-language reference is out of these repos (Q1), and the D-74 completeness caveat is
  documented in its **interim** state — these are determined by the evidence, not open choices.
