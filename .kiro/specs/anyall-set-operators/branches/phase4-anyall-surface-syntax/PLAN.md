# Phase 4 Plan — Rust surface syntax + roundtrip (`phase4-anyall-surface-syntax`)

Implements spec Phase 4 (tasks `T4.1` parser, `T4.2` EST + `Display`, `T4.3` protobuf) for the
non-nested set quantifiers `E.all(P)` / `E.any(P)` and the element keyword `it`. All work is
gated behind the `anyall` cargo feature and must leave the default build byte-for-byte unchanged.

**Scope: cedar repo only** (`cedar-spec/cedar`, the nested independent repo). No Lean, no DRT in
this phase (but this plan decides whether the Lean protobuf decoder change is Phase 4 or 6 — it
is **Phase 6**; see Design decision 5). Branch name intentionally matches the phase number
(lesson: branch N implements phase N).

Every claim below is grounded in a file read during planning; file:line anchors are given inline.

---

## Goal

Make `.all` / `.any` **writable and round-trippable** on the Rust surface, closing the four
placeholders Phases 1–3 left for Phase 4 to fill:

- EST `Builder::all` is `unreachable!` — `cedar-policy-core/src/est/expr.rs:499-501`.
- PST `Builder::all` is `unreachable!` — `cedar-policy-core/src/pst/expr.rs:1044-1046`.
- AST→protobuf serialization of `All` is `unimplemented!` — `cedar-policy/src/proto/ast.rs:532-536`.
- No parser production yet accepts `.all(...)`/`.any(...)` (today `UnreservedId::to_meth`
  rejects them as `UnknownMethod` — `cedar-policy-core/src/parser/cst_to_ast.rs:779-787`).

Acceptance (requirements): **1.1, 1.2, 1.3** (syntax accept/`it` bind/off-build reject),
**1.4, 1.6** (reject nesting / `it` outside a predicate — the Phase-4 enforcement point per D-20),
**4.1, 4.2, 4.3** (AST↔text, AST↔protobuf, AST↔EST↔text roundtrip), plus **2.3** (the `.any`
lowering is exercised through the parser). Set-term rejection 1.5 is already enforced by the
Phase-3 validator (`SetTermInQuantifier`); the parser adds the statically-detectable subset.

---

## Grounding — how the real parser lowers method calls (verified)

The architecture the plan must fit (read in `cedar-policy-core/src/parser/`):

1. **Grammar does not special-case method names.** `grammar.lalrpop:315-327`: a `Member` is a
   `Primary` followed by zero-or-more `MemAccess`, where `MemAccess := '.' IDENT`
   (`cst::MemAccess::Field`) `| '(' [ExprList] ')'` (`cst::MemAccess::Call`) `| '[' Expr ']'`.
   So `resource.ports.all(it >= 8000)` parses as `Primary(resource)` + `Field(ports)` +
   `Field(all)` + `Call([ it >= 8000 ])`. `.all`/`.any` are **ordinary method-call CST**, exactly
   like `.contains(...)` / `.isEmpty()`. **No `.lalrpop` change is needed** (and must be avoided —
   changing the grammar would risk the off-build; see decision 1).

2. **Method dispatch is one `match` on the method name:** `UnreservedId::to_meth`
   (`cst_to_ast.rs:739-795`). `"contains"` → `builder.contains`, `"isEmpty"` → `builder.is_empty`,
   etc.; the fallthrough is `UnknownMethod { id, hint }` (`:779-787`). **This is where `.all`/`.any`
   are added**, mirroring exactly how the relational arm calls `builder.greatereq(..)`
   (`cst_to_ast.rs:2321`). This is the gating point: an `#[cfg(feature = "anyall")]` arm here, and
   nowhere in the grammar.

3. **THE critical constraint — args are lowered eagerly, before the method name is seen.**
   `Node<cst::MemAccess>::to_access` (`cst_to_ast.rs:1944-1961`): a `Call(args)` is converted via
   `args.iter().map(|e| e.to_expr::<Build>())` into a `Vec<Build::Expr>` **first**; `to_meth` then
   receives already-built `Expr` values. Consequences the plan must handle:
   - The predicate `it >= 8000` is parsed as a **full `ast::Expr`**, not a `PredExpr`. So Phase 4
     must convert that `Expr` → `PredExpr` (rejecting set terms / nesting), reusing the Phase-1
     `PredExpr` smart constructors (`ast/pred.rs`).
   - The element keyword `it` inside that arg is parsed by the ordinary `Primary::Name` path
     (`cst_to_ast.rs:1988-2004`): `maybe_to_var()` is `None` for `it`, so it becomes
     `ExprOrSpecial::Name { name: "it" }`. There is **no `Expr` representation of `it` today** — a
     bare name used as a value errors downstream. So `it` cannot simply flow through the generic
     `to_expr`; the `.all`/`.any` arm needs an `it`-aware conversion (two sub-strategies in
     decision 2).

4. **`it` is a plain identifier today.** `cst.rs:89-130` `enum Ident` has `Principal/Action/
   Resource/Context/...` and `Ident(SmolStr)`; `it` lexes as `Ident("it")` via the IDENTIFIER
   regex `grammar.lalrpop:70`. There is **no reserved `it`** — satisfying 1.3 for free as long as
   the off-build never routes `it` anywhere new.

5. **The builder lowering already exists** (Phase 1): `ast::Expr::all(expr, pred)` and
   `ast::Expr::any(expr, pred)` (= `!all(expr, !pred)`) at `ast/expr.rs:802-818`; the generic
   `ExprBuilder` trait carries `type Pred` / `fn all` / `fn pred_from_ast`
   (`ast/expr.rs:1148,1468,1476`). The parser arm just calls these; it does **not** build the
   negation itself (D-05 keeps `any` lowering in the constructor).

---

## Files to touch (cedar repo, all additions `#[cfg(feature = "anyall")]`)

| File | Change |
|---|---|
| `cedar-policy-core/src/parser/cst_to_ast.rs` | `anyall` arm in `UnreservedId::to_meth` for `"all"`/`"any"`; new `Expr → PredExpr` conversion with `it`-binding + nesting/set-term/`it`-position checks. |
| `cedar-policy-core/src/parser/err.rs` | New `ToASTErrorKind` variants (nested quantifier, `it` outside predicate, set term in predicate, wrong arity for `all`/`any`). |
| `cedar-policy-core/src/est/expr.rs` | New `ExprNoExt::All { arg, pred }` (pred = full `est::Expr`, D-6); replace `Builder::all` `unreachable!`; `TryFrom`/`into_expr` both directions; `Display`. |
| `cedar-policy-core/src/pst/expr.rs` | New PST `Expr::All` form; replace `Builder::all` `unreachable!`; `Display`; AST↔PST + EST↔PST conversions (`pst/ast_conversions.rs`, `pst/est_conversions.rs`). |
| `cedar-policy-core/src/ast/expr.rs` | `Display` for `ExprKind::All` (prints `arg.all(pred)`; `any` already lowered to `!arg.all(!pred)`). Confirm `try_into_expr` All arm now routes to the real EST builder (was reachable only via the removed `unreachable!`). |
| `cedar-policy/protobuf_schema/core.proto` | New `All` message + `all` field (number **17**) in the `Expr.expr_kind` oneof; a recursive `Pred` message carrying a full `Expr`. |
| `cedar-policy/src/proto/ast.rs` | Replace the `unimplemented!` All arm (`:532`) with encode; add the decode arm with re-validation of nesting/set-free side-conditions (proto bytes are untrusted). |
| `.kiro/specs/.../tasks.md` | Flip Phase 4 rows to DONE after green. |
| `.kiro/specs/.../DECISIONS.md` | Append D-25.. (numbered below). |

**Deliberately NOT touched (grounded):**
- `grammar.lalrpop` — `.all`/`.any` are already-parseable method-call CST (grounding 1); touching
  it risks the off-build.
- `cedar-policy-formatter` — formats the **CST** (`pprint/doc.rs:20,495,748`); `.all(...)` is a
  `MemAccess::Call` it already renders (`doc.rs:763`). No new CST node, so no formatter change,
  and the formatter crate does not even see `anyall` (feature only in core + cedar-policy
  Cargo.toml — verified `grep -rln anyall --include=Cargo.toml`).
- `cedar-policy-symcc` — its `compile_expr` ends in a wildcard `_ => UnsupportedFeature`
  (`symcc/compiler.rs:819`), so a new `ExprKind::All` is non-breaking; real SymCC support is
  Phase 5. The crate does not propagate `anyall`.
- `cedar-language-server` — matches `ExprKind` non-exhaustively (`_ => None`,
  `hover/visitor.rs:86`); does not propagate `anyall`.
- Lean `CedarProto/Expr.lean` — decides nothing in Phase 4 (decision 5).

---

## Task breakdown (logical commits — cedar repo unless noted)

Order mirrors Phases 1–3: EST/PST/proto representation first (so the AST↔X conversions compile),
then the parser that produces them, then the roundtrip tests. Each commit keeps the full matrix
green.

- **C0 (cedar-spec).** This PLAN.md. (SHA reported below.)
- **C1 — EST `All` form + builder + conversions + Display.** Add `ExprNoExt::All { arg: Arc<Expr>,
  pred: Arc<Expr> }` (D-6: inner is a full EST `Expr`, not a restricted type); replace the
  `unreachable!` builder (`est/expr.rs:499`) with a real `all`; implement `EST→AST`
  (`into_expr`, `:1171`-style arm) rejecting nesting/set-terms via the `PredExpr` constructors and
  `AST→EST` (`try_into_expr`, `:1339`-style arm, structural, no re-sugar — same mechanism that
  leaves `>=` as `!(<)`); `Display`/serde JSON shape. _Satisfies 4.1 (EST half), 4.3._
- **C2 — PST `All` form + builder + conversions + Display.** Mirror C1 for PST: new `Expr::All`
  (`#[non_exhaustive]` already), replace `unreachable!` (`pst/expr.rs:1044`), AST↔PST
  (`ast_conversions.rs`) and EST↔PST (`est_conversions.rs`), `Display`. _Satisfies 4.1 (PST)._
- **C3 — Parser (`to_meth` arm) + `Expr→PredExpr` + errors.** The core of T4.1. Add the
  `#[cfg(feature="anyall")]` `"all"`/`"any"` arms in `to_meth` (`cst_to_ast.rs:747`-block) that
  take the single already-built `Expr` arg, run `expr_to_pred` (new) to convert it to `PredExpr`
  with `it`→`PredExprKind::Item`, then call `builder.all(e, pred)` / `builder.any(e, pred)`. New
  error variants in `err.rs`. _Satisfies 1.1, 1.2, 1.3, 1.4, 1.6, 2.3._
- **C4 — AST `Display` for `All`.** `expr.rs` `Display` prints `arg.all(pred)`; verify `.any`
  prints as `!arg.all(!pred)` through the existing `Not`/`All` arms and re-parses shape-equal.
  _Satisfies 4.1, 4.3._
- **C5 — Protobuf schema + encode/decode + round-trip.** Add proto `All`/`Pred` messages
  (field 17), replace `unimplemented!` (`proto/ast.rs:532`), add decode with re-validation.
  _Satisfies 4.2._
- **C6 — Roundtrip + error-case tests** (non-vacuous; see Green checks). Can fold into C3–C5 per
  surface; kept listed separately so coverage is explicit.
- **Review loop** (user mandate): fresh blind reviewer each round until no actionable findings;
  record rounds in OUTCOMES.md.

---

## Design decisions (the 7 the plan must settle)

### 1. Grammar + the off-build ("exactly as today")

`E.all(P)` / `E.any(P)` parse through the **existing** method-call CST (grounding 1), so there is
**no grammar change**. The gate lives entirely in `UnreservedId::to_meth`
(`cst_to_ast.rs:739`): an `#[cfg(feature = "anyall")]` arm matches `"all"`/`"any"`; when the
feature is **off**, that arm does not exist and `"all"`/`"any"` fall through to the existing
`UnknownMethod { id, hint }` path (`:779-787`) — i.e. **"exactly as today" = the same
`UnknownMethod` parse error a user gets for any unrecognised method today**, with the existing
suggestion hint. `it` stays an ordinary identifier on the off-build (grounding 4): nothing routes
it to a new path unless the `anyall` `all`/`any` arm fires. Rationale: smallest possible surface,
no risk to the default parser, and 1.3 holds structurally rather than by a runtime check.

### 2. CST→AST: lowering the predicate into `PredExpr`

Because args are lowered eagerly to full `Expr` (grounding 3), the `all`/`any` arm receives one
`ast::Expr` and must turn it into a `PredExpr`. Two candidate strategies; **plan adopts (A)**:

- **(A) Convert the built `Expr` → `PredExpr` (`expr_to_pred`).** Walk the arg `Expr` structurally
  into `PredExprKind`, mapping the `it` leaf and rejecting out-of-fragment forms. Reuses the
  Phase-1 `PredExpr` smart constructors (`ast/pred.rs`) which already reject
  `isEmpty`/`contains`/`containsAll`/`containsAny` and have no `Set` variant. **Problem to solve:**
  `it` has no `Expr` representation today, so the generic `to_expr` on the arg would already have
  failed on a bare `it`. Resolved by (2a) below.
- (B) Re-parse the arg CST under an `it`-aware builder. Rejected: duplicates the whole relational/
  method machinery for one arg and diverges from the "args are built once" invariant.

**(2a) Representing `it` through the eager conversion.** The arg is converted with the ordinary
`to_expr` *before* `to_meth` runs, and a bare `it` currently lands in `Primary::Name`
(`cst_to_ast.rs:1988`) as `ExprOrSpecial::Name{"it"}`, which errors as a bare value. Plan: the
`all`/`any` arm must convert the arg CST with an **`it`-recognising conversion** rather than reuse
the pre-built `Expr`. Concretely, Phase 4 adds a conversion that, scoped to the predicate, maps the
identifier `it` to a sentinel the `Expr→PredExpr` step recognises. The cleanest grounded option is
the **reserved-unknown sentinel already used by the Phase-3 validator** (D-21:
`__cedar::anyall::it`, a name un-writable in policy text): emit `it` as that reserved
`Expr::unknown`/name during arg conversion, then `expr_to_pred` maps that sentinel →
`PredExprKind::Item` and maps *any other* occurrence of a bare `it`-as-value (there won't be one,
since only this arm introduces the sentinel) as before. This keeps the single-arg-conversion
invariant and reuses an existing reserved name. (Alternative: thread an `in_predicate` flag into
`to_expr_or_special` so `Primary::Name("it")` yields a dedicated marker — more invasive to the
hot path; recorded as the fallback if the sentinel proves leaky.) **This choice is flagged D-25
(OPEN) for the reviewer** because it reuses the validator's sentinel at the parser layer.

**Checks performed during `expr_to_pred` (precise error variants, new in `err.rs`):**
- **1.4 nested quantifier:** the arg `Expr` contains an `ExprKind::All` → `NestedQuantifier`.
  (`PredExpr` has no `All` variant, so this is caught at the conversion boundary — the first typed
  layer, per design decision #6 / D-20.)
- **1.5 statically-detectable set term:** a set literal (`ExprKind::Set`) or
  `contains`/`containsAll`/`containsAny`/`isEmpty` op inside the predicate → `SetTermInPredicate`.
  (The `PredExpr` smart constructors already reject the ops; the plan surfaces a *parser* error
  rather than a panic. Full type-directed set-term rejection remains the Phase-3 validator's
  `SetTermInQuantifier` — the parser only catches the structural subset, matching requirement 1.5's
  "flagged by the parser-time well-formedness check **where statically detectable**".)
- **1.6 `it` outside a predicate:** a bare `it` reaching `Primary::Name` on the **non**-predicate
  path → `ItKeywordOutsidePredicate`. Implemented by making `it` a recognised reserved word
  **only** when the `anyall` arm is active and only inside the arg; everywhere else on the on-build
  it must error as reserved-in-invalid-position rather than silently becoming a `Name`. (Needs a
  decision on whether `it` becomes globally reserved under `anyall` — see D-26.)
- **arity:** `.all`/`.any` take exactly one argument (reuse `extract_single_argument`,
  `cst_to_ast.rs:807`); zero/≥2 → the existing `wrong_arity` error.

### 3. Display / pretty-printing

`ExprKind::All` prints as `arg.all(pred)` where `pred` is the `PredExpr` printed with its `Item`
leaf rendered as `it`. `.any` has **no node** — it is stored as `!arg.all(!pred)` (D-05), so it
prints via the existing `Not` + `All` `Display` arms as `!arg.all(!pred)`. Requirement **4.1/4.3**
explicitly accept the **lowered normal form**: `.any` round-trips as `!s.all(!p)`, exactly as
`e1 >= e2` round-trips as `!(e1 < e2)` (verified: AST→EST `try_into_expr` is structural and does
not re-sugar — `est/expr.rs:1339`-area for `Greater`/`GreaterEq`). So **Display does NOT re-sugar**
`.any`; the plan asserts the normal-form roundtrip, which the requirement calls acceptable
(4.1: "shape-equal in the lowered normal form"; 4.3: "surface-form stability is a design choice …
not a hard requirement if lowering is lossy"). The `PredExpr` `Display` is a parallel printer over
`PredExprKind` (new) since `PredExpr` is a distinct type from `Expr`.

### 4. EST (JSON)

New `ExprNoExt::All { arg: Arc<Expr>, pred: Arc<Expr> }` where **`pred` is a full `est::Expr`**
(design decision #6 / D-6: EST stays simple, no restricted `est::PredExpr` for now). The EST
`type Pred` is already `crate::ast::PredExpr` (`est/expr.rs:474`), but the *stored* EST form holds
a full EST `Expr` inner; the builder's `all` receives the AST `PredExpr`, lifts it to an EST `Expr`
via `pred_from_ast` (`est/expr.rs:504`) / an AST-`PredExpr`→EST-`Expr` embedding, and stores it.
- **AST→EST** (`try_into_expr`, structural): emit `All { arg, pred }`; the `pred` is already the
  lowered/normalised predicate; no re-sugar (same as `>=`).
- **EST→AST** (`into_expr`, `est/expr.rs:1171`-area): convert the inner EST `Expr` back to a
  `PredExpr`, **rejecting nesting and set terms at this boundary** (the first layer with the typed
  `PredExpr`) via the same `expr_to_pred` logic as the parser. The `it` leaf in EST JSON needs a
  representation — reuse the same sentinel/`Item` mapping as decision 2.
- JSON key: `"all"` with `{"arg": <expr>, "pred": <expr>}`. Flagged (D-6): a restricted
  `est::PredExpr` that makes non-nesting structural at EST is a future tightening, deferred.

### 5. PST + protobuf; and the Lean decoder question

**PST:** mirror EST — new `pst::Expr::All` (the enum is `#[non_exhaustive]`, so external matches
already carry a wildcard — `pst/mod.rs` doc), replace the `unreachable!` builder
(`pst/expr.rs:1044`), add `Display` and the AST↔PST / EST↔PST conversions.

**Protobuf:** the `Expr.expr_kind` oneof currently ends at field **16** (`ExtHasAttr`) —
`core.proto:158-177`. Add `All all = 17;` and messages:
```proto
message All { Expr arg = 1; Pred pred = 2; }
message Pred { /* recursive, mirrors Expr minus Set / All, plus an `item` marker */ }
```
Decision: **reuse `Expr` for the predicate on the wire, not a separate `Pred` message**, carrying
the `it`/`Item` leaf as the reserved-unknown sentinel (decision 2) — this avoids duplicating the
entire `Expr` message in proto and matches the "EST/PST pred is a full Expr" choice (D-6). Decode
(`proto/ast.rs`) **re-runs the nesting/set-free validation** because proto bytes are untrusted
(Phase-1 reviewer lesson). Replace the `unimplemented!` at `proto/ast.rs:532`.

**Lean `CedarProto` decoder — Phase 6, not Phase 4 (decided).** DRT ships ASTs to Lean as
**protobuf** (`cedar-drt/fuzz/src/props.rs:217-224` decodes `Expression` from proto;
`CedarProto/Expr.lean` is the Lean-side wire decoder, keyed by proto field number). A new proto
field 17 therefore *will* need a Lean `CedarProto/Expr.lean` arm — **but only once DRT generates
`.all` and sends it to Lean, which is Phase 6** (the generator arm is Phase 6 / T6.1 and is gated
on the same flag). In Phase 4 the protobuf round-trip is **Rust-internal** (encode→decode→AST in
`cedar-policy`), so no Lean change is required to make Phase 4 green. **Plan: reserve field 17 and
the message shape now; the Lean decoder arm is a Phase-6 prerequisite recorded as a follow-up**
(and noted in Phase 6's plan). This matches the Phase-3 follow-up already listing a Phase-6
`EvaluationError` proto/decoder gap.

### 6. Formatter and other CST/EST matchers

Grounded above (Files-not-touched): the **formatter** operates on the CST and already renders
`MemAccess::Call` (`pprint/doc.rs:763`), so `.all(it >= 8000)` formats with no change and the crate
never sees `anyall`. **symcc** (`_ => UnsupportedFeature`, `compiler.rs:819`) and
**language-server** (`_ => None`, `hover/visitor.rs:86`) match `ExprKind` with wildcards and do not
propagate `anyall`, so neither breaks. The binding exhaustive-match risk is confined to
`cedar-policy-core` + `cedar-policy` under `anyall`/`--all-features`, which Phases 1–3 already swept
— Phase 4 only *fills* the placeholders those sweeps left, so the matrix stays the governing check.

### 7. Tests (non-vacuous — counts required, mutation-checked)

Per the retained lesson, every green claim must show tests **run** (count>0) and, for new behavior,
a mutation that makes them fail. Tests to add (all `#[cfg(feature="anyall")]`):
- **Parse/print roundtrip** (`cst_to_ast` tests): `resource.ports.all(it >= 8000)` parses to
  `ExprKind::All`; `...any(it == 3)` parses to `!all(!(it==3))`; `parse → Display → parse` is
  shape-equal (both `.all` and `.any`, incl. record-element predicate `owners.all(it.dept=="eng")`).
- **EST roundtrip:** AST → EST JSON → AST shape-equal; the JSON `"all"` shape is as specified;
  EST→AST rejects a nested-quantifier and a set-term predicate.
- **Protobuf roundtrip:** AST → proto bytes → AST shape-equal; decode of a hand-built nested/
  set-term proto is rejected (untrusted-bytes re-validation).
- **Error cases:** 1.4 nested `s.all(it.all(...))` → `NestedQuantifier`; 1.5
  `s.all(it.contains(1))` / `s.all([1].contains(it))` → set-term error; 1.6 bare `it` outside a
  predicate → `ItKeywordOutsidePredicate`; arity 0/2 → `wrong_arity`.
- **Off-build (1.3):** without `anyall`, `s.all(it >= 1)` → the existing `UnknownMethod` parse
  error; `it` parses as an ordinary identifier (a `has`/attr context) unchanged.
- **Mutations to prove non-vacuity:** (a) make `expr_to_pred` accept a nested `All` → the 1.4 test
  fails; (b) drop the set-term check → the 1.5 tests fail; (c) make `.any` call `all` without
  negating → the `.any` roundtrip test fails.

**Green matrix (must all pass with `--tests`), per the Phase-1/3 lesson that feature *combinations*
break, not single flags:**
- core: `default`, `--features anyall`, `--features anyall,tolerant-ast`,
  `--features experimental`, `--all-features`.
- cedar-policy: `default`, `--features experimental`, `--features protobufs`,
  `--features protobufs,anyall`, `--all-features` (`protobufs` is a cedar-policy feature, not a
  core one; corrected after review round 1).
- Report lib test counts default vs `anyall` and the exact delta (expect `+N` new tests, 0 ignored),
  as Phases 1 (+12) and 3 (+48) did.
- `cargo clippy --all-features` clean (lib) for both crates.
- Inertness: `default` artifact unchanged; every new item `#[cfg(feature="anyall")]`; diff additive.

Env for all builds (host quirk, D-13 / lesson): `export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"; unset LD_PRELOAD`.

---

## Green checks (per task)

- **T4.1 parser:** core parser tests pass with and without `anyall`; off-build gives `UnknownMethod`
  (1.3); on-build accepts `.all`/`.any`, binds `it`, rejects 1.4/1.5(static)/1.6.
- **T4.2 EST + Display:** AST↔EST↔text roundtrip tests pass with `anyall`; EST→AST rejects
  nesting/set-terms.
- **T4.3 protobuf:** AST↔proto round-trip test passes with `anyall,protobufs`; untrusted-bytes
  decode re-validates.

## Risks

- **R1 — `it` through the eager arg conversion (decision 2a).** The arg is built as a full `Expr`
  before `to_meth`, and `it` has no `Expr` form. The sentinel-reuse approach is the least invasive,
  but reuses the validator's reserved unknown at the parser layer — **D-25, flagged for the
  reviewer**. Fallback: thread an `in_predicate` flag through `to_expr_or_special`.
- **R2 — making `it` reserved under `anyall` (1.6).** If `it` becomes globally reserved whenever
  `anyall` is on, an existing policy using `it` as an attribute/name would break *on the on-build*
  (acceptable: `anyall` is opt-in and the keyword is the feature's point) but must NOT affect the
  off-build. **D-26.**
- **R3 — proto wire choice (reuse `Expr` vs new `Pred` message).** Reusing `Expr` is simpler but
  lets malformed (nested/set-term) preds onto the wire; mitigated by decode-time re-validation.
  **D-27.**
- **R4 — feature-combination matrix.** The Phase-1/3 lesson: a single `--features anyall` check is
  insufficient. The full matrix above is mandatory before any green claim.
- **R5 — Lean decoder (Phase 6).** Field 17 must be mirrored in `CedarProto/Expr.lean` before Phase
  6 differential; recorded as a Phase-6 prerequisite, not a Phase-4 task.

## Discrepancies vs tasks.md

- tasks.md T4.1 says the production "calls `builder.all(..)`/`builder.any(..)`" — correct, but
  tasks.md does **not** mention that args are lowered eagerly, so the real work is the
  `Expr→PredExpr` conversion + `it` representation (grounding 3), which this plan makes explicit.
- tasks.md T4.2 says EST `pred` is a full `Expr` — matches design D-6; confirmed against
  `est/expr.rs` (`ExprNoExt` is a flat enum with `Arc<Expr>` children).
- tasks.md does not state whether the Lean proto decoder changes in Phase 4; this plan decides
  **Phase 6** (decision 5) and records the follow-up.
- tasks.md lists no explicit error-variant names; this plan proposes `NestedQuantifier`,
  `ItKeywordOutsidePredicate`, `SetTermInPredicate` in `err.rs`.

## Minor decisions for DECISIONS.md (D-25 onward)

- **D-25 (OPEN — needs reviewer eye).** `it` is carried through the eager arg conversion as the
  reserved-unknown sentinel `__cedar::anyall::it` (reusing the Phase-3 validator's D-21 name), and
  `expr_to_pred` maps that sentinel → `PredExprKind::Item`. Reversal: thread an `in_predicate` flag
  through `to_expr_or_special` instead.
- **D-26 (OPEN).** Under `anyall`, `it` becomes a recognised reserved word so that `it` outside a
  predicate is a parse error (1.6); on the off-build `it` stays an ordinary identifier (1.3). The
  on-build therefore rejects pre-existing policies that used `it` as a name — accepted because
  `anyall` is opt-in.
- **D-27 (SETTLED).** Protobuf carries the predicate as a reused `Expr` message (field 17 `All`),
  not a separate recursive `Pred` message, with decode-time re-validation of the nesting/set-free
  side-conditions. Reversal: add a dedicated `Pred` proto message mirroring `PredExpr`.
- **D-28 (SETTLED).** `Display` does not re-sugar `.any`; it prints the lowered `!arg.all(!pred)`
  normal form, which 4.1/4.3 explicitly permit (same as `>=` → `!(<)`).
- **D-29 (SETTLED).** The Lean `CedarProto/Expr.lean` decoder arm for proto field 17 is a **Phase 6**
  prerequisite (DRT ships proto to Lean), not Phase 4; Phase 4's proto round-trip is Rust-internal.
