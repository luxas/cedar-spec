# Phase 1 — `phase1-anyall-rust-ast`

**Branch:** `phase1-anyall-rust-ast` (both repos; confirmed checked out in both).
**Spec tasks:** T1.1 (`PredExpr`/`PredExprKind` module) and T1.2 (`ExprKind::All` + builder lowering).
**Satisfies:** 1.5 (structural set-freeness), 2.3 (lowering at the builder layer), 4.1 (shape
machinery), design Surface 1.
**All new code is `#[cfg(feature = "anyall")]`.** Default build byte-for-byte unchanged.

> Grounding note: every file/line reference below was read in the real tree at
> `/local/home/luxask/code/cedar-spec/cedar` on branch `phase1-anyall-rust-ast`
> (cedar HEAD `e181a796`). Line numbers are from that state; re-confirm with a fresh read
> before editing, since earlier edits in this phase shift later ones.

---

## (a) Goal, scope, out-of-scope

**Goal.** Introduce the Rust AST *data types* for the universal quantifier and its restricted
predicate — `ExprKind::All { expr, pred }` and the new `PredExpr`/`PredExprKind` type — plus the
`ExprBuilder` construction/lowering entry points (`all`, and `any` as `!all(!p)`), all gated on
`anyall`. Extend **every exhaustive `ExprKind` match that compiles under `--features anyall`** so
the crate builds both with and without the flag. Add unit tests that construct `All`, exercise
`PredExpr::negate()` round-trip, and prove the smart constructors reject set operators.

**In scope (T1.1, T1.2):**
- New module `cedar-policy-core/src/ast/pred.rs`: `PredExpr<T>` / `PredExprKind<T>`, a
  `PredExprBuilder`, smart constructors with set-op rejection, and `PredExpr::negate()`.
- `ExprKind::All { expr: Arc<Expr<T>>, pred: Arc<PredExpr<T>> }` variant + the arm in every
  exhaustive `ExprKind` match **reachable under `anyall`** (enumerated in §c).
- `ExprBuilder::all` + default `ExprBuilder::any` (lowering), with the type-level caveat in §e.
- Re-export from `ast.rs`.
- Non-vacuous unit tests (§g).

**Explicitly OUT of scope for Phase 1** (later phases — do NOT implement here):
- Evaluator arm (`evaluator.rs`) → Phase 3 (T3.1). Its `ExprKind` match has `_ =>` arms, so it
  compiles with the new variant present; a Phase-1 build does not need an eval arm.
- Validator / typecheck / well-formedness (`validator/*`, `Expr::try_validate` nesting/set-free/
  `it` checks) → Phase 3 (T3.2). EXCEPTION: `validator/entity_manifest.rs` is *exhaustive* and
  must get a minimal compile-only arm now (§c) or `--features anyall` won't build.
- Parser CST→AST, `it` keyword binding → Phase 4 (T4.1).
- EST/PST forms, protobuf, `Display` round-trip of `.all` surface → Phase 4 (T4.2/T4.3).
- TPE `ResidualKind::All` → Phase 6.5. `tpe/residual.rs` has a `_ => Err(())` arm, so it
  compiles without a Phase-1 change.
- Lean, DRT generator, SymCC → Phases 2, 6, 5.
- `From<Value>`-based element instantiation → Phase 2/3. Phase 1 only ensures the *types* don't
  preclude a full `Value` element (they don't: `All.expr` is a full `Expr`, and `PredExprKind::Item`
  is a nullary leaf that later binds to a `Value`).

---

## (b) Files to create / edit (cedar repo), with the specific change per file

### CREATE `cedar-policy-core/src/ast/pred.rs` (new, entirely `#[cfg(feature = "anyall")]`)
Defines, mirroring `expr.rs` conventions (`Educe` for loc-ignoring `PartialEq/Eq/Hash`, private
fields, builder-based construction):

- `pub struct PredExpr<T = ()>` wrapping `PredExprKind<T>` + `source_loc: Option<Loc>` + `data: T`
  (same three-field shape as `Expr<T>`, same `Educe(PartialEq(ignore), Hash(ignore))` on
  `source_loc`).
- `pub enum PredExprKind<T = ()>` — the restricted-but-recursive predicate (full shape in §d).
- A `PredExprBuilder<T>` (or free smart-constructor fns on `PredExpr`) that is the ONLY public
  way to build a `PredExpr`, so the set-op side-conditions can't be bypassed. Rejecting
  constructors return `Result<_, PredConstructionError>` (new error enum here); non-rejecting
  ones are infallible.
- `PredExpr::negate(self) -> PredExpr<T>` → wraps in `PredExprKind::UnaryApp { op: Not, .. }`
  (needed by `ExprBuilder::any`; see §e). It is a plain structural wrapper, NOT a smart
  constructor that simplifies — mirror how `ExprBuilder::not` just wraps.
- `eq_shape` / `hash_shape` / `cmp_shape` + `variant_order` for `PredExprKind` (same pattern as
  `Expr`, needed so `All`'s own shape machinery in §c can recurse into `pred`).
- `#[cfg(test)] mod test` with the T1.1 unit tests (§g).

### EDIT `cedar-policy-core/src/ast.rs` (module root — NOT `ast/mod.rs`, which does not exist)
After the `mod expr; pub use expr::*;` pair (lines 19–22), add:
```rust
#[cfg(feature = "anyall")]
mod pred;
#[cfg(feature = "anyall")]
pub use pred::*;
```
(Discrepancy fix: the spec/tasks say "re-export from `ast/mod.rs`". The real module root is
`ast.rs`, which uses `mod X; pub use X::*;` — there is no `ast/mod.rs`.)

### EDIT `cedar-policy-core/src/ast/expr.rs`
Add the `All` variant and the gated arm in every exhaustive match in this file (§c lists each
with line numbers). Add `ExprBuilder::all` to the concrete `impl ExprBuilder for ExprBuilder<T>`
(§e), and convenience `Expr::all` / `Expr::any` associated fns next to `Expr::greatereq`
(lines ~630–650) if a direct `Expr`-level constructor is wanted for tests.

### EDIT `cedar-policy-core/src/ast/expr_iterator.rs`
`ExprIterator::next` (the REAL `subexpressions()` traversal — it lives here, not in `expr.rs`).
Exhaustive match, no wildcard → add a gated arm pushing `expr` (and the predicate's own
sub-structure is NOT an `Expr`, so it is not pushed onto an `Expr` stack — see §c note).

### EDIT `cedar-policy-core/src/ast/expr_visitor.rs`
`ExprVisitor::visit_expr` (lines 56–82). Exhaustive, no wildcard → add a gated arm. Add a
default `visit_all` method to the trait (default `None`, matching the other `visit_*` defaults)
so no existing visitor impl breaks.

### EDIT `cedar-policy-core/src/expr_builder.rs`
Add `all` (required method, gated) and `any` (default method, gated) to the `ExprBuilder` trait
— WITH the associated-type caveat in §e, which is the single biggest design decision this phase
forces and which the tasks list glossed over.

### EDIT `cedar-policy-core/src/validator/entity_manifest.rs`
`entity_manifest_from_expr` (match starts ~line 516). **Exhaustive, no wildcard** → would break
`--features anyall`. Add a minimal compile-only gated arm:
`ExprKind::All { .. } => Err(EntityManifestError::UnsupportedCedarFeature(...))` (same pattern as
its existing `ExprKind::Error` arm at line 693). This is NOT the real entity-manifest analysis
(that is a later phase's concern if ever) — it is the minimum to keep the gated build green.
Flag in OUTCOMES that this arm is a stub.

> No other crate file needs editing in Phase 1: every other `ExprKind` match
> (`evaluator.rs`, `validator/typecheck.rs`, `validator/level_validate.rs`,
> `validator/expr_iterator.rs`, `parser/cst_to_ast.rs`, `tpe/residual.rs`, `ast/value.rs`,
> `ast/request.rs`, `ast/restricted_expr.rs`, `ast/expr_allows_errors.rs`,
> `entities/json/value.rs`, `entities/json/err.rs`) has a `_ =>` wildcard and so compiles with
> the new variant present. Confirmed by grep in the real tree. Touching them is Phase 3+ work,
> not Phase 1. **Verify this claim holds** by building `--features anyall` (§g) — any NEW
> non-exhaustive-match error names exactly the file to add to this list.

---

## (c) Exhaustive `ExprKind` match sites to extend (the full enumerated list)

New variant placed LAST in the enum (after `Record`, after the `tolerant-ast` `Error`) so no
existing `variant_order` numbers shift:

```rust
// in enum ExprKind<T>, after the tolerant-ast Error variant (expr.rs ~line 170)
#[cfg(feature = "anyall")]
/// Universal set quantifier `expr.all(pred)`. `any` lowers to `!expr.all(!pred)`.
All {
    /// Must evaluate to a Set.
    expr: Arc<Expr<T>>,
    /// Set-free, non-nested predicate over the current element `it`.
    pred: Arc<PredExpr<T>>,
},
```

Match sites (all arms `#[cfg(feature = "anyall")]`):

| # | File | Fn / item | Line (approx) | Arm to add |
|---|------|-----------|---------------|------------|
| 1 | `ast/expr.rs` | `ExprKind::variant_order` | 183–202 (`Error`=>17 at 201) | `All { .. } => 18` (after Error's 17; no renumber) |
| 2 | `ast/expr.rs` | `Expr::try_type_of` | 368–440 | `All { .. } => Some(Type::Bool)` |
| 3 | `ast/expr.rs` | `Expr::try_into_expr` | 450–531 | `All { expr, pred } => Ok(builder.all(expr…, pred…))` — recurse `expr` via `try_into_expr::<B>`, map `pred` via `pred.try_into_pred::<B>()` **IF** B has a pred type; see §e. For Phase 1 (AST→AST / AST→EST) this is the one call that depends on the §e decision. |
| 4 | `ast/expr.rs` | `Expr::substitute_general` | 823–905 | `All { expr, pred } => Ok(Expr::all(expr.substitute_general…, pred.substitute_general…))` — needs a `PredExpr::substitute_general` too (unknowns can appear in a predicate). Add it in `pred.rs`. |
| 5 | `ast/expr.rs` | `Expr::eq_shape` | 1571–1693 | `(All{expr,pred}, All{expr1,pred1}) => expr.eq_shape(expr1) && pred.eq_shape(pred1)` |
| 6 | `ast/expr.rs` | `Expr::hash_shape` | 1695–1778 | `All { expr, pred } => { expr.hash_shape(state); pred.hash_shape(state); }` |
| 7 | `ast/expr.rs` | `Expr::cmp_shape` | 1779–1933 | `(All{expr,pred}, All{expr1,pred1}) => expr.cmp_shape(expr1).then_with(|| pred.cmp_shape(pred1))` |
| 8 | `ast/expr_iterator.rs` | `ExprIterator::next` | 46–89 | `All { expr, pred } => { self.expression_stack.push(expr); /* pred is NOT Expr<T> */ }` — see note below |
| 9 | `ast/expr_visitor.rs` | `ExprVisitor::visit_expr` | 56–82 | `All { expr, pred } => self.visit_all(expr, pred, loc)` + add default `visit_all` method |
| 10 | `validator/entity_manifest.rs` | `entity_manifest_from_expr` | ~516–699 | stub `All { .. } => Err(UnsupportedCedarFeature(...))` (compile-only; see §b) |

**Non-exhaustive matches (have `_ =>`) — NOT in Phase 1, no arm needed to compile:**
`ast/expr.rs::is_projectable` (344, `matches!` with no `All`, so `All` is correctly non-projectable
by default — semantically fine); `is_ref`/`is_ref_set`/`slots` (use `matches!`/`filter_map`);
`evaluator.rs`, `validator/typecheck.rs`, `validator/level_validate.rs`,
`validator/expr_iterator.rs`, `parser/cst_to_ast.rs`, `tpe/residual.rs`, `ast/value.rs`,
`ast/request.rs`, `ast/restricted_expr.rs`, `ast/expr_allows_errors.rs`, `entities/json/*`.

> **Site #8 note (important).** `ExprIterator`'s stack is `Vec<&Expr<T>>`. The quantifier's
> `pred` is a `PredExpr<T>`, NOT an `Expr<T>`, so it CANNOT be pushed onto that stack — the
> `subexpressions()` iterator by construction does not descend into the predicate. That is the
> correct and intended behavior (predicate sub-terms are a different type and are iterated, if
> ever needed, by a separate `PredExpr::subexpressions`). Push only `expr`. This is a real
> consequence of the two-type design that the task list did not spell out.

> **Site #3 note (`try_into_expr`).** This is where the §e associated-type decision bites: the
> generic `B: ExprBuilder` must be able to build an `All`. If `all`/`any` live only on the
> concrete AST builder (option B1), then `try_into_expr::<B>` cannot call `builder.all(..)` for
> an arbitrary `B` and this arm must be written against a new `B::Pred` associated type (option
> B2) or the EST builder must also implement `all`. **Decide §e before writing site #3.** For a
> Phase-1-minimal path, option B2 (associated `type Pred` on `ExprBuilder`, defaulting such that
> AST and EST both supply it) is the clean answer and is what unblocks the `Display`/EST
> roundtrip in Phase 4 anyway.

---

## (d) `PredExpr` / `PredExprKind` shape + smart-constructor rejection rules

```rust
#[cfg(feature = "anyall")]
#[derive(Educe, Debug, Clone)]
#[educe(PartialEq, Eq, Hash)]
pub struct PredExpr<T = ()> {
    expr_kind: PredExprKind<T>,
    #[educe(PartialEq(ignore))] #[educe(Hash(ignore))]
    source_loc: Option<Loc>,
    data: T,
}

#[cfg(feature = "anyall")]
#[derive(Hash, Debug, Clone, PartialEq, Eq)]
pub enum PredExprKind<T = ()> {
    /// The current set element, surface keyword `it`. The ONLY new leaf.
    Item,
    /// A literal. `Literal` is ALREADY set-free (its doc comment says set
    /// literals must be `ExprKind::Set`, never `Literal`) — so reuse it directly,
    /// NO `SetFreeLiteral` wrapper. (Confirmed in ast/literal.rs:22–47.)
    Lit(Literal),
    Var(Var),
    If  { test_expr: Arc<PredExpr<T>>, then_expr: Arc<PredExpr<T>>, else_expr: Arc<PredExpr<T>> },
    And { left: Arc<PredExpr<T>>, right: Arc<PredExpr<T>> },
    Or  { left: Arc<PredExpr<T>>, right: Arc<PredExpr<T>> },
    UnaryApp  { op: UnaryOp,  arg: Arc<PredExpr<T>> },                       // op != IsEmpty
    BinaryApp { op: BinaryOp, arg1: Arc<PredExpr<T>>, arg2: Arc<PredExpr<T>> }, // op ∉ {Contains,ContainsAll,ContainsAny}
    ExtensionFunctionApp { fn_name: Name, args: Arc<Vec<PredExpr<T>>> },
    GetAttr { expr: Arc<PredExpr<T>>, attr: SmolStr },
    HasAttr { expr: Arc<PredExpr<T>>, attr: SmolStr },
    ExtHasAttr { expr: Arc<PredExpr<T>>, attrs: NonEmpty<SmolStr> },
    Like { expr: Arc<PredExpr<T>>, pattern: Pattern },
    Is   { expr: Arc<PredExpr<T>>, entity_type: EntityType },
    Record(Arc<BTreeMap<SmolStr, PredExpr<T>>>),  // records OK; NO Set variant, NO Slot, NO Unknown
}
```

Structural exclusions (unrepresentable, enforced by the TYPE):
- **No `All`** → nested quantifiers impossible.
- **No `Set`** → set literals impossible.
- **No `Slot`, no `Unknown`** → a predicate is evaluated per-element at runtime; slots/unknowns
  do not belong in it. (Omitted from `PredExprKind`. If a later phase finds TPE needs unknowns
  inside a predicate — req 7.3 — that is a Phase-6.5 revisit, flagged in §h, not Phase 1.)

Smart-constructor rejection rules (the fields are private; builders are the only way in):
- `PredExprBuilder::unary_app(op, arg)` → **reject `op == UnaryOp::IsEmpty`** (returns
  `Err(PredConstructionError::SetOperator(...))`). `not`/`neg` are fine. (`UnaryOp` has exactly
  `Not | Neg | IsEmpty` — confirmed ops.rs:19–34.)
- `PredExprBuilder::binary_app(op, …)` → **reject `op ∈ {Contains, ContainsAll, ContainsAny}`**.
  Allowed: `Eq, Less, LessEq, Add, Sub, Mul, In, GetTag, HasTag`. (`BinaryOp` full list confirmed
  ops.rs:46–118. Note `In` is allowed by the type here; whether an `In` whose RHS is a set is a
  "set term" is a *validator*/typecheck concern — Phase 3 — not a Phase-1 structural reject.)
- There is NO `set(...)` constructor on the pred builder at all.
- `negate(self)` wraps in `UnaryApp { op: Not }` directly (bypasses the reject check since `Not`
  is always allowed) — used by `ExprBuilder::any`.

(Why smart constructors, not split op enums: the design (decision #6) accepts the op
side-conditions as construction-time checks rather than duplicating `BinaryOp`/`UnaryOp` into
`PredBinaryOp`/`PredUnaryOp`. Nesting and set-literals — the analyzability-critical parts — are
already structural via omission.)

---

## (e) `ExprBuilder::all` (core) + `ExprBuilder::any` (default) — and the type caveat the tasks missed

**Precedent (verified in `expr_builder.rs`):** `greater`/`greatereq` are **default trait
methods** with `where Self: Sized`, e.g.
```rust
fn greatereq(self, e1: Self::Expr, e2: Self::Expr) -> Self::Expr where Self: Sized {
    self.clone().not(self.less(e1, e2))   // e1 >= e2  ==  !(e1 < e2)
}
```
So `any` *should* be the analogous default: `any(expr, pred) = !all(expr, pred.negate())`.

**⚠️ DISCREPANCY the tasks/design understate — the builder trait is NOT generic over `PredExpr`.**
`ExprBuilder` has `type Expr` but **no `type Pred`**. Every method takes/returns `Self::Expr`.
But `all(expr, pred)` and `any(expr, pred)` need a *predicate* argument whose type is NOT
`Self::Expr` (for the AST builder it is `PredExpr<T>`; for the EST builder, per design decision
#6, the EST `all`/`any` carry a *full `Expr`* inner, i.e. a different type again). You cannot
write `fn all(self, expr: Self::Expr, pred: Self::Expr)` — the AST predicate is a `PredExpr`, not
an `Expr`. Resolve with ONE of:

- **Option B1 (minimal, Phase-1-local):** add `all`/`any` ONLY to the concrete
  `impl ExprBuilder for ExprBuilder<T>` block in `expr.rs` (as inherent-style methods on that
  impl, or on an `anyall`-gated extension trait), NOT to the shared `ExprBuilder` trait. Then
  `try_into_expr::<B>` (site #3) can't call `builder.all(..)` generically — so AST→EST in Phase 1
  must special-case, OR the EST builder (Phase 4) grows its own `all`. Simplest to compile now,
  but pushes a wart into site #3.
- **Option B2 (recommended):** add an associated `type Pred` to `ExprBuilder` (AST: `PredExpr<T>`;
  EST: its full-`Expr`-inner pred form) plus required `fn all(self, expr: Self::Expr, pred:
  Self::Pred) -> Self::Expr` and default `fn any(self, expr, pred) -> Self::Expr where Self: Sized
  { self.clone().not(self.all(expr, pred.negate_pred())) }`. This makes site #3 (`try_into_expr`)
  type-check for any `B`, and is exactly what Phase 4's EST roundtrip needs anyway. Cost: a
  `type Pred` on every `ExprBuilder` impl in the tree (AST, EST, and any test builders) — all
  gated, but it IS a trait-surface change. **Recommend B2** and note it touches the EST builder's
  trait impl (a one-line `type Pred = …;` under the flag) even though EST *behavior* is Phase 4.
  `negate` lives on the pred type, so the default `any` calls `pred.negate()` (AST) — abstract
  this as a small `trait NegatablePred` or a `Self::Pred: HasNegate` bound if B2's EST pred also
  must negate; for Phase 1, since only AST constructs `All`, a `where Self::Pred: ...` bound or
  keeping `any` on the concrete AST impl is acceptable.

**Decision to record before coding:** pick B1 or B2 and write it in OUTCOMES. B2 is the smaller
total cost across Phases 1+4 and avoids a throwaway special-case in site #3. If B1 is chosen to
keep the Phase-1 diff tiny, `any` can be a default method on the concrete AST builder only and
site #3's `All` arm reconstructs via the concrete AST builder (acceptable because Phase 1's only
`try_into_expr` targets are AST→AST and the Phase-4 EST path will revisit it).

Either way:
- `all(expr, pred)` → `ExprKind::All { expr: Arc::new(expr), pred: Arc::new(pred) }`.
- `any(expr, pred)` → `self.not(self.all(expr, pred.negate()))`, i.e. `UnaryApp{Not}` wrapping an
  `All` whose `pred` is the negated predicate. There is NO `ExprKind::Any`.
- Optional `Expr::all` / `Expr::any` inherent fns next to `Expr::greatereq` for ergonomic tests.

---

## (f) Commit breakdown (logical, multiple commits)

1. **`phase1: PredExpr/PredExprKind module (T1.1)`** — new `ast/pred.rs` (types, builder, smart
   constructors with set-op rejection, `negate`, shape machinery, `substitute_general`), + the
   gated `mod pred; pub use pred::*;` in `ast.rs`. Includes the T1.1 unit tests. Green:
   `cargo check -p cedar-policy-core` with and without `--features anyall`.
2. **`phase1: ExprKind::All variant + shape/traversal arms (T1.2)`** — the variant in `expr.rs`
   and match arms at sites #1,2,4,5,6,7 (variant_order, try_type_of, substitute_general,
   eq/hash/cmp_shape), plus #8 `expr_iterator.rs` and #9 `expr_visitor.rs` (+ default
   `visit_all`), plus #10 `entity_manifest.rs` compile stub. Green: `cargo check` both ways.
3. **`phase1: ExprBuilder all/any lowering (T1.2)`** — the §e builder decision (B1/B2),
   `ExprBuilder::all`/`any`, site #3 `try_into_expr` arm, optional `Expr::all`/`Expr::any`. Green:
   `cargo test -p cedar-policy-core` both ways (this is where the construct/negate/reject tests
   run).
4. **`phase1: plan (T1.1 PredExpr module, T1.2 ExprKind::All, gated)`** — THIS PLAN.md, in the
   cedar-spec repo (committed first in practice; see "commit this plan" below).

(Commits 1–3 are in the **cedar** repo; the plan commit is in **cedar-spec**. Two repos, two
commit streams, as in Phase 0.)

---

## (g) Non-vacuous green-check plan

**Build/compile gates (every commit):**
- `cargo check -p cedar-policy-core` — no flag.
- `cargo check -p cedar-policy-core --features anyall` — this is the gate that proves the match
  arms are complete; a missing exhaustive arm fails HERE and names the file.
- Same two for `-p cedar-policy` (passthrough feature `anyall`).
- Build env: `cargo` from `~/.cargo/bin` (ENV preamble). `LD_PRELOAD` is irrelevant to a pure
  `cargo` build in the cedar repo, but keep it UNSET to match Phase 0's rule.

**Test suites + expected counts (non-vacuous):**
- `cargo test -p cedar-policy-core` (no flag) → expect the Phase-0 baseline **1571** tests, all
  pass, unchanged (proves default-build inertness, req 3.1).
- `cargo test -p cedar-policy-core --features anyall` → expect **1571 + N** where N = the new
  Phase-1 tests below (count must be > 0 and must INCREASE vs. no-flag; if the count is identical
  the new tests are not compiling under the flag — a vacuous pass, FAIL the check).
- `cargo test -p cedar-policy` both ways → expect **471** baseline unchanged no-flag; +any
  re-exported tests with flag.
- **Report the actual RUN counts**, not just exit 0 (lesson: a zero-exit with "running 0 tests"
  proves nothing).

**NEW `#[test]`s this phase MUST add** (in `ast/pred.rs` and `ast/expr.rs`, all
`#[cfg(all(test, feature = "anyall"))]`):
1. `construct_all` — build `Expr::all(Expr::set([...]), <pred over Item>)`; assert the
   `expr_kind()` is `ExprKind::All { .. }` with the expected `expr`/`pred`.
2. `pred_negate_roundtrip` — `p.negate()` is `UnaryApp{Not, p}`; `p.negate().negate()` is
   `Not(Not(p))` (NOT simplified — matches `ExprBuilder::not`'s non-simplifying behavior);
   assert via `eq_shape`.
3. `any_lowers_to_not_all_not` — `builder.any(e, p)` `eq_shape`s `builder.not(builder.all(e,
   p.negate()))`; i.e. there is no `Any` node and the `All`'s pred is `!p`. (req 2.3 at the type
   level.)
4. `smart_ctor_rejects_is_empty` — `PredExprBuilder…unary_app(IsEmpty, _)` returns `Err`.
5. `smart_ctor_rejects_contains{,_all,_any}` — `binary_app(Contains|ContainsAll|ContainsAny, …)`
   each returns `Err`; and a sanity positive: `binary_app(Eq, …)` / `unary_app(Not, …)` succeed.
6. `all_shape_eq_hash_cmp` — two structurally-equal `All`s are `eq_shape` and hash equal; a
   differing `pred` makes them unequal and orders by `cmp_shape` (covers sites #5–7).
7. `all_subexpressions_excludes_pred` — `expr.all(set, pred).subexpressions()` yields the `All`
   node and the receiver `set` and its elements, but does NOT descend into `pred` (site #8
   behavior is intended, not a bug).

**Revert-sensitivity (ideally, to prove non-vacuity):** confirm that commenting out the `All`
variant (or the smart-constructor reject) makes tests 1/4/5 fail to compile or fail — i.e. the
tests actually exercise the new code, not tautologies. Note this in OUTCOMES even if shown by
reasoning rather than a scripted revert.

---

## (h) Risks / unknowns / discrepancies the implementer MUST know

1. **Builder is not generic over the predicate type (§e).** The single biggest decision. `all`/
   `any` cannot be added to `ExprBuilder` the way `greater` was, because there is no `type Pred`.
   Pick B1 (concrete-only, tiny diff, wart in `try_into_expr`) or B2 (`type Pred` associated
   type, clean, touches EST builder's trait impl under the flag). **Recommend B2.** This is the
   most likely place Phase 1 stalls if not decided up front.
2. **Module root is `ast.rs`, not `ast/mod.rs`.** Spec/tasks say `ast/mod.rs`; it doesn't exist.
   Re-export via `mod pred; pub use pred::*;` in `ast.rs` (gated). (Corrected in §b.)
3. **Two exhaustive matches OUTSIDE `expr.rs`** that the tasks list (which only enumerated
   `expr.rs` arms) MISSED and that break `--features anyall`: `ast/expr_visitor.rs::visit_expr`
   and `validator/entity_manifest.rs::entity_manifest_from_expr`. Both have NO `_ =>` wildcard.
   `expr_iterator.rs::next` is also exhaustive and is the REAL home of `subexpressions()` (not a
   method in `expr.rs`). All three are in §c (sites #8,9,10).
4. **`subexpressions()` cannot descend into `pred`** (§c site #8 note) — the stack is
   `Vec<&Expr<T>>` and `pred` is a `PredExpr<T>`. Intended, but anything downstream assuming
   `subexpressions()` reaches every leaf (e.g. a slot/unknown scan over an `All`) will silently
   miss predicate internals. Since `PredExprKind` has no `Slot`/`Unknown` (§d), the existing
   `slots()`/`unknowns()` scans are correct to not look inside — but flag it.
5. **`Literal` reuse, not a new `SetFreeLiteral`** — confirmed set-free in `literal.rs` (variants
   `Bool|Long|String|EntityUID`, doc comment says set literals must be `ExprKind::Set`). The
   earlier "introduce `SetFreeLiteral`" idea is unnecessary; use `Literal` directly.
6. **`variant_order` numbering.** Place `All => 18` AFTER the `tolerant-ast` `Error => 17`. Do
   NOT insert in the middle (would renumber existing variants and perturb `cmp_shape` ordering of
   serialized/compared ASTs). Because `All` is `anyall`-gated and `Error` is `tolerant-ast`-gated,
   also sanity-check the number when BOTH flags are on (18 is free in all four flag combinations).
7. **`In` is structurally allowed in a predicate** (§d) — a set-free *validator* still must reject
   `it in <set>` where the RHS is a set, but that is Phase 3 (typecheck), not a Phase-1 structural
   reject. Don't try to reject `In` structurally now; the design puts only Contains/…/IsEmpty in
   the construction-time check.
8. **No `Slot`/`Unknown` in `PredExprKind`** may collide with TPE's req 7.3 (residual sub-terms
   inside a predicate) in Phase 6.5. If Phase 6.5 needs unknowns in a predicate, that is a
   deliberate later revisit — note it, do not pre-add here.
9. **`PredExpr` needs its own `substitute_general`** (site #4 recurses into `pred`). Add it in
   `pred.rs` even though full substitution semantics are a later concern — Phase 1 only needs it
   to compile and to not drop predicate structure.
10. **DecidableEq / Educe derive parity.** `Expr` uses `Educe` for loc-ignoring `PartialEq/Eq/
    Hash`; replicate exactly on `PredExpr` so `#[educe(PartialEq)]` on the `All` variant's `pred`
    field behaves like the other `Arc<Expr>` fields.
