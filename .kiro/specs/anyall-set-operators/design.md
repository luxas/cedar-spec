# Design — `.any` / `.all` non-nested set operators

This design is grounded in the real code read during authoring. File references and
enum/variant names below are the actual ones in the repo as of this writing.

## Design decisions (summary)

1. **New AST node for the universal quantifier only.** Add `All(PredExpr)` as the single
   new expression form. `any` is lowered to `!s.all(!p)`, exactly as `e1 >= e2` is defined
   as `!(e1 < e2)` — so only one node, one evaluator arm, one compiler arm, and one set of
   proofs are needed.
2. **`PredExpr` is a restricted, set-free `Expr`.** It is an `Expr` *without* the quantifier
   node, *without* set literals/`Set`, and *without* the `Set`-valued `Literal`; it adds a
   `Item` form denoting the current set element (surface keyword `it`). Set-free is the
   analyzable fragment (Mohamed et al. 2025).
3. **Evaluation is by instantiation.** `PredExpr` is turned into a concrete `Expr` by
   substituting a concrete element literal for `Item`, then evaluated by the existing
   evaluator — no second evaluator.
4. **Deterministic `QuantifierError`** (from RFC 0021): if *any* element's predicate would
   error, the whole quantifier yields one bounded, iteration-order-independent error.
5. **Everything is behind the `anyall` feature flag** on all three surfaces; the default
   build is unchanged.

---

## Surface 1 — Rust AST (`cedar/cedar-policy-core`)

### Real names found

- `cedar-policy-core/src/ast/expr.rs`: expressions are `Expr<T>`, a struct wrapping an
  `ExprKind<T>` enum plus `source_loc` and generic `data`. The variants of `ExprKind<T>`
  are: `Lit(Literal)`, `Var(Var)`, `Slot(SlotId)`, `Unknown(Unknown)`, `If { test_expr,
  then_expr, else_expr }`, `And { left, right }`, `Or { left, right }`, `UnaryApp { op, arg }`,
  `BinaryApp { op, arg1, arg2 }`, `ExtensionFunctionApp { fn_name, args }`, `GetAttr { expr,
  attr }`, `HasAttr { expr, attr }`, `ExtHasAttr { expr, attrs }`, `Like { expr, pattern }`,
  `Is { expr, entity_type }`, `Set(Arc<Vec<Expr<T>>>)`, `Record(Arc<BTreeMap<SmolStr,
  Expr<T>>>)`, and (feature `tolerant-ast`) `Error { error_kind }`.
  Note: there is **no** `Expr::All` today — "`Expr::All`" in the kernel plan maps to a new
  `ExprKind::All` variant.
- `cedar-policy-core/src/ast/literal.rs`: `enum Literal { Bool(bool), Long(Integer),
  String(SmolStr), EntityUID(Arc<EntityUID>) }`. **`Literal` already has no set variant** —
  its doc comment states set literals must become `ExprKind::Set`, not `Literal`. So the
  "introduce a new `SetFreeLiteral`" idea maps to: *`Literal` already is set-free*, and the
  set-freeness we must enforce is "the predicate contains no `ExprKind::Set` and no
  Set-valued sub-expression", not a new literal enum. We still introduce a dedicated
  `SetFreeLiteral` **type alias / newtype around `Literal`** at the `PredExpr` boundary to
  make the invariant explicit in types (see below).
- `cedar-policy-core/src/ast/ops.rs`: `enum UnaryOp { Not, Neg, IsEmpty }` and
  `enum BinaryOp { Eq, Less, LessEq, Add, Sub, Mul, In, Contains, ContainsAll, ContainsAny,
  GetTag, HasTag }`. The set operators to EXCLUDE from a set-free predicate are
  `Contains`, `ContainsAll`, `ContainsAny` and `IsEmpty` (and `In` against a set RHS).

### New / changed Rust definitions (all `#[cfg(feature = "anyall")]`)

```rust
// ast/expr.rs — new ExprKind variant
pub enum ExprKind<T = ()> {
    // ... existing variants ...
    #[cfg(feature = "anyall")]
    /// Universal set quantifier: `expr.all(pred)`. `any` lowers to `!expr.all(!pred)`.
    All {
        /// Expression that must evaluate to a Set.
        expr: Arc<Expr<T>>,
        /// Set-free, non-nested predicate over the current element `it`.
        pred: Arc<PredExpr<T>>,
    },
}
```

```rust
// ast/pred.rs (new module) — the restricted predicate expression
/// A `PredExpr` is an `Expr` restricted to the analyzable fragment:
///   * NO `ExprKind::All` (no nested quantifiers)
///   * NO `ExprKind::Set` and no Set-valued literal (set-free)
///   * PLUS an `Item` form denoting the current set element (surface `it`)
#[cfg(feature = "anyall")]
pub enum PredExprKind<T = ()> {
    /// The current set element, written `it`.
    Item,
    /// A set-free literal. `SetFreeLiteral` is a newtype over `Literal`
    /// (which is already set-free) that documents/enforces the invariant.
    Lit(SetFreeLiteral),
    Var(Var),
    If  { test_expr: Arc<PredExpr<T>>, then_expr: Arc<PredExpr<T>>, else_expr: Arc<PredExpr<T>> },
    And { left: Arc<PredExpr<T>>, right: Arc<PredExpr<T>> },
    Or  { left: Arc<PredExpr<T>>, right: Arc<PredExpr<T>> },
    UnaryApp  { op: UnaryOp,  arg: Arc<PredExpr<T>> },   // op != IsEmpty
    BinaryApp { op: BinaryOp, arg1: Arc<PredExpr<T>>, arg2: Arc<PredExpr<T>> }, // op not in {Contains, ContainsAll, ContainsAny}
    ExtensionFunctionApp { fn_name: Name, args: Arc<Vec<PredExpr<T>>> },
    GetAttr { expr: Arc<PredExpr<T>>, attr: SmolStr },
    HasAttr { expr: Arc<PredExpr<T>>, attr: SmolStr },
    ExtHasAttr { expr: Arc<PredExpr<T>>, attrs: NonEmpty<SmolStr> },
    Like { expr: Arc<PredExpr<T>>, pattern: Pattern },
    Is   { expr: Arc<PredExpr<T>>, entity_type: EntityType },
    Record(Arc<BTreeMap<SmolStr, PredExpr<T>>>), // records allowed; set literals not
}

/// Newtype documenting that this literal participates in a set-free predicate.
/// `Literal` already excludes sets, so this is a thin wrapper, not a new enum.
#[cfg(feature = "anyall")]
pub struct SetFreeLiteral(pub Literal);
```

Rationale for excluded forms:
- `Item` is the only genuinely new leaf; the surface keyword `it` resolves to it.
- `Set` / set literals: excluded structurally (no `Set` variant in `PredExprKind`).
- `Contains` / `ContainsAll` / `ContainsAny` / `IsEmpty`: excluded by construction-time
  validation on `BinaryApp` / `UnaryApp` — these take or produce set terms.
- `All`: absent from `PredExprKind`, so nesting is unrepresentable.

### Construction / lowering

- `ExprBuilder` gains `#[cfg(feature = "anyall")]` methods `all(expr, pred)` and
  `any(expr, pred)`. `any` lowers immediately to `All { expr, pred: !pred }` wrapped in a
  `UnaryApp { op: Not, .. }`, mirroring how `greatereq`/`greater` build on `less`/`lesseq`.
- CST→AST (`parser`) gains an `anyall`-gated production for the `.all( … )` / `.any( … )`
  access form and binds `it` → `PredExprKind::Item`. The validity checks for 1.4/1.5/1.6
  (no nesting, set-free, `it` only inside a predicate) run here and in `Expr::try_validate`.
- The `Display`/EST path: because AST→EST is lossless and infallible today (`into_expr::<est::Builder>()`),
  the EST builder gains a matching `All` form, and the pretty-printer emits `expr.all(pred)`.
  `any` prints as the lowered `!expr.all(!pred)` (acceptable per requirement 4.3), OR we keep
  a surface-preserving `Any` marker in the EST only — recorded as a design choice; default is
  to print the lowered form for simplicity and lossless roundtrip.

### Touch list (Rust)

`ast/expr.rs` (variant + `variant_order`, `try_type_of`→`Type::Bool`, `subexpressions`,
`eq_shape`/`hash_shape`/`cmp_shape`, `substitute_general`, `try_into_expr`), new `ast/pred.rs`,
`ast/mod.rs` re-export, `parser` CST→AST, `est` builder + JSON, `evaluator`, `validator`,
protobuf schema + round-trip, and the public `cedar-policy` re-exports — every one guarded by
`#[cfg(feature = "anyall")]`.

---

## Surface 2 — Lean spec (`cedar-lean`)

### Real names found

- `Cedar/Spec/Expr.lean`: `inductive Expr` with constructors `lit (p : Prim)`, `var (v : Var)`,
  `ite`, `and`, `or`, `unaryApp (op : UnaryOp) (expr : Expr)`, `binaryApp (op : BinaryOp)
  (a b : Expr)`, `getAttr`, `hasAttr`, `extHasAttr`, `set (ls : List Expr)`,
  `record (map : List (Attr × Expr))`, `call (xfn : ExtFun) (args : List Expr)`.
  `UnaryOp` = `not | neg | isEmpty | like | is`; `BinaryOp` = `eq | mem | hasTag | getTag |
  less | lessEq | add | sub | mul | contains | containsAll | containsAny`. There is a hand-written
  `DecidableEq` (`decExpr` / `decExprList` / `decProdAttrExprList`) that must gain the new arm.
- `Cedar/Spec/Value.lean`: `inductive Prim { bool | int | string | entityUID }`,
  `inductive Value { prim | set (s : Set Value) | record | ext }`, `inductive Error
  { entityDoesNotExist | attrDoesNotExist | tagDoesNotExist | typeError | arithBoundsError |
  extensionError }`, and `abbrev Result (α) := Except Error α`. A total order `Value.lt`
  already exists — reuse it for the deterministic QuantifierError witness.
- `Cedar/Spec/Evaluator.lean`: `def evaluate (x : Expr) (req : Request) (es : Entities) :
  Result Value` matches on each `Expr` constructor; `apply₁`, `apply₂`, `getAttr`, etc. are the
  operator helpers. The `.set` arm uses `xs.mapM₁ … Set.make`.

### New / changed Lean definitions (behind the `anyall` build flag)

```lean
-- Spec/Value.lean : new error constructor
inductive Error where
  | entityDoesNotExist
  | attrDoesNotExist
  | tagDoesNotExist
  | typeError
  | arithBoundsError
  | extensionError
  | quantifierError   -- NEW: deterministic, iteration-order-independent

-- Spec/Expr.lean : restricted predicate + the quantifier node
inductive PredExpr where
  | item                                   -- the current element `it`
  | lit  (p : Prim)                        -- Prim is already set-free
  | var  (v : Var)
  | ite  (c t e : PredExpr)
  | and  (a b : PredExpr)
  | or   (a b : PredExpr)
  | unaryApp  (op : UnaryOp)  (e : PredExpr)      -- op ≠ isEmpty
  | binaryApp (op : BinaryOp) (a b : PredExpr)    -- op ∉ {contains, containsAll, containsAny}
  | getAttr   (e : PredExpr) (a : Attr)
  | hasAttr   (e : PredExpr) (a : Attr)
  | extHasAttr (e : PredExpr) (a : Attr) (as : List Attr)
  | record (map : List (Attr × PredExpr))
  | call   (xfn : ExtFun) (args : List PredExpr)

inductive Expr where
  -- ... existing constructors unchanged ...
  | all (e : Expr) (p : PredExpr)          -- NEW; `any` desugars to `.not (.all e p.negate)`
```

Set-freeness is enforced by *omission*: `PredExpr` has no `set` constructor, no `item`-as-set,
and the excluded ops are kept out via smart constructors / a `WellFormedPred` predicate used in
the validator and typechecker.

### Evaluation (instantiation story)

Add to `Evaluator.lean`:

```lean
-- Instantiate a PredExpr into a concrete Expr by plugging a concrete element literal
-- (actually a Value) in for `.item`, then reuse `evaluate`.
def PredExpr.instantiate (p : PredExpr) (elem : Value) : Expr := …  -- `.item ↦ literal-of elem`

def evalAll (e : Expr) (p : PredExpr) (req : Request) (es : Entities) : Result Value := do
  let s ← (evaluate e req es).as (Data.Set Value)   -- type error if not a set (req 2.4)
  -- Deterministic QuantifierError: fold over the set in its canonical order.
  -- If ANY element's predicate errors, the whole thing is `.error .quantifierError`
  -- (req 2.5), independent of order; otherwise it is the conjunction of the booleans.
  match s.elts.foldl step (.ok true) with …

-- new arm in `evaluate`:
  | .all e p => evalAll e p req es
```

`any` never reaches `evaluate` directly — it is desugared to `.not (.all e p.negate)` at
construction (req 2.3), so there is a single evaluator arm and a single correctness proof.
Empty-set case follows from the fold seed `.ok true` for `all` and its negation for `any`
(req 2.7).

### Proofs (`Cedar/Thm/`) and SymCC

- `Cedar/Thm/`: proof directories that gain `.all` cases include **Validation**
  (`Thm/Validation/Typechecker*`, `Thm/Validation/Validator.lean` — well-typedness and sound
  type rule for `all`), **WellTyped** (`Thm/WellTyped*`), and the **evaluator/soundness**
  lemmas that recurse over `Expr`. Each hand-written structural recursion (including the
  `decExpr` `DecidableEq` and any `sizeOf`/termination lemmas) needs the `all` arm.
- **SymCC**: the symbolic compiler lives in `Cedar/SymCC/` (notably `SymCC/Compiler.lean`,
  which has `compilePrim` / `compileVar` / `compileApp₁` / `compileApp₂` / the top-level
  `compile`). The `all` node compiles to a **bounded conjunction over the symbolic set's
  elements** of the compiled set-free predicate; because the predicate is set-free, the
  encoding stays in the solver's decidable fragment (Mohamed et al. 2025). `SymCCOpt/` and the
  SymCC proof tree `Thm/SymCC/{Compiler,Enforcer,Verifier,Concretizer,…}` gain the matching
  arm and soundness/completeness cases. If the predicate is not set-free, the compiler returns
  an error (req 5.2) rather than emitting an undecidable term.
  - **Grounding (Mohamed et al. 2025).** Compiling `all` to a bounded conjunction over the
    symbolic set's elements is exactly that paper's *filter-elimination* strategy
    (`set.all(p,s) ≡ σ(p,s) ≈ s`). The set-free `PredExpr` is the paper's **Condition 1** (no
    set terms in a filter predicate). This is load-bearing, not cosmetic: §III-D proves that a
    filter predicate mentioning a set term (e.g. a set-valued element — the sets-of-sets case)
    makes satisfiability **undecidable** (reduction from Hilbert's Tenth Problem). So the
    compiler MUST refuse a non-set-free predicate rather than emit an encoding the solver
    cannot decide. Nested quantifiers are likewise outside the fragment (req 1.4); the paper's
    all-universal cross-product rewrite is not required for Cedar's single non-nested node.
- `lake build Cedar` from `cedar-lean/` must stay green at every commit.

---

## Surface 3 — DRT (`cedar-drt` + `cedar-policy-generators`)

### Real names found

- The AST/expression **generator** lives in `cedar-policy-generators/src/expr.rs` (with
  `abac.rs`, `schema.rs`, `settings.rs::ABACSettings`, `hierarchy.rs`). This is what produces
  `cedar_policy_core::ast::Expr` values for the fuzzers.
- The **differential eval harness** is `cedar-drt/fuzz/fuzz_targets/eval-type-directed.rs`,
  which builds a `FuzzTargetInput { schema, entities, expression: Expr, request }` and calls
  `cedar_drt::tests::run_eval_test`, comparing the Rust engine against the Lean definitional
  engine via `cedar_lean_ffi::CedarLeanFfi`. Analyzability is differentially tested by the
  `symcc-*` targets (e.g. `symcc-check-equivalent-ok.rs`, `symcc-cex-drt.rs`,
  `symcc-term-drt-*`).

### Changes (behind `anyall`)

- `cedar-policy-generators/src/expr.rs`: add an `#[cfg(feature = "anyall")]` arm that generates
  `ExprKind::All { expr, pred }` where `expr` is a Set-typed generated expression and `pred` is a
  freshly-generated **set-free, non-nested** `PredExpr` referencing `it`. A new helper
  `arbitrary_pred_expr` enforces the restriction structurally. Nesting is impossible because the
  pred generator never calls back into the `All` arm.
- The generator arm is gated on the same `anyall` flag as the engines (req 3.3), so when the
  feature is off (or the Lean FFI build does not support it) no `.all`/`.any` nodes are produced
  and the two engines are only compared on the shared fragment.
- `symcc.rs` / the `symcc-*` targets exercise analyzability: a generated `.all(P)` with set-free
  `P` must compile and the solver's verdict must match the concrete evaluator (req 5.3).
- No new fuzz *target file* is strictly required — `eval-type-directed.rs` and the `symcc-*`
  targets already consume whatever the generator emits — but a dedicated `anyall`-focused target
  may be added for coverage.

### Build/test commands (reference only — not run here)

- Lean: `lake build Cedar` from `cedar-lean/`.
- DRT: `cargo test` and `cargo test --features integration-testing` from `cedar-drt/`.

---

## QuantifierError error semantics (explicit)

Carried verbatim in spirit from RFC 0021 and stated here as the normative choice:

> **If evaluating the predicate on ANY element of the set would error, the entire `.all`
> (and therefore `.any`) expression evaluates to a single `QuantifierError`.** This holds
> even if some other element evaluates to `false` for `all` (or `true` for `any`): the
> quantifier is defined as its expansion to a conjunction/disjunction, and that expansion
> errors if any conjunct/disjunct errors.

Properties the implementation must preserve:
- **Deterministic / order-independent.** The result does not depend on set iteration order.
  Any diagnostic payload is derived deterministically — e.g. from the **smallest** erroring
  element under the existing total order (`Value.lt` in Lean, the `Ord`/`cmp_shape` ordering
  in Rust) — so it is a function of the input, not of traversal.
- **Bounded.** The error payload is bounded in size (constant in policy and input size).
- **NOT first-error-wins** (that would be non-deterministic — rejected alternative in RFC 0021).
- **NOT errors-as-false** (that would break the conjunction/disjunction interpretation —
  rejected alternative in RFC 0021).

In Lean this is `Error.quantifierError`; in Rust it is a new evaluation-error variant, both
`#[cfg(feature = "anyall")]` / flag-gated.

## Analyzability (explicit)

`.all` / `.any` are decidable **iff the predicate contains no set term** — exactly the
restriction `PredExpr` encodes. Source: Mudathir, M. (2025), *Solving Set Constraints with
Comprehensions and …*, TU Wien,
[PDF](https://repositum.tuwien.at/bitstream/20.500.12708/219545/1/Mohamed%20Mudathir%20-%202025%20-%20Solving%20Set%20Constraints%20with%20Comprehensions%20and...pdf).
Non-nested bounded set quantifiers over a set-free predicate compile to a bounded conjunction
the SMT solver can decide; nested quantifiers and set-valued predicates are excluded precisely
because they fall outside this decidable fragment.
