# Phase 5 PLAN — SymCC analyzability for `.all` (`phase5-anyall-symcc`)

**Scope of this phase (tasks.md):** T5.1 — a SymCC compiler arm that compiles `all` "to a
bounded conjunction over the symbolic set's elements" of the compiled set-free predicate, and
rejects set-term predicates (req 5.1/5.2); T5.2 — the `all` case across
`Thm/SymCC/{Compiler,Enforcer,Verifier,Concretizer,…}` (req 5.1 verified). Green check: `lake
build Cedar`.

**Deliverable of THIS plan agent:** only this `PLAN.md` (committed). No implementation. Tree
otherwise clean.

> **BOTTOM LINE UP FRONT.** Phase 5 as written in tasks.md is **blocked on a user decision**
> and cannot be implemented soundly and non-vacuously as a self-contained unit, for two
> independent reasons:
>
> 1. **D-11 makes the SymCC arm unreachable.** The Lean `typeOf` conservatively rejects every
>    `.all`. SymCC's compiler and its soundness theorems are stated *for well-typed input*
>    (`compile x εnv` is specified "given an expression `x` that has type `τ` w.r.t. `Γ`"). With
>    no Lean type rule, no well-typed `.all` exists, so any Phase-5 compiler arm is **vacuously
>    unreachable** in the verified pipeline — exactly the "self-contained but empty" trap.
>    Making it reachable requires the D-11 "Full" type rule *first*.
> 2. **The trusted Term IR has no quantifier.** A *symbolic* set receiver (the normal case,
>    e.g. `context.ports.all(it >= 8000)`) compiles to an **opaque set-typed Term whose elements
>    are not statically enumerable**. "Bounded conjunction over the elements" is only literally
>    possible for a **concrete literal set**. Supporting symbolic receivers — which req 5.1
>    demands — requires adding a **new quantifier/filter `Op` to the trusted `Term`+`Encoder`
>    layer** (and likely switching the SMT logic to `HO_ALL`), a large soundness-critical change
>    with its own proof obligations.
>
> See **CRITICAL DECISION** at the end. The options and their costs are **D-33 / D-34** below.

---

## 0. Unavailable tooling this session
`@kirocrew-computer` MCP server was declared by the agent spec but **not configured**; its tools
were unavailable. Nothing else was blocked — all investigation used shell/read/git and a live
cvc5 1.4.1 binary.

---

## 1. What was read / verified (grounding)

All file references below are real, read this session.

### 1.1 How SymCC represents sets today
- **`Cedar/SymCC/Term.lean`.** `Term` = `prim | var (TermVar) | none ty | some t | set (Set
  Term) ty | record (Map Attr Term) | app (Op) (args) (retTy)`. A set is either a **concrete
  literal** `Term.set (Set.mk [t₁…tₙ]) ty` (a statically-known element list) **or an opaque
  set-typed term**: a `.var` of set type, or an `.app` whose `retTy` is `.set …` (e.g.
  `record.get` of a set attribute, a UUF returning a set, `set.inter`). There is **no
  bound-variable term, no lambda, and no quantifier/`filter`/`fold` constructor** anywhere in
  `Term` or `Op`.
- **`Cedar/SymCC/Op.lean`.** The only set ops are `Op.set.member`, `Op.set.subset`,
  `Op.set.inter` (CVC "theory of finite sets `FS`"). **No `set.all`, no `set.filter`, no
  `forall`.** Confirmed by grep: the only hits for `forall|filter|quantif` in `SymCC/` are a
  comment in `Enforcer.lean` and this phase's own TODO in `Compiler.lean`.
- **`Cedar/SymCC/Factory.lean`.** Set factory functions `set.member`, `set.subset`, `set.inter`,
  `set.isEmpty`, `set.intersects`. They constant-fold on literal sets and otherwise emit an
  `.app Op.set.member/subset/inter …`. **None of them can enumerate the elements of an opaque
  set-typed term** — there is no element list to fold over unless the term is a `.set (Set.mk
  …)` literal.
- **`Cedar/SymCC/Encoder.lean`.** Trusted SMTLib emission. Sets encode as SMT `(Set T)` with
  `set.empty` / `set.insert` (literals), and ops encode as `set.member` / `set.subset` /
  `set.inter`. Logic is `(set-logic "ALL")`; the `Option` datatype is declared; **no
  `define-fun` predicate lambdas and no quantifier are ever emitted.** Term encoding is in ANF
  and is explicitly **trusted** (not proved) — so a new Op here is a trust-surface change.
- **`Cedar/SymCC/Compiler.lean`.** `compile : Expr → SymEnv → Result Term`, producing a term of
  type `.option τ.toTermType`. Errors are modeled as the `Option` layer (`Term.none`/`Term.some`,
  `ifSome`, `isSome`). The `.all` arm is **currently `.error .unsupportedError`** (added inert in
  Phase 2). A receiver `context.ports` compiles via `compileVar .context` (a record `TermVar`)
  then `compileGetAttr` → `.app (record.get "ports") [...] (.set (.bitvec 64))` — an **opaque
  set-typed term, elements not statically known**. This is the common, important case
  (`resource.ports.all(it >= 8000)` from US-1), so "unroll concrete literals only" would reject
  it.

### 1.2 How the symbolic property is consumed
- **`Cedar/SymCC/Verifier.lean`.** `verify*` build `Asserts` (bool Terms) whose conjunction is
  UNSAT iff the property holds; the policy term `t : .option .bool` is combined with
  `enforce …` and e.g. `not (eq t (⊙true))`. The compiled `.all` term must be a `.option .bool`
  like every other node, so error semantics must thread through the `Option` layer (see §4).

### 1.3 cvc5 1.4.1 capability (measured, not assumed)
Ran four SMT-LIB probes against `/home/linuxbrew/.linuxbrew/bin/cvc5` (`cvc5 1.4.1 [git 2b2e844]`):

| Probe | Logic | Result |
|---|---|---|
| `(forall ((x Int)) (=> (set.member x S) (>= x 0)))` quantified-membership | `ALL` | **decided** (`sat`/`unsat` on both an LIA instance and a `str.prefixof` instance — not `unknown`) |
| `(= (set.filter p S) S)` filter-elimination, `p` a `define-fun` | `ALL` | **error**: "Function terms are only supported with higher-order logic. Try adding the logic prefix `HO_`." |
| same filter-elimination | `HO_ALL` | **`sat`** (works) |
| `(set.all p S)` | `ALL` | **error** (needs `HO_`) |
| `(set.all p S)` | `HO_ALL` | **`sat`** (works) |
| concrete literal set → plain `(and (>= a 0) (>= b 0))` | `ALL` | **`sat`** (no set op needed) |

**Takeaways.**
- `set.filter` / `set.all` **exist but require `HO_ALL`** (higher-order). The current encoder uses
  `ALL` and never emits predicate lambdas — switching to HO is a real trusted-encoder change.
- A **bounded quantifier `forall x. member x S ⇒ P(x)`** over a set-free body **works under plain
  `ALL` and is decided**. This is exactly Mohamed et al. (FMCAD 2025)'s decidable fragment
  (Condition 1: no set terms in the filter body) and is the natural encoding for an **opaque
  symbolic set** — but it needs a **bound-variable Term + a quantifier Op** that the IR lacks.
- A **concrete literal set** needs **no set op at all** — it unrolls to a literal `and`-chain
  over the compiled per-element predicate, reusing only existing `Op`s.

### 1.4 Rust side
- There **is** a Rust `cedar-policy-symcc` crate (v0.7.0, nested cedar repo), mirroring the Lean
  SymCC: `src/symcc/compiler.rs` has the parallel `compile(x: &Expr, env) → Result<Term>` with the
  same per-`ExprKind` arms and the same `Op`/`Factory`/`Encoder` structure.
- **The DRT `symcc-*` differential compares the Rust and Lean SMTLib byte-for-byte**
  (`cedar-drt/fuzz/src/symcc.rs`: `similar_asserts::assert_eq!(rust, lean, …)` on the encoded
  asserts; targets like `symcc-cex-drt.rs` call `CompiledPolicySet::compile` on the Rust side and
  the Lean FFI on the other). **Consequence:** whatever encoding Phase 5 picks for `.all` must be
  implemented **identically** in Rust and Lean, or Phase 6 differential fails. The Rust arm is a
  Phase 6 wiring task (Phase 5's green check is Lean-only), but the **encoding design is chosen
  now** and both sides must match. The Rust `compile` match currently has no `All` arm; under
  `--features anyall` the cedar repo must add one (exhaustiveness) — flag whether
  `cedar-policy-symcc`'s `anyall` feature is even wired (its `[features]` table exists; the
  pass-through from core/`cedar-policy` needs checking in Phase 6).

### 1.5 Proof surface that T5.2 touches
`Cedar/Thm/SymCC/` tree, read this session: `Compiler.lean` + `Compiler/{Args,Attr,Basic,Binary,
Call,Control,ExtHasAttr,ExtHasAttrRec,Invert,LitVar,Record,Set,Unary,WF,WellTyped}.lean`,
`Enforcer.lean(+dir)`, `Verifier.lean(+dir)`, `Concretizer.lean(+dir)`, `Opt.lean(+dir)`,
`WellTyped.lean`, `ValidRefs.lean`, plus `Thm/SymCC/Term/` (Term WF/semantics). The compiler
soundness statement (`Compiler.lean` docstring) is **conditioned on well-typed input**, which is
the hook D-11 blocks.

### 1.6 SymTest harness (non-vacuous test target for 5.1)
`cedar-lean/SymTest/*.lean` are cvc5-backed `TestCase SolverM` suites, aggregated in `Main.lean`
(`Arith ++ Has ++ Like ++ In ++ Decimal ++ IPAddr ++ Datetime ++ Tags ++ Solver ++ WellTyped ++
Decoder ++ Verifier`) and run via `TestSuite.runAll tests |>.run (← Solver.cvc5)` (needs the
`CVC5` env var). Representative sizes: `Has.lean` 17, `In.lean` 40 cvc5-backed cases. **A new
`SymTest/AnyAll.lean` is where Phase 5's non-vacuous, solver-executed `.all` tests belong** —
each a real cvc5 solve, counted and asserted (count > 0), per the learned non-vacuous-test rule.

---

## 2. The core design question: what does "bounded conjunction over the elements" mean here?

Three realizable encodings, given the IR as it actually is:

### Option A — SMT bounded quantifier over an opaque set (new quantifier Op)
Compile `s.all(P)` to `forall x : τ. member x ⟦s⟧ ⇒ ⟦P⟧[it := x]`, encoded under `ALL` as a
quantified membership implication (**measured decidable** in §1.3). Dually `any` already lowers to
`!all(!P)`, so no separate existential is needed.
- **Pros:** handles the *symbolic* receiver (the real use case, req 5.1); stays in plain `ALL`
  (no HO); matches the paper's decidable fragment directly.
- **Cons / cost:** needs (1) a **bound-variable Term** (`Term.bvar`/`TermVar` scoping) and a
  **`forall`/`set.all`-style `Op`** with a predicate body; (2) a **trusted Encoder arm** emitting
  the SMT `forall`; (3) a **Term-semantics definition** for the new Op (what it denotes), plus WF;
  (4) **soundness + completeness proofs** for the new Op and the compiler arm. This is the largest
  of the three, touching the trusted IR core, and interacts with the whole `Thm/SymCC/Term/`
  tree. Variable capture / de Bruijn discipline is a new concern the IR has never had.

### Option B — filter-elimination `set.filter`/`set.all` under `HO_ALL`
Compile to `set.all(λx. ⟦P⟧) ⟦s⟧` (or `set.filter(p,s) ≈ s`), the paper's filter-elimination
form, **requires switching the encoder logic to `HO_ALL`** (measured: fails under `ALL`).
- **Pros:** one op, closest to the paper's `σ(p,s)≈s` statement.
- **Cons:** **higher-order logic** changes the whole solver contract and may regress existing
  (first-order) queries' performance/stability; still needs a predicate-lambda Term the IR lacks;
  same proof burden as A plus the HO-logic switch is a global trusted-encoder change. **Not
  recommended** vs. A — A gets decidability under plain `ALL`.

### Option C — unroll over concrete literal sets only; reject/approximate opaque sets
Compile `s.all(P)` only when `⟦s⟧` is a `Term.set (Set.mk [t₁…tₙ]) ty` **literal**: emit
`⋀ᵢ ⟦P⟧[it := tᵢ]` using only existing `and`/`eq`/the compiled predicate — **no new Op, no new
proof primitive**. For an **opaque** set receiver, either `.error .unsupportedError` (reject, req
5.2-style) or over-approximate.
- **Pros:** smallest; no trusted-IR change; proofs are structural over the existing `and`.
- **Cons:** **rejects the primary use case** (`resource.ports.all(…)` over an attribute set is
  opaque), so req 5.1 ("compile `E.all(P)` … produce a term the SMT solver can decide") is only
  met for literal-set receivers — a very thin slice. The SymCC feature would analyze almost no
  real `.all` policy. Acceptable only as an explicit **interim** scope cut.

> **The compiler produces opaque set terms for the common case** (§1.1), so **Option C alone does
> not satisfy req 5.1 in spirit.** Option A is the only self-contained encoding that makes
> symbolic `.all` analyzable under the existing (first-order) solver contract. **Recommended
> target: A** — but see §3, it is gated on D-11.

---

## 3. Interaction with D-11 — is the SymCC arm even reachable?

**No, not meaningfully, while D-11 stands.** The SymCC compiler + its soundness theorems are
specified **for well-typed input** (`Compiler.lean`: "given an expression `x` that has type `τ`
…"). D-11 is that the Lean `typeOf` **conservatively rejects every `.all`**. So:

- There is **no well-typed `.all`** in the Lean pipeline. A Phase-5 compiler arm would compile a
  node the typechecker never admits, and its soundness case in `Thm/SymCC/Compiler/WellTyped.lean`
  would be **vacuous** (hypothesis `typeOf … = ok _` is unprovable/false for `.all`). That is the
  "green but empty" outcome: `lake build Cedar` passes with a vacuous arm, but nothing is actually
  verified and the SymTest cvc5 tests cannot even typecheck a `.all` policy to feed the compiler.
- **Therefore Phase 5 requires the D-11 "Full" type rule to land first** (or concurrently): a
  `typeOfPred` over `PredExpr`, a `TypedExpr.all` mirror, `EvaluatesTo` extended to admit
  `quantifierError`, and the soundness proof — the work D-11 itself describes as "days of proof
  work," touching `Thm/Validation/*` and every proof that destructs `EvaluatesTo`.

**Can a sound, self-contained Phase 5 exist WITHOUT the type rule?** Only in the degenerate sense
of Option C with the arm reachable solely from a *hand-constructed* well-typed term in a unit test
that bypasses `typeOf` — which is not the verified pipeline and does not satisfy 5.1/5.3. So the
honest answer: **a non-vacuous Phase 5 depends on D-11 being resolved to the Full rule.** This is
a **critical decision for the user** (it is the same decision D-11 already escalates; Phase 5 is
the phase that forces it).

**Proof-effort estimate (which files, rough case counts):**
- *D-11 Full type rule* (precondition): `Thm/Validation/Typechecker*` + `Validator.lean` + a new
  `typeOfPred` soundness mirror (~ the predicate analogue of the existing per-operator typing
  lemmas; the ~6.5k-line scale D-11 cites), `EvaluatesTo` extension rippling through **every**
  proof that case-splits it (dozens of lemmas). Days.
- *T5.1 compiler arm* (Option A): ~1 arm in `Compiler.lean` + factory/encoder support for the new
  Op. Small code, but the new Op's WF + semantics are new definitions.
- *T5.2 compiler soundness/completeness*: the `.all` case in `Thm/SymCC/Compiler/*` (Basic +
  likely a new `Quant.lean` sibling of `Set.lean`), `Enforcer`, `Verifier`, `Concretizer`, `Opt`.
  With a new quantifier Op, the completeness side (the compiled term is SAT iff the Cedar
  semantics has a model) is the hard part — new, not a copy of an existing arm. Estimate: the
  largest single proof item in the whole feature.

---

## 4. Error semantics in SymCC (must match `evalAll`, §2 of requirements)

The concrete `evalAll` (Phase 2/3): receiver error propagates; **any** element predicate error or
non-bool ⇒ `quantifierError`; empty ⇒ `true`; no short-circuit on `false`. SymCC models errors as
the `Option` layer (`Term.none` = error-ish/absent, `ifSome`, `isSome`).

- **Option C (literal unroll):** `⋀ᵢ ⟦P⟧[it:=tᵢ]` where each `⟦P⟧[it:=tᵢ] : .option .bool`;
  combine with the existing `compileAnd`/`ifSome` discipline so that if **any** conjunct is
  `none` (error) the whole is `none` — matching `quantifierError` collapsing to a single error.
  Empty list ⇒ `⊙true` (req 2.7). This reuses the proven `and`/`ifSome` error-propagation, so the
  error semantics come almost for free.
- **Option A (quantifier):** harder — a quantified body cannot per-element short-circuit, and the
  "any element errors ⇒ whole errors" rule must be encoded as a **second** quantifier (`exists x ∈
  s. P errors` ⇒ result is error) alongside the value quantifier, both over the opaque set. This
  is a real subtlety: the SMT encoding must represent *three* outcomes (true/false/error) of a
  quantifier, not two. **Must be designed explicitly** and is part of why Option A's completeness
  proof is heavy. (Note D-16: non-bool predicate ⇒ quantifierError; D-22: `RecursionLimit` has no
  Lean counterpart — SymCC is Lean-semantics-faithful so neither should surface specially.)

New decision recorded: **D-35** (below) — the tri-valued (true/false/error) encoding of the
quantifier result is a required design artifact for Option A, and is trivial for Option C.

---

## 5. Rust side scope (confirmation)

- Rust `cedar-policy-symcc` **must** gain the identical `.all` arm because the DRT differential
  asserts **byte-equal** SMTLib between Rust and Lean (§1.4). But that landing is **Phase 6**
  (generator + differential wiring) — Phase 5's green check is `lake build Cedar` only. Phase 5
  must nonetheless (a) pick the encoding so both can match, and (b) note the cedar-repo
  exhaustiveness/`anyall`-feature wiring as a Phase 6 precondition (the Rust `compile` match has no
  `All` arm today; `cedar-policy-symcc`'s `anyall` pass-through needs verifying).
- **In scope for Phase 5:** Lean compiler arm + Lean proofs + Lean SymTest cvc5 tests.
  **Out of scope for Phase 5 (→ Phase 6):** the Rust `cedar-policy-symcc` arm and the differential.

---

## 6. Proposed commit breakdown (CONDITIONAL on the user's D-33 choice)

> The branch cannot produce a non-vacuous green until D-11/D-33 is decided. Two shapes:

### If the user chooses **Full type rule + Option A** (the spec-faithful target)
Pre-req commit stack (may be its own branch — this is large enough that it arguably belongs with
Phase 2/3's validator, not Phase 5):
- **P0 (pre-req, D-11 Full):** `typeOfPred`, `TypedExpr.all`, `EvaluatesTo` + `quantifierError`,
  soundness. Green: `lake build Cedar` (all `Thm/Validation`, `Thm/WellTyped`). *Largest.*
Phase-5 commits:
- **C1 — new quantifier `Op` + Term + Factory + Encoder (trusted).** `Op.lean` (`set.all` or a
  bound-var `forall`), `Term.lean` (bound var), `Factory.lean` (smart constructor + literal-set
  constant-folding to the `and`-chain), `Encoder.lean` (SMT emission under `ALL`). Green: `lake
  build Cedar` (Term WF). Also update `Term.lt`/`DecidableEq`/`Repr` for the new constructor.
- **C2 — Term semantics + WF proofs for the new Op.** `Thm/SymCC/Term/*`. Green: `lake build
  Cedar`.
- **C3 — `compile` `.all` arm (T5.1).** `Compiler.lean`: emit the quantifier term; **reject
  set-term predicates** (req 5.2) — note `PredExpr` is already structurally set-free, so the
  rejection is for defense-in-depth / the EST-origin path. Green: `lake build Cedar`.
- **C4 — compiler soundness + completeness `.all` case (T5.2).** `Thm/SymCC/Compiler/*` (new
  `Quant.lean`), `Enforcer`, `Verifier`, `Concretizer`, `Opt`. Green: `lake build Cedar`. *Second
  largest.*
- **C5 — non-vacuous SymTest.** New `SymTest/AnyAll.lean`, wired into `SymTest/Main.lean`; N cvc5
  solves (literal-set `.all`, symbolic-receiver `.all`, `.any` via `!all(!·)`, an error case ⇒
  `quantifierError`, empty ⇒ true, a record-element predicate reading `it.attr`). Green: run
  `SymTest` with `CVC5` set; assert count > 0 and that a mutation (drop a conjunct / flip the
  quantifier) makes a test fail (per the non-vacuous-test learned rule).

### If the user chooses **Option C interim (literal sets only), keep D-11 conservative**
- **C1 — `compile` `.all` arm, literal-set only (T5.1 partial).** Unroll a `Term.set (Set.mk …)`
  receiver to `⋀ᵢ ⟦P⟧[it:=tᵢ]` via existing `and`/`ifSome`; **opaque receiver ⇒
  `.error .unsupportedError`** (explicit scope cut, documented). No new Op. Green: `lake build
  Cedar`. — But note the arm is still only reachable from a hand-built well-typed term unless
  D-11 is also lifted, so even C's SymTest cases need a type-rule or a test shim. **This is why C
  alone is not clearly self-contained** and the decision cannot be dodged.
- **C2 — structural `.all` case in `Thm/SymCC/*`** (vacuous-or-literal). Green: `lake build
  Cedar`.
- **C3 — SymTest literal-set cases.** As above but literal receivers only.

Each commit: `git commit -F <msgfile>` (never backticks/`$()` in `-m`, per the learned rule).

### Green-check commands (every commit)
```
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:/home/linuxbrew/.linuxbrew/bin:$PATH"
unset LD_PRELOAD; export LEAN_CC=/usr/bin/gcc LEAN_AR=/usr/bin/ar CVC5=/home/linuxbrew/.linuxbrew/bin/cvc5
cd cedar-lean
lake build Cedar.SymCC.Compiler   # fast, while iterating
lake build Cedar                  # full, before each commit
# SymTest (cvc5): build the SymTest exe and run it with CVC5 set (see D-13: LIBRARY_PATH host quirk may apply)
```

---

## 7. Proposed new decisions (record in DECISIONS.md as D-33.. — do NOT edit DECISIONS.md here)

- **D-33 (CRITICAL — the Phase 5 go/no-go).** Phase 5 cannot be non-vacuous while D-11 keeps
  `typeOf` rejecting `.all`. **Options:** (1) adopt D-11 "Full" type rule as a Phase-5 pre-req
  (spec-faithful; days of proof work) → then Option A; (2) Option C interim (literal sets only,
  thin req-5.1 coverage) and still need at least a minimal type rule or a test shim; (3) defer
  Phase 5 entirely until the user decides D-11. **Recommend (1)** if the SymCC analyzability
  guarantee is load-bearing for the feature; **(3)** if the user wants to settle D-11 first.
- **D-34 (encoding choice).** For symbolic (opaque) set receivers, use **Option A — a bounded
  quantifier `forall x. member x S ⇒ P(x)` under plain `ALL`** (measured decidable, matches
  Mohamed et al. Condition 1), **not** HO `set.filter`/`set.all` (Option B needs `HO_ALL`, a
  global trusted-encoder change) and **not** literal-only (Option C fails req 5.1 for the common
  case). Cost: a new bound-var Term + quantifier Op in the trusted IR, with WF + semantics +
  soundness/completeness proofs. Reversible only at the cost of redoing C1–C4.
- **D-35 (tri-valued quantifier result).** The SymCC `.all` term must encode three outcomes
  (true / false / `quantifierError`) to match `evalAll` (req 2.5/2.8), i.e. a value quantifier
  plus an "exists an erroring element" quantifier, both threaded through the `Option` layer.
  Trivial under Option C (reuses `compileAnd`/`ifSome`); a required explicit artifact under Option
  A. Watch D-16 (non-bool ⇒ quantifierError) and D-22 (`RecursionLimit` not special-cased).
- **D-36 (Rust/Lean lockstep).** The DRT `symcc-*` differential asserts **byte-identical** SMTLib
  between Rust `cedar-policy-symcc` and Lean (§1.4). The `.all` encoding chosen here must be
  implemented identically on both sides; the Rust arm + `anyall` feature wiring in the cedar repo
  is a **Phase 6** precondition (Phase 5 is Lean-only green), but the encoding is frozen now.

---

## 8. Open items for the implementer (after the decision)
- Confirm whether a new quantifier Op should be `Op.set.all` (set-scoped, no explicit bound var,
  keeps first-order flavor) vs. a general `Term.forall`/bound-var form; the former is closer to
  the existing `set.*` ops and may be easier to keep decidable and to encode, but check it is
  expressible under `ALL` (the §1.3 `forall` probe used an explicit bound var — re-probe the exact
  shape chosen).
- Confirm `cedar-policy-symcc`'s `anyall` feature pass-through exists (its `[features]` table is
  present; the dependency chain from core → `cedar-policy` → `cedar-policy-symcc` must forward it)
  — a Phase 6 blocker if missing, alongside D-31 (the pre-existing `cedar-drt/fuzz` proto_gen
  mismatch that already blocks Phase 6 fuzzing).
- `SymCCOpt/` (the optimized compiler) has its own `.all` arm obligation mirroring `Compiler.lean`
  (Phase 2 already added a vacuous `SymCCOpt.compile` arm per the Phase 2 OUTCOMES deviations).

---

### 5-line summary
1. The Lean SymCC Term/Op IR has **no quantifier or filter operator**, and a symbolic set
   receiver (`context.ports`) compiles to an **opaque set-typed term whose elements are not
   statically enumerable** — so "bounded conjunction over the elements" is literal only for
   concrete literal sets.
2. cvc5 1.4.1 (measured) **decides** a bounded quantifier `forall x. member x S ⇒ P(x)` under
   plain `ALL`; `set.filter`/`set.all` exist but need `HO_ALL`. Recommended encoding is the
   plain-`ALL` bounded quantifier (**D-34**, Option A) — adding a new trusted Op is the cost.
3. **D-11 blocks Phase 5:** `typeOf` rejects every `.all`, so the SymCC compiler (specified for
   well-typed input) and its soundness proofs would be **vacuously unreachable** — "green but
   empty." A non-vacuous Phase 5 needs the D-11 Full type rule to land first.
4. The DRT `symcc-*` differential asserts **byte-identical** Rust/Lean SMTLib, so the `.all`
   encoding must be mirrored in `cedar-policy-symcc` (Phase 6 wiring; encoding frozen now, D-36);
   error semantics are tri-valued true/false/quantifierError through the Option layer (D-35).
5. Deliverable: this PLAN only, committed; new decisions proposed as D-33..D-36 for DECISIONS.md
   (not edited here); commit stacks given for both the "Full rule + Option A" and the "Option C
   interim" paths.

CRITICAL DECISION NEEDED: yes — the user must resolve D-11 (adopt the Full Lean type rule for
`.all` as a Phase-5 pre-req, enabling the recommended bounded-quantifier SymCC encoding) versus an
interim literal-sets-only scope cut versus deferring Phase 5, because without a Lean type rule the
entire SymCC `.all` arm and its soundness proofs are vacuously unreachable.
