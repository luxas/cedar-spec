# Requirements — `.any` / `.all` non-nested set operators

## Overview

Add non-nested bounded set quantifiers `.all` and `.any` to Cedar, so a policy can
test whether a predicate holds for every element (or some element) of a set. The
feature is gated behind a new Cargo feature `anyall` and the analogous Lean build
flag, so the default build is byte-for-byte unchanged until the feature is enabled.

Unlike the earlier rejected RFC 0021 (`all?`/`any?`), the predicate here is a
*general* non-nested predicate that refers to the set element through a reserved
keyword `it`, restricted so that it **contains no set term**. This set-free
restriction is exactly what makes the operators analyzable: non-nested bounded set
quantifiers are decidable when the predicate contains no set term (Mohamed et al. 2025,
see [Background](#background-rfc-0021-and-the-decidability-result)).

### Background: RFC 0021 and the decidability result

RFC 0021 ("Add basic `all?` and `any?` operators",
`/local/home/luxask/code/rfcs/archive/rfc/0021-any-and-all-operators.md`) was
accepted 2023-11-08 and then **rejected 2024-05-21**. It was rejected because even
its revised ("basic") form was **not analyzable**: making it analyzable would have
required further restrictions such as comparing set members to constants only, and
it was unclear the operators would remain useful under those restrictions.

RFC 0021 also described, as a rejected alternative, a **"Generalized" form** using an
`it` keyword and arbitrary non-nested predicates. The new design resembles that
generalized form, but is now made analyzable by a single clean restriction derived
from a decidability result: **non-nested bounded set quantifiers are decidable when
the predicate contains no set term.** That is why `PredExpr` below is defined to be
set-free. The analyzability claim is sourced to:

> Mudathir Mohamed, Nick Feng, Clark Barrett, Cesare Tinelli, Andrew Reynolds,
> Marsha Chechik (2025). *Solving Set Constraints with Comprehensions and Bounded
> Quantifiers.* Formal Methods in Computer-Aided Design (FMCAD) 2025.
> [PDF](https://repositum.tuwien.at/bitstream/20.500.12708/219545/1/Mohamed%20Mudathir%20-%202025%20-%20Solving%20Set%20Constraints%20with%20Comprehensions%20and...pdf)
>
> The decidable fragment is characterized by that paper's **Condition 1**: *no
> predicate passed to the filter operator σ may include set terms (terms of sort
> `Set(τ)`)*, together with a decidable element theory (Conditions 2–3). Cedar's
> set-free `PredExpr` is exactly Condition 1.

The new design also **carries over RFC 0021's chosen error semantics**: a single
deterministic, iteration-order-independent `QuantifierError` (see requirement 2.x),
not first-error-wins and not errors-as-false.

---

## User stories

- **US-1 (policy author).** As a policy author, I want to write
  `resource.ports.all(it >= 8000)` so that I can require every element of a set to
  satisfy a comparison without manually expanding a conjunction, which is impossible
  for non-literal sets like `context.portNumbers`.
- **US-2 (policy author).** As a policy author, I want `resource.tags.any(it like "private*")`
  so that I can test existential conditions over a set.
- **US-3 (policy author).** As a policy author, I want deterministic behavior when a
  predicate errors on some element, so that the same policy and input always yield the
  same result regardless of set iteration order.
- **US-4 (integrator).** As someone embedding Cedar, I want the operators behind an
  `anyall` feature flag so that builds that do not opt in are completely unaffected.
- **US-5 (verification engineer).** As a verification engineer, I want the operators to
  be analyzable by the symbolic compiler whenever the predicate contains no set term, so
  that `is_authorized` reasoning (equivalence, always-allows, etc.) still terminates.
- **US-6 (tooling author).** As a tooling author, I want `.any`/`.all` policies to
  round-trip losslessly through the policy string / EST / AST / protobuf representations,
  so that existing format-conversion tooling keeps working.

---

## Acceptance criteria (EARS)

Criteria use EARS "WHEN/THEN/SHALL" phrasing. "The parser", "the evaluator", "the
validator", and "the symbolic compiler" refer to the Rust `cedar-policy-core` surface
and its Lean `Cedar/Spec` + `Cedar/SymCC` counterparts unless stated.

### 1. Syntax

1.1 WHEN the `anyall` feature is enabled AND a policy contains `E.all(P)` or `E.any(P)`
where `E` is an expression and `P` is a predicate, THEN the parser SHALL accept it and
produce an `ExprKind::All` node — directly for `.all`, and for `.any` via the builder's
`!E.all(!P)` lowering (there is no `ExprKind::Any`; see design).

1.2 WHEN a predicate `P` refers to the current set element, THEN the author SHALL write
the element as the reserved keyword `it`, and the parser SHALL bind `it` to that element.

1.3 WHEN the `anyall` feature is NOT enabled, THEN the parser SHALL reject `.all(` /
`.any(` and SHALL treat `it` as an ordinary identifier exactly as today (no behavior
change in the default build).

1.4 Nested `.all` / `.any` SHALL be **structurally impossible** in every typed tree: a
quantifier's predicate has type `PredExpr` (AST / Lean) or `PredExprNoExt` (EST), which has no
quantifier variant and no full-`Expr` child, so a nested quantifier cannot be constructed —
this is enforced by the type, not a runtime check. WHEN nested quantifiers appear in the
*untyped* surface syntax (PST / CST), THEN the PST→AST conversion SHALL reject them (the first
layer at which the typed `PredExpr` exists). Nested quantifiers are disallowed for performance
and analyzability.

1.5 WHEN a predicate `P` contains a set term — a set literal, or any sub-expression whose
value type is Set (including `it` used where `it` is itself a set, and the set operators
`contains` / `containsAll` / `containsAny`) — THEN the policy SHALL be rejected by the
validator (and flagged by the parser-time well-formedness check where statically
detectable), because set-free predicates are the analyzable fragment.

1.6 WHEN `it` appears outside any `.all` / `.any` predicate, THEN the parser SHALL reject
it as a use of a reserved keyword in an invalid position.

### 2. Evaluation semantics

2.1 WHEN `E.all(P)` is evaluated AND `E` evaluates to a set `s` AND `P[it := e]` evaluates
to `true` for every `e` in `s` (no errors), THEN the result SHALL be `true`.

2.2 WHEN `E.all(P)` is evaluated AND `P[it := e]` evaluates to `false` for at least one
`e` in `s` (and no element errors), THEN the result SHALL be `false`.

2.3 WHEN `E.any(P)` is evaluated, THEN it SHALL evaluate exactly as `!E.all(!P)` (the
`any` form lowers to the `all` form, see design), so `E.any(P)` is `true` iff `P[it := e]`
is `true` for some `e`.

2.4 WHEN `E` does not evaluate to a set, THEN evaluation SHALL yield a type error (the
existing `Error.typeError` / Rust evaluation type error), identical to how `contains`
reports a non-set receiver.

2.5 (QuantifierError — carried from RFC 0021.) WHEN `E.all(P)` is evaluated AND evaluating
`P[it := e]` would error for at least one element `e` of `s`, THEN the whole expression
SHALL yield a single deterministic `QuantifierError`, regardless of iteration order, and
regardless of whether some other element evaluates to `false`. The result SHALL NOT depend
on which erroring element is encountered first, SHALL NOT be the element-specific error,
and SHALL NOT be "errors treated as false".

2.6 WHEN `QuantifierError` carries diagnostic information, THEN that information SHALL be
bounded in size and computed deterministically (e.g. derived from the smallest erroring
element under the existing total order `Value.lt`), so evaluator output size stays constant
in policy and input size.

2.7 WHEN `s` is empty, THEN `E.all(P)` SHALL be `true` and `E.any(P)` SHALL be `false`
(vacuous truth / vacuous falsity), with no QuantifierError.

### 3. `anyall` feature gate

3.1 WHEN the Rust crates are built WITHOUT the `anyall` feature, THEN the AST, parser,
evaluator, validator, EST, protobuf, and public API SHALL be identical to the pre-feature
build (no new enum variants reachable, no grammar change).

3.2 WHEN the Lean project is built WITHOUT the corresponding build flag, THEN
`lake build Cedar` SHALL build the spec and all proofs with no `.all` / `PredExpr`
constructs present.

3.3 WHEN the feature is enabled on exactly one surface but not the others, THEN the DRT
differential harness SHALL NOT generate `.all` / `.any` AST nodes (the generator arm is
gated on the same flag), so the Rust engine and the Lean definitional engine are compared
only on a shared, mutually-supported language fragment.

### 4. Roundtrip

4.1 WHEN a policy containing `.all` / `.any` is converted AST → policy string → AST, THEN
the result SHALL be shape-equal to the original (lossless), analogous to how `e1 >= e2` is
represented and printed via `!(e1 < e2)`.

4.2 WHEN a policy containing `.all` / `.any` is converted through EST (JSON) and back, and
through protobuf and back, THEN the result SHALL round-trip losslessly.

4.3 WHEN `.any(P)` is lowered (by `ExprBuilder::any` to `!.all(!P)`, at the same layer as
`>`/`>=` — NOT in the parser) and pretty-printed, THEN the printed form SHALL be a valid
policy that re-parses to a shape-equal AST (surface-form stability is a design choice
recorded in design.md, not a hard requirement if lowering is lossy).

### 5. Analyzability

5.1 WHEN the `anyall` feature is enabled AND the symbolic compiler compiles `E.all(P)`
where `P` contains no set term, THEN compilation SHALL succeed and produce a term the SMT
solver can decide (per Mohamed et al. 2025).

5.2 WHEN the predicate `P` contains a set term, THEN the symbolic compiler SHALL reject it
(the validator already rejects such policies per 1.5; the compiler SHALL additionally
refuse rather than emit an undecidable encoding).

5.3 WHEN the symbolic compiler and the concrete evaluator both run on the same `.all` / `.any`
policy, THEN the `symcc-*` DRT targets SHALL confirm they agree (no counterexample where
analysis and evaluation disagree).

---

## Open questions / unresolved TODOs

- **OQ-1 (sets of sets).** **RESOLVED (negatively) by Mohamed et al. 2025.** Decidability of
  `.all` / `.any` over **sets of sets** is NOT available in general. If the element `it` were
  itself a set, the filter predicate would mention a set term, violating the paper's
  **Condition 1** ("no predicate passed to the filter operator may include set terms"); the
  paper proves (§III-D) that dropping Condition 1 makes satisfiability **undecidable** (by
  reduction from Hilbert's Tenth Problem). Therefore sets-of-sets predicates are **out of
  scope by design, not merely deferred** — the set-free `PredExpr` restriction already
  excludes them, and that exclusion is load-bearing for analyzability.
  - *Nuance:* the paper shows nested **all-universal** quantifiers can be rewritten via the
    cross-product `s₁ × … × sₙ` into a single `set.all` over tuples, which IS decidable. This
    is about nesting of quantifiers, NOT about a set-valued element inside one predicate, and
    is not needed for Cedar's single non-nested `.all`/`.any`. Nested **alternating** (∀∃)
    quantifiers remain undecidable. Our "no nested quantifiers" rule (req 1.4) stays.
- ~~OQ-2 (decidability citation).~~ **RESOLVED.** The analyzability claim is sourced to
  Mohamed et al. (2025), FMCAD (link above). No longer a TODO.

_No open TODOs remain. Both reference links are resolved and the sets-of-sets question is
answered._
