# `.all` / `.any` — non-nested set quantifiers (experimental)

> **Experimental.** These operators are gated behind the off-by-default `anyall` Cargo feature
> (included in the `experimental` meta-feature). The default Cedar build does not include them,
> and they are subject to change. Enable with `--features anyall` (or `--features experimental`).

Cedar's `.all` and `.any` operators test whether a predicate holds for **every** element (or
**some** element) of a set, without manually expanding a conjunction or disjunction — which is
impossible for non-literal sets such as `context.portNumbers`.

```cedar
permit(principal, action, resource)
when { resource.ports.all(it >= 8000) };

permit(principal, action, resource)
when { resource.tags.any(it like "private*") };
```

## Syntax

- `E.all(P)` — true iff the predicate `P` holds for every element of the set `E`.
- `E.any(P)` — true iff `P` holds for some element of `E`.
- Inside the predicate, the current element is written as the keyword **`it`**:
  `resource.owners.all(it.department == "eng")`.

`E` is any expression that evaluates to a set. `P` is a **predicate** (see restrictions below).

## The keyword `it`

`it` denotes the current set element while a predicate is being evaluated. It is only
meaningful **inside** an `.all(..)` / `.any(..)` predicate. Using `it` anywhere else is a parse
error:

```text
`it` can only be used inside the predicate of `.all(..)` or `.any(..)`
```

Outside the `anyall` feature, `it` is an ordinary identifier with no special meaning (the
default build is unchanged). Attribute/field uses such as `principal.it`, `{it: 1}`, and
`resource has it` continue to work as before.

## Restriction: predicates must be set-free and non-nested

A predicate `P` may use `it`, the request variables (`principal`, `action`, `resource`,
`context`), literals, attribute/tag access, comparisons, boolean connectives, `like`, `is`,
`in`, and extension functions. It **may not** contain:

- a **set literal** or any sub-expression whose value is a set (including `it` where `it` is
  itself a set);
- the **set operators** `contains`, `containsAll`, `containsAny`, or `isEmpty`;
- a **nested** `.all` / `.any`.

This "set-free, non-nested" restriction is what makes `.all` / `.any` **analyzable** (see
Analyzability below); it is not an incidental limitation.

A predicate that violates the restriction is rejected. At parse time:

```text
invalid `.all`/`.any` predicate: <detail>
```

with the help text:

```text
a predicate may use `it`, request variables, literals and non-set operators, but no set literals, set operators, or nested `.all`/`.any`
```

A set-**typed** predicate expression that is only caught by typing is rejected by the validator:

```text
for policy `<id>`, the predicate of a set quantifier contains a set-typed expression
```

with the help text:

```text
`.all`/`.any` predicates may not use set values, set literals, or set operators
```

## Evaluation semantics

- **Empty set.** `E.all(P)` on an empty set is `true` (vacuous truth); `E.any(P)` is `false`
  (vacuous falsity).
- **Non-set receiver.** If `E` does not evaluate to a set, evaluation is a type error, exactly
  as `contains` reports a non-set receiver.
- **Deterministic error (`QuantifierError`).** If evaluating `P` on **any** element would error
  (or produce a non-boolean), the whole quantifier evaluates to a single, deterministic,
  iteration-order-independent error:

  ```text
  the predicate of a set quantifier errored on at least one element
  ```

  This holds even if another element already makes the quantifier `false` — an error on any
  element outranks a `false` on another. The error is **not** first-error-wins and **not**
  errors-as-false; it is defined by the quantifier's expansion to a conjunction/disjunction,
  which errors if any conjunct/disjunct errors.
- **No short-circuit on `false`.** Because a later element may still error, `.all` does not stop
  at the first `false` element; it scans every element to detect a possible error (and `.any`,
  by the lowering below, does not stop at the first `true`). Evaluation is therefore O(n) in the
  set size with no best-case short-circuit. (It may exit early on the first *error*, since an
  error is already the final result.)

`E.any(P)` is defined as `!E.all(!P)` and shares `.all`'s semantics exactly.

## Validation (typing)

If `E` has type `Set<τ>` and the predicate `P` typechecks to `Bool` with `it : τ`, then
`E.all(P)` (equivalently `E.any(P)`) typechecks to `Bool`. If `E` is not a set, or `P` is not
`Bool` under `it : τ`, the policy is rejected with a type error. Unknown element types follow
Cedar's existing treatment of set element types (the same as `contains` / `containsAll`).

## Analyzability

`.all` / `.any` are analyzable by Cedar's symbolic compiler **iff the predicate contains no set
term** — exactly the set-free restriction above. This is the decidable fragment identified by:

> Mudathir Mohamed, Nick Feng, Clark Barrett, Cesare Tinelli, Andrew Reynolds, Marsha Chechik
> (2025). *Solving Set Constraints with Comprehensions and Bounded Quantifiers.* Formal Methods
> in Computer-Aided Design (FMCAD) 2025.

The set-free predicate is that paper's **Condition 1** ("no predicate passed to the filter
operator may include set terms"). A set-valued predicate (e.g. a set-of-sets element) is
**undecidable** and is excluded by design — the symbolic compiler rejects it rather than
emitting an undecidable encoding.

> **Caveat (experimental, current state).** The symbolic compiler's *soundness* on `.all` is
> proven, and `.all` policies compile, interpret, and evaluate symbolically. One analysis
> restriction and one proof item are open: (1) a predicate whose `in` has an element-dependent
> left operand is currently **unsupported** by the symbolic compiler (rejected), pending a
> set-typed-footprint extension; and (2) the "every well-typed policy compiles" completeness
> property is not yet established for `.all`. Concrete evaluation and validation are unaffected.

## Enabling the feature

Per crate:

- `cedar-policy` / `cedar-policy-core`: build with `--features anyall` (or
  `--features experimental`, which includes it).
- `cedar-policy-symcc`: build with `--features anyall` for symbolic analysis of `.all` / `.any`.
- Differential testing (`cedar-drt`): build with `--features anyall`; generation is also
  controlled by `ABACSettings::enable_anyall`.
