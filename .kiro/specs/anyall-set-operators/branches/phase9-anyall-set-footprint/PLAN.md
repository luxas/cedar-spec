# Phase 9 — Enforcer set-footprint extension (D-70 option B)

Status: PLANNED-LATER (not in the current branch stack). Placed by the user at Phase 9, after
Phase 8 benchmarks. Follow-up to D-70, whose option A shipped in Phase 5B.

## Scope

Phase 5B (D-70 option A) keeps the `.all` quantifier footprint `it`-free: `compile` rejects a `.all`
predicate that applies `in` (Cedar's `in` / the ancestors uninterpreted function) to a left operand
that depends on the bound element `it` (a `typeError`, mirroring the D-65 Bool-type guard), and
`footprint (.all x₁ p) = footprint x₁ ∪ footprintPred p` collects only the entity-typed compiled
terms of the `it`-free subexpressions of the predicate. This is sound because `SameOn` grants
attribute/tag/request agreement unconditionally and ancestor agreement only at the UIDs named by
finitely many footprint Terms — and a symbolic receiver's element UIDs cannot be named by finitely
many Terms, so an `it`-dependent `in` has no groundable footprint under A.

Phase 9 removes that restriction. It extends the Enforcer so the footprint may contain a SET-TYPED
entry — the compiled receiver set itself — and grounds the hierarchy well-formedness assumptions
(acyclicity, transitivity) over that set via SMT `set.filter`, rather than only over the finite set of
named entity Terms. `SymEntities.SameOn` / `SymEnv.SameOn` are extended correspondingly so that ancestor
agreement is granted over the elements of a footprint set entry (via the same `set.filter` the
grounding uses), which is what lets a predicate's `it`-dependent `in` be sound.

Grounding shape (to be designed/validated):
- acyclicity of a set entry S: one `set.filter` over S asserting no element is its own ancestor;
- element-vs-footprint-term transitivity (an element of S vs a named footprint Term): one `set.filter`
  over S;
- element-vs-element transitivity (two elements of the SAME S): a `set.filter` NESTED over S.

## The open decidability question (must be settled before committing an encoding)

The element-vs-element transitivity constraint is a `set.filter` whose body itself quantifies over the
same set S (a nested filter / quantifier). It is NOT established that cvc5's finite-sets + `ALL`
fragment (the logic Phase 5 measured decidable for the single-level `set.all` encoding, D-34) remains
decidable — or tractable — under this nested-`set.filter` form. Phase 9 must first determine whether
the nested constraint stays in a decidable fragment (and, empirically via the Phase 8 harness, whether
cvc5 solves it at useful set sizes); if not, the encoding must be reshaped (e.g. a bounded unrolling to
the receiver's cardinality when it is a literal set, or a different transitivity formulation) before any
Lean-side `SameOn`/`enforce` change is made. Only after the encoding is fixed do the Lean changes
(footprint set entries, `SameOn` extension, the `compile_interpret_on_footprint` `.all` case without the
A guard, and the matching Rust `cedar-policy-symcc` grounding for the DRT differential) follow.

B would replace Phase 5B's A guard commit only; everything else in Phase 5B is independent of this choice.
