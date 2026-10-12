# D-70 option B decidability probe (raw cvc5 1.4.1, `HO_ALL`)

Plan-level evidence for Phase 9 that the Enforcer set-typed footprint grounding (D-70 B) is
encodable: the open question was whether **element-vs-element transitivity** — a `set.filter`
whose body quantifies over the *same* set via an inner `set.filter` — stays decidable (returns
`sat`/`unsat`, not `unknown`) in cvc5's finite-sets + `HO_ALL` fragment.

Entities are an abstract sort `E`; the ancestors UF is `anc : E -> (Set E)` (the `declare-fun`
shape the encoder emits for the ancestors `uuf`); the receiver is a symbolic `(Set E)`.

Reproduce: `cvc5 --tlimit=60000 <file>`.

| File | Shape | Expected | Result | Wall |
|---|---|---|---|---|
| `p1_single_filter.smt2` | acyclicity + element-vs-named-term transitivity (single-level filter) | sat | **sat** | 4.8 ms |
| `p2_nested_filter.smt2` | element-vs-element transitivity (NESTED filter over the same S) | sat | **sat** | 4.6 ms |
| `p3_nested_unsat.smt2` | nested transitivity + acyclicity + a forced 2-cycle | unsat | **unsat** | 5.1 ms |
| `p4_pinned5_sat.smt2` | nested transitivity over a 5-member membership-constrained set | sat | **sat** | 10.0 ms |
| `p5_3cycle_unsat.smt2` | nested transitivity + acyclicity + a forced 3-cycle | unsat | **unsat** | 6.1 ms |

**Verdict: GO.** cvc5 1.4.1 decides every instance — the nested filter in both polarities, 2- and
3-cycle UNSAT — in single-digit ms, no `unknown`. The nested-filter transitivity constraint is in
the decidable `HO_ALL`/finite-sets fragment, so D-70 B needs no reshaping. See PLAN.md §4 for the
fallbacks held in reserve and the Phase-8-harness tractability check required before the Lean
`SameOn` change.
