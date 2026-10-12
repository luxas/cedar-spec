# cedar-docs hand-off — `.all` / `.any` set quantifiers

The policy-author LANGUAGE reference for Cedar lives on the public documentation website
[docs.cedarpolicy.com](https://docs.cedarpolicy.com), whose source is the separate
[`cedar-policy/cedar-docs`](https://github.com/cedar-policy/cedar-docs) repository — **not** in
`cedar` or `cedar-spec`. When `.all` / `.any` graduate from experimental, the website needs the
content below. The paste-ready draft is `./language-reference-anyall.md` in this directory.

## Target cedar-docs pages

- **Policy syntax → Operators and functions** (the operator reference): add `.all(..)` and
  `.any(..)` with the keyword `it`, next to `contains` / `containsAll` / `containsAny`. Source:
  the "Syntax", "The keyword `it`", and "Evaluation semantics" sections of the draft.
- **Policy syntax → the grammar page**: add the `.all` / `.any` access-form production and note
  `it` as a context-sensitive keyword (ordinary identifier outside a predicate).
- **Validation / typing reference**: add the `Set<τ>` + `Bool`-under-`it:τ` type rule. Source:
  the "Validation (typing)" section.
- **Analysis (Cedar symbolic analysis) docs**: add the set-free decidability note and the FMCAD
  2025 citation. Source: the "Analyzability" section (including the experimental caveat).
- **A "what's experimental" / release-notes page**: note the `anyall` feature gate and that the
  operators are off by default until graduation.

## What must be carried verbatim

- The element keyword is `it`.
- The set-free + non-nested restriction (no set literals, no
  `contains`/`containsAll`/`containsAny`/`isEmpty`, no nested `.all`/`.any`).
- The deterministic `QuantifierError` and the no-short-circuit-on-`false` rule.
- Empty-set results: `.all` ⇒ `true`, `.any` ⇒ `false`.
- The FMCAD 2025 analyzability citation (Mohamed et al.).

## Not for the website

The exact Rust/Lean error-message strings, feature-flag build commands, and DRT settings in the
in-repo docs are implementation detail; the website should describe the behavior, not the API.
