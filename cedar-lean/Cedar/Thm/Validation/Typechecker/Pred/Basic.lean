/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Typechecker.LitVar

/-!
# Predicate type soundness — foundation (D-74 option A, Phase 9c, §5.1/§5.2)

This file states the predicate analogue of `type_of_is_sound`
(`Thm/Validation/Typechecker.lean`) over `PredExpr`/`evaluatePred`/`typeOfPred`,
with the quantifier element keyword `it` (`PredExpr.item`) bound to a value `it`
that is an instance of its static element type `itTy`.

**WEAK soundness (D-94 / D-P9c-5 resolved option (c)).** The statement admits
*any* error on the error side and carries **no** capability invariant: a
well-typed predicate, evaluated with the element bound to a value of its static
type, either errors (with any error) or yields a value that is an instance of the
returned type. This is deliberately weaker than the expression `type_of_is_sound`
(which rules out `attrDoesNotExist`/`typeError` via a capability invariant): the
capability invariant cannot be threaded soundly through a predicate because
`itExpr := .var .principal` and `typeOfAll` passes the OUTER capabilities into
`typeOfPred`, so an `it`-dependent attribute capability would be keyed by
`principal` (D-95, an OPEN Lean-spec precision/parity follow-up). Weak soundness
is all every downstream D-74-A consumer needs — `normalize_evaluatePred` only
needs "a `.bool .ff`-typed sub-predicate evaluates to `false` or errors (never
`true`)", which the any-error form delivers via `instance_of_ff_is_false`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Predicate analogue of `EvaluatesTo`, WEAK form (D-94): evaluating `p` with the
element bound to `it` yields the value `v`, or **any** error. No restriction to
the three validation-time errors — a predicate may legitimately raise
`attrDoesNotExist` (hence `quantifierError` at the quantifier), which the
capability invariant would have ruled out for expressions but which we do not
track for predicates.
-/
def EvaluatesToPred (p : PredExpr) (it : Value) (request : Request) (entities : Entities) (v : Value) : Prop :=
  (∃ err, evaluatePred p it request entities = .error err) ∨
  evaluatePred p it request entities = .ok v

/--
Predicate analogue of `CapabilitiesInvariant` (D-97 option b). A capability
`(e, k) ∈ c` is interpreted against the `it`-bound predicate evaluation: for the
unique predicate `q` whose `toCapKey` is `e` (keys are `toCapKey` images, D-97),
the attribute/tag fact holds of `evaluatePred q it`. Quantifying over all `q`
with `q.toCapKey = e` mirrors the Expr invariant without needing an inverse of
`toCapKey`; at the attr/tag arms the relevant `q` is the operand sub-predicate,
whose `toCapKey` is exactly the key `typeOfHasAttr`/`typeOfHasTag` consulted.
-/
def CapabilitiesInvariantPred (c : Capabilities) (it : Value) (request : Request) (entities : Entities) : Prop :=
  (∀ (e : Expr) (k : Attr), (e, .attr k) ∈ c →
    ∀ q : PredExpr, q.toCapKey = e → EvaluatesToPred (.hasAttr q k) it request entities true) ∧
  (∀ (e k : Expr), (e, .tag k) ∈ c →
    ∀ q r : PredExpr, q.toCapKey = e → r.toCapKey = k →
      EvaluatesToPred (.binaryApp .hasTag q r) it request entities true)

/-- The empty capability set trivially satisfies the predicate invariant. -/
theorem empty_capabilities_invariant_pred (it : Value) (request : Request) (entities : Entities) :
    CapabilitiesInvariantPred ∅ it request entities := by
  constructor <;> intro e k h <;> contradiction

/-- Union of two predicate-invariant capability sets is predicate-invariant (pred twin of `capability_union_invariant`). -/
theorem capability_union_invariant_pred {c₁ c₂ : Capabilities} {it : Value}
    {request : Request} {entities : Entities}
    (h₁ : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : CapabilitiesInvariantPred c₂ it request entities) :
    CapabilitiesInvariantPred (c₁ ∪ c₂) it request entities := by
  simp only [CapabilitiesInvariantPred, List.mem_union_iff] at *
  constructor
  case left =>
    intro e k h₃ q hq
    rcases h₃ with h₃ | h₃
    · exact h₁.left e k h₃ q hq
    · exact h₂.left e k h₃ q hq
  case right =>
    intro e k h₃ q r hq hr
    rcases h₃ with h₃ | h₃
    · exact h₁.right e k h₃ q r hq hr
    · exact h₂.right e k h₃ q r hq hr

/--
Predicate analogue of `GuardedCapabilitiesInvariant`: the output capabilities
satisfy `CapabilitiesInvariantPred` provided the predicate evaluates to `true`.
-/
def GuardedCapabilitiesInvariantPred (p : PredExpr) (c : Capabilities) (it : Value)
    (request : Request) (entities : Entities) : Prop :=
  evaluatePred p it request entities = .ok true → CapabilitiesInvariantPred c it request entities

theorem empty_guarded_capabilities_invariant_pred {p : PredExpr} {it : Value}
    {request : Request} {entities : Entities} :
    GuardedCapabilitiesInvariantPred p ∅ it request entities := by
  intro _; exact empty_capabilities_invariant_pred it request entities

/--
Predicate analogue of `TypeOfIsSound` (D-97 option b). The true mirror: it takes
`CapabilitiesInvariantPred c₁ it …`, and concludes the guarded production of
`CapabilitiesInvariantPred c₂` AND that evaluation yields a value of the returned
type or (D-94) **any** error.
-/
def TypeOfPredIsSound (p : PredExpr) : Prop :=
  ∀ {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities} {env : TypeEnv}
    {ty : TypedExpr} {request : Request} {entities : Entities},
    CapabilitiesInvariantPred c₁ it request entities →
    InstanceOfWellFormedEnvironment request entities env →
    InstanceOfType env it itTy →
    typeOfPred p itTy c₁ env = Except.ok (ty, c₂) →
    GuardedCapabilitiesInvariantPred p c₂ it request entities ∧
    ∃ v, EvaluatesToPred p it request entities v ∧ InstanceOfType env v ty.typeOf

/-- An error on the left of `EvaluatesToPred` for any witness `v`. -/
theorem EvaluatesToPred.error {p : PredExpr} {it : Value} {request : Request} {entities : Entities}
    {err : Error} {v : Value}
    (h : evaluatePred p it request entities = .error err) :
    EvaluatesToPred p it request entities v :=
  Or.inl ⟨err, h⟩

/-! ### Trivial arms: `.item`, `.lit`, `.var`. -/

/--
`.item`: `typeOfPred .item itTy = ok (.var .principal itTy)` and
`evaluatePred .item it = .ok it`. The result type is `itTy`, closed directly by
the `InstanceOfType env it itTy` hypothesis.
-/
theorem type_of_pred_item_is_sound {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred .item itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariantPred .item c₂ it request entities ∧
    ∃ v, EvaluatesToPred .item it request entities v ∧ InstanceOfType env v ty.typeOf := by
  simp only [typeOfPred, Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h₃
  obtain ⟨hty, hc⟩ := h₃
  subst hc; subst hty
  refine ⟨empty_guarded_capabilities_invariant_pred, it, ?_, ?_⟩
  · exact Or.inr (by simp only [evaluatePred])
  · show InstanceOfType env it (TypedExpr.var Var.principal itTy).typeOf
    simp only [TypedExpr.typeOf]
    exact hit

/-- `.lit`: value typing coincides with the expression `.lit` soundness. -/
theorem type_of_pred_lit_is_sound {l : Prim} {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₃ : typeOfPred (.lit l) itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariantPred (.lit l) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.lit l) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have hc : c₂ = ∅ := by
    simp only [typeOfPred, typeOfLit] at h₃
    split at h₃ <;> (try split at h₃) <;> simp_all [Validation.ok, Validation.err]
  subst hc
  have hexpr : typeOf (Expr.lit l) c₁ env = Except.ok (ty, ∅) := by
    simpa only [typeOf, typeOfPred] using h₃
  have ⟨_, v, hev, hinst⟩ := type_of_lit_is_sound (request := request) (entities := entities) hexpr
  refine ⟨empty_guarded_capabilities_invariant_pred, v, ?_, hinst⟩
  simp only [EvaluatesTo, evaluate] at hev
  simp only [EvaluatesToPred, evaluatePred]
  rcases hev with hev | hev | hev | hev | hev
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact absurd hev (by simp)
  · exact Or.inr hev

/-- `.var`: value typing coincides with the expression `.var` soundness. -/
theorem type_of_pred_var_is_sound {vr : Var} {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (h₃ : typeOfPred (.var vr) itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariantPred (.var vr) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.var vr) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have hc : c₂ = ∅ := by
    simp only [typeOfPred, typeOfVar] at h₃
    cases vr <;> simp_all [Validation.ok]
  subst hc
  have hexpr : typeOf (Expr.var vr) c₁ env = Except.ok (ty, ∅) := by
    simpa only [typeOf, typeOfPred] using h₃
  have ⟨_, v, hev, hinst⟩ := type_of_var_is_sound h₂ hexpr
  refine ⟨empty_guarded_capabilities_invariant_pred, v, ?_, hinst⟩
  have heval : evaluatePred (.var vr) it request entities = evaluate (.var vr) request entities := by
    cases vr <;> simp only [evaluatePred, evaluate]
  simp only [EvaluatesToPred, heval]
  simp only [EvaluatesTo] at hev
  rcases hev with hev | hev | hev | hev | hev
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inr hev

end Cedar.Thm
