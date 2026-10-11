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
Predicate analogue of `TypeOfIsSound`, WEAK form (D-94). A well-typed predicate
(under `it : itTy`, with the element value `it` an instance of `itTy`) evaluates
to a value of the returned type or to some error. There is NO guarded-capabilities
conclusion and NO capability-invariant hypothesis (D-P9c-5 (c)).
-/
def TypeOfPredIsSound (p : PredExpr) : Prop :=
  ∀ {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities} {env : TypeEnv}
    {ty : TypedExpr} {request : Request} {entities : Entities},
    InstanceOfWellFormedEnvironment request entities env →
    InstanceOfType env it itTy →
    typeOfPred p itTy c₁ env = Except.ok (ty, c₂) →
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
    ∃ v, EvaluatesToPred .item it request entities v ∧ InstanceOfType env v ty.typeOf := by
  simp only [typeOfPred, Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h₃
  obtain ⟨hty, hc⟩ := h₃
  subst hc; subst hty
  refine ⟨it, ?_, ?_⟩
  · exact Or.inr (by simp only [evaluatePred])
  · show InstanceOfType env it (TypedExpr.var Var.principal itTy).typeOf
    simp only [TypedExpr.typeOf]
    exact hit

/-- `.lit`: value typing coincides with the expression `.lit` soundness. -/
theorem type_of_pred_lit_is_sound {l : Prim} {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₃ : typeOfPred (.lit l) itTy c₁ env = Except.ok (ty, c₂)) :
    ∃ v, EvaluatesToPred (.lit l) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have hexpr : typeOf (Expr.lit l) c₁ env = Except.ok (ty, c₂) := by
    simpa only [typeOf, typeOfPred] using h₃
  have ⟨_, v, hev, hinst⟩ := type_of_lit_is_sound (request := request) (entities := entities) hexpr
  refine ⟨v, ?_, hinst⟩
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
    ∃ v, EvaluatesToPred (.var vr) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have hexpr : typeOf (Expr.var vr) c₁ env = Except.ok (ty, c₂) := by
    simpa only [typeOf, typeOfPred] using h₃
  have ⟨_, v, hev, hinst⟩ := type_of_var_is_sound h₂ hexpr
  refine ⟨v, ?_, hinst⟩
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
