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

The predicate world differs from the expression world in exactly two places
(D-P9c-2, D-P9c-3):

* **`EvaluatesToPred`** carries the SAME THREE allowed errors as `EvaluatesTo`
  (`entityDoesNotExist` / `extensionError` / `arithBoundsError`) — there is no
  `quantifierError` disjunct, because `evaluatePred` can never produce
  `quantifierError` (it is introduced only by `evalAll`; the `*_ne_qerr` lemmas
  in `Typechecker/All.lean` certify every primitive the predicate can call).
* The capability invariant is **not** predicate-indexed: the ordinary
  `CapabilitiesInvariant c request entities` is reused unchanged, and the only
  new hypothesis is `InstanceOfType env it itTy` (the bound element is an
  instance of its static type). `it` resolves to a value directly
  (`evaluatePred .item it = .ok it`) and establishes/consumes no capability
  about the request or entity store.

Capabilities are keyed by `Expr`, and `typeOfPred` already threads `x₁.toExpr`
through the per-operator helpers, so `GuardedCapabilitiesInvariant` is stated
over `p.toExpr`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Predicate analogue of `EvaluatesTo`: evaluating a predicate `p` with the element
keyword bound to `it` yields the value `v`, or one of the three validation-time
allowed errors. There is deliberately no `quantifierError` disjunct
(`evaluatePred` never produces it; §5.1).
-/
def EvaluatesToPred (p : PredExpr) (it : Value) (request : Request) (entities : Entities) (v : Value) : Prop :=
  evaluatePred p it request entities = .error .entityDoesNotExist ∨
  evaluatePred p it request entities = .error .extensionError ∨
  evaluatePred p it request entities = .error .arithBoundsError ∨
  evaluatePred p it request entities = .ok v

/--
Predicate analogue of `TypeOfIsSound`. A well-typed predicate (under `it : itTy`,
with the element value `it` an instance of `itTy`) evaluates to a value of the
returned type or to an allowed error, and its output capabilities satisfy the
guarded invariant over the predicate's `Expr` reconstruction.
-/
def TypeOfPredIsSound (p : PredExpr) : Prop :=
  ∀ {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities} {env : TypeEnv}
    {ty : TypedExpr} {request : Request} {entities : Entities},
    CapabilitiesInvariant c₁ request entities →
    InstanceOfWellFormedEnvironment request entities env →
    InstanceOfType env it itTy →
    typeOfPred p itTy c₁ env = Except.ok (ty, c₂) →
    GuardedCapabilitiesInvariant p.toExpr c₂ request entities ∧
    ∃ v, EvaluatesToPred p it request entities v ∧ InstanceOfType env v ty.typeOf

/-! ### Trivial arms: `.item`, `.lit`, `.var`. -/

/--
`.item`: `typeOfPred .item itTy = ok (.var .principal itTy)` and
`evaluatePred .item it = .ok it`. The result type is `itTy`, closed directly by
the `InstanceOfType env it itTy` hypothesis. `(.item).toExpr = itExpr =
.var .principal`, whose capabilities are empty.
-/
theorem type_of_pred_item_is_sound {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred .item itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariant (PredExpr.item).toExpr c₂ request entities ∧
    ∃ v, EvaluatesToPred .item it request entities v ∧ InstanceOfType env v ty.typeOf := by
  simp only [typeOfPred, Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h₃
  obtain ⟨hty, hc⟩ := h₃
  subst hc; subst hty
  refine ⟨empty_guarded_capabilities_invariant, it, ?_, ?_⟩
  · show EvaluatesToPred .item it request entities it
    unfold EvaluatesToPred
    exact Or.inr (Or.inr (Or.inr (by simp only [evaluatePred])))
  · show InstanceOfType env it (TypedExpr.var Var.principal itTy).typeOf
    simp only [TypedExpr.typeOf]
    exact hit

/--
`.lit`: coincides with the expression `.lit` soundness via `PredExpr.toExpr`
(`(.lit l).toExpr = .lit l`, `evaluatePred (.lit l) = evaluate (.lit l)`,
`typeOfPred (.lit l) = typeOfLit l = typeOf (.lit l)`).
-/
theorem type_of_pred_lit_is_sound {l : Prim} {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₃ : typeOfPred (.lit l) itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariant (PredExpr.lit l).toExpr c₂ request entities ∧
    ∃ v, EvaluatesToPred (.lit l) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have hexpr : typeOf (Expr.lit l) c₁ env = Except.ok (ty, c₂) := by
    simpa only [typeOf, typeOfPred] using h₃
  have ⟨hg, v, hev, hinst⟩ := type_of_lit_is_sound (request := request) (entities := entities) hexpr
  refine ⟨by simpa only [PredExpr.toExpr] using hg, v, ?_, hinst⟩
  simp only [EvaluatesTo, evaluate] at hev
  simp only [EvaluatesToPred, evaluatePred]
  rcases hev with hev | hev | hev | hev | hev
  · exact Or.inl hev
  · exact Or.inr (Or.inl hev)
  · exact Or.inr (Or.inr (Or.inl hev))
  · exact absurd hev (by simp)
  · exact Or.inr (Or.inr (Or.inr hev))

/--
`.var`: coincides with the expression `.var` soundness. `(.var vr).toExpr =
.var vr`, and `evaluatePred (.var vr) = evaluate (.var vr)` (the request vars
resolve identically).
-/
theorem type_of_pred_var_is_sound {vr : Var} {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (h₃ : typeOfPred (.var vr) itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariant (PredExpr.var vr).toExpr c₂ request entities ∧
    ∃ v, EvaluatesToPred (.var vr) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have hexpr : typeOf (Expr.var vr) c₁ env = Except.ok (ty, c₂) := by
    simpa only [typeOf, typeOfPred] using h₃
  have ⟨hg, v, hev, hinst⟩ := type_of_var_is_sound h₂ hexpr
  refine ⟨by simpa only [PredExpr.toExpr] using hg, v, ?_, hinst⟩
  have heval : evaluatePred (.var vr) it request entities = evaluate (.var vr) request entities := by
    cases vr <;> simp only [evaluatePred, evaluate]
  simp only [EvaluatesToPred, heval]
  simp only [EvaluatesTo] at hev
  rcases hev with hev | hev | hev | hev | hev
  · exact Or.inl hev
  · exact Or.inr (Or.inl hev)
  · exact Or.inr (Or.inr (Or.inl hev))
  · exfalso; cases vr <;> simp only [evaluate] at hev <;> exact absurd hev (by simp)
  · exact Or.inr (Or.inr (Or.inr hev))

end Cedar.Thm
