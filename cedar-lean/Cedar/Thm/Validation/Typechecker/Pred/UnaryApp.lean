/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.UnaryApp

/-!
# Predicate type soundness — `.unaryApp` arm (Phase 9c, M2)

Mirror of `type_of_unaryApp_is_sound` (`Typechecker/UnaryApp.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`. `typeOfPred (.unaryApp op x₁)` peels to
`typeOfPred x₁` then the SAME `typeOfUnaryApp op ty₁` helper the expression
typechecker uses, and `evaluatePred (.unaryApp op x₁)` is `evaluatePred x₁ >>=
apply₁ op` — identical to `evaluate` modulo the sub-term evaluator. The output
capabilities are `∅` (so the guarded invariant is `empty_guarded_capabilities_invariant`),
and `(.unaryApp op x₁).toExpr = .unaryApp op x₁.toExpr`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Inversion of `typeOfPred (.unaryApp op x₁)` (pred twin of `type_of_unary_inversion`).
-/
theorem type_of_pred_unary_inversion {op : UnaryOp} {x₁ : PredExpr} {itTy : CedarType}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h₁ : typeOfPred (.unaryApp op x₁) itTy c₁ env = Except.ok (tx, c₂)) :
    c₂ = ∅ ∧
    ∃ tx₁ ty c₁',
      tx = .unaryApp op tx₁ ty ∧
      typeOfPred x₁ itTy c₁ env = Except.ok (tx₁, c₁') ∧
      match op with
      | .not => ∃ bty, ty = .bool bty.not ∧ tx₁.typeOf = .bool bty
      | .neg => tx₁.typeOf = .int ∧ ty = .int
      | .isEmpty => ty = .bool .anyBool ∧ ∃ ty₀, tx₁.typeOf = .set ty₀
      | .like _ => ty = .bool .anyBool ∧ tx₁.typeOf = .string
      | .is ety₀  => ∃ ety₁, ty = .bool (if ety₀ = ety₁ then .tt else .ff) ∧ tx₁.typeOf = .entity ety₁ := by
  simp only [typeOfPred] at h₁
  simp_do_let (typeOfPred x₁ itTy c₁ env) as h₂ at h₁
  rename_i res ; have ⟨ty₁, c₁'⟩ := res
  simp only [typeOfUnaryApp, Function.comp_apply] at h₁
  split at h₁ <;> try contradiction
  all_goals {
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₁
    replace ⟨ h₁, hc ⟩ := h₁
    simp only [hc, true_and]
    exists ty₁
    rename_i hty₁ _
    simp [h₁, hty₁]
  }

/--
`.unaryApp` predicate soundness (pred twin of `type_of_unaryApp_is_sound`). The
proof is a direct mirror of the five per-op expression lemmas; the shared
inversion + IH + eval-result case split carries over verbatim with
`typeOf→typeOfPred`, `evaluate→evaluatePred`, `EvaluatesTo→EvaluatesToPred`.
-/
theorem type_of_pred_unaryApp_is_sound {op₁ : UnaryOp} {x₁ : PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₁ : CapabilitiesInvariant c₁ request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.unaryApp op₁ x₁) itTy c₁ env = Except.ok (ty, c₂))
    (ih : TypeOfPredIsSound x₁) :
    GuardedCapabilitiesInvariant (PredExpr.unaryApp op₁ x₁).toExpr c₂ request entities ∧
    ∃ v, EvaluatesToPred (.unaryApp op₁ x₁) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have ⟨hc, tx₁, tyr, c₁', htx, h₄, hmatch⟩ := type_of_pred_unary_inversion h₃
  subst hc
  simp only [PredExpr.toExpr]
  refine ⟨empty_guarded_capabilities_invariant, ?_⟩
  -- IH on the operand
  have ⟨_, v₁, hev₁, hinst₁⟩ := ih h₁ h₂ hit h₄
  subst htx
  simp only [TypedExpr.typeOf]
  simp only [EvaluatesToPred] at hev₁
  cases op₁
  case not =>
    obtain ⟨bty, htyr, hbty⟩ := hmatch
    subst htyr; rw [hbty] at hinst₁
    simp only [EvaluatesToPred, evaluatePred] at hev₁ ⊢
    rcases hev₁ with hev₁ | hev₁ | hev₁ | hev₁ <;> simp [hev₁]
    case inr.inr.inr =>
      cases bty
      case anyBool =>
        have ⟨b, h₈⟩ := instance_of_anyBool_is_bool hinst₁; subst h₈
        simp [apply₁]; apply bool_is_instance_of_anyBool
      case tt =>
        have h₈ := instance_of_tt_is_true hinst₁; subst h₈
        simp [apply₁, BoolType.not]; exact false_is_instance_of_ff
      case ff =>
        have h₈ := instance_of_ff_is_false hinst₁; subst h₈
        simp [apply₁, BoolType.not]; exact true_is_instance_of_tt
    all_goals exact type_is_inhabited_bool
  case neg =>
    obtain ⟨hbty, htyr⟩ := hmatch
    subst htyr; rw [hbty] at hinst₁
    simp only [EvaluatesToPred, evaluatePred] at hev₁ ⊢
    rcases hev₁ with hev₁ | hev₁ | hev₁ | hev₁ <;> simp [hev₁]
    case inr.inr.inr =>
      have ⟨i, h₈⟩ := instance_of_int_is_int hinst₁; subst h₈
      simp only [apply₁, intOrErr]
      cases i.neg?
      case none => simp; exact type_is_inhabited_int
      case some i' => simp; exact InstanceOfType.instance_of_int
    all_goals exact type_is_inhabited_int
  case isEmpty =>
    obtain ⟨htyr, ty₀, hbty⟩ := hmatch
    subst htyr; rw [hbty] at hinst₁
    simp only [EvaluatesToPred, evaluatePred] at hev₁ ⊢
    rcases hev₁ with hev₁ | hev₁ | hev₁ | hev₁ <;> simp [hev₁]
    case inr.inr.inr =>
      have ⟨s, h₈, _⟩ := instance_of_set_type_is_set hinst₁; subst h₈
      simp [apply₁]; exact bool_is_instance_of_anyBool _
    all_goals exact type_is_inhabited_bool
  case like p =>
    obtain ⟨htyr, hbty⟩ := hmatch
    subst htyr; rw [hbty] at hinst₁
    simp only [EvaluatesToPred, evaluatePred] at hev₁ ⊢
    rcases hev₁ with hev₁ | hev₁ | hev₁ | hev₁ <;> simp [hev₁]
    case inr.inr.inr =>
      have ⟨s, h₈⟩ := instance_of_string_is_string hinst₁; subst h₈
      simp [apply₁]; exact bool_is_instance_of_anyBool _
    all_goals exact type_is_inhabited_bool
  case is ety =>
    obtain ⟨ety', htyr, hbty⟩ := hmatch
    subst htyr; rw [hbty] at hinst₁
    simp only [EvaluatesToPred, evaluatePred] at hev₁ ⊢
    rcases hev₁ with hev₁ | hev₁ | hev₁ | hev₁ <;> simp [hev₁]
    case inr.inr.inr =>
      have ⟨uid, h₈, h₉⟩ := instance_of_entity_type_is_entity hinst₁
      simp [apply₁, h₉, h₈]
      cases h₁₀ : ety == ety' <;> simp at h₁₀ <;> simp [h₁₀]
      case false => exact false_is_instance_of_ff
      case true => exact true_is_instance_of_tt
    all_goals exact type_is_inhabited_bool

end Cedar.Thm
