/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Pred.SupportC
import Cedar.Thm.Validation.Typechecker.And

/-!
# Predicate type soundness — `.and` arm (Phase 9c, M3), WEAK form (D-94)

Mirror of `type_of_and_is_sound` (`Typechecker/And.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, dropping all capability plumbing: the
WEAK predicate soundness has no capability invariant, so the second IH is applied
with just `h₂`/`hit`. The result is a boolean; every branch closes with a bool
instance or an admitted error.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- Inversion of `typeOfPred (.and x₁ x₂)` (pred twin of `type_of_and_inversion`). -/
theorem type_of_pred_and_inversion {x₁ x₂ : PredExpr} {itTy : CedarType} {c c' : Capabilities}
    {env : TypeEnv} {tx : TypedExpr}
    (h₁ : typeOfPred (.and x₁ x₂) itTy c env = Except.ok (tx, c')) :
    ∃ tx₁ bty₁ c₁ tx₂ c₂,
      typeOfPred x₁ itTy c env = .ok (tx₁, c₁) ∧
      tx₁.typeOf = .bool bty₁ ∧
      typeOfPred x₂ itTy (c ∪ c₁) env = .ok (tx₂, c₂) ∧
      if bty₁ = BoolType.ff
      then tx = tx₁ ∧ c' = ∅
      else ∃ bty bty₂,
        tx = (.and tx₁ tx₂ (.bool bty)) ∧
        tx₂.typeOf = .bool bty₂ ∧
        if bty₂ = BoolType.ff
        then bty = BoolType.ff ∧ c' = ∅
        else bty = lubBool bty₁ bty₂ ∧ c' = c₁ ∪ c₂ := by
  simp only [typeOfPred] at h₁
  simp_do_let (typeOfPred x₁ itTy c env) as h₂ at h₁
  rename_i res₁
  obtain ⟨tr₁, cr₁⟩ := res₁
  simp_do_let (typeOfPred x₂ itTy (c ∪ cr₁) env) as h₂b at h₁
  rename_i res₂
  obtain ⟨tr₂, cr₂⟩ := res₂
  simp only [typeOfAnd, List.empty_eq] at h₁
  split at h₁ <;> simp only [ok, err, Except.ok.injEq, reduceCtorEq] at h₁
  case h_1 h₃ =>
    refine ⟨tr₁, BoolType.ff, cr₁, tr₂, cr₂, rfl, h₃, h₂b, ?_⟩
    simp only [↓reduceIte]
    obtain ⟨ht, hc⟩ := Prod.mk.inj h₁
    exact ⟨ht.symm, hc.symm⟩
  case h_2 bty₁ h₃ h₄ =>
    refine ⟨tr₁, bty₁, cr₁, tr₂, cr₂, rfl, h₄, h₂b, ?_⟩
    rw [if_neg h₃]
    simp only [bind, Except.bind] at h₁
    split at h₁ <;> simp only [ok, err, Except.ok.injEq, reduceCtorEq, Prod.mk.injEq] at h₁ <;>
    have ⟨hty, hc⟩ := h₁ <;> subst hty hc
    case h_1 hty₂ =>
      exact ⟨.ff, .ff, rfl, hty₂, by simp⟩
    case h_2 hty₂ =>
      refine ⟨bty₁, BoolType.tt, rfl, hty₂, ?_⟩
      cases bty₁
      case ff => exact absurd rfl h₃
      all_goals simp [lubBool]
    case h_3 bty₂ h₆ h₇ hty₂ =>
      refine ⟨.anyBool, bty₂, rfl, hty₂, ?_⟩
      have hbty₂ : bty₂ = .anyBool := by cases bty₂ <;> simp at h₆ h₇ ⊢
      subst hbty₂
      rw [if_neg (by simp)]
      cases bty₁ <;> simp [lubBool]

/-- `.and` predicate soundness (pred twin of `type_of_and_is_sound`), full-mirror form. -/
theorem type_of_pred_and_is_sound {x₁ x₂ : PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
    (hnr : NoReservedItKey env)
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.and x₁ x₂) itTy c₁ env = Except.ok (tx, c₂))
    (ih₁ : TypeOfPredIsSound x₁)
    (ih₂ : TypeOfPredIsSound x₂) :
    GuardedCapabilitiesInvariantPred (.and x₁ x₂) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.and x₁ x₂) it request entities v ∧ InstanceOfType env v tx.typeOf := by
  have ⟨tx₁, bty₁, rc₁, tx₂, rc₂, h₄, h₅, h₄b, h₆⟩ := type_of_pred_and_inversion h₃
  have ⟨ig₁, v₁, ih₁₂, ih₁₃⟩ := ih₁ hnr hci h₂ hit h₄
  rw [h₅] at ih₁₃
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃
  subst hb₁
  refine ⟨?_, ?_⟩
  · -- GUARDED CONCLUSION
    intro htrue
    -- `.and` yields true ⇒ both operands yield true.
    have ⟨hx₁, hx₂⟩ := pred_and_eval_true_inv htrue
    have hprod₁ : CapabilitiesInvariantPred rc₁ it request entities := ig₁ hx₁
    split at h₆
    case isTrue hff =>
      -- bty₁ = .ff would make x₁ instance of .ff hence false, contradicting x₁ = true.
      exfalso
      subst hff
      have hb₁eq : evaluatePred x₁ it request entities = .ok (.prim (.bool b₁)) := by
        rcases ih₁₂ with ⟨err, h⟩ | h
        · rw [hx₁] at h; simp only [reduceCtorEq] at h
        · rw [← h, hx₁]
      rw [hx₁] at hb₁eq
      simp only [Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hb₁eq
      subst hb₁eq
      have := instance_of_ff_is_false ih₁₃
      simp only [Value.prim.injEq, Prim.bool.injEq, reduceCtorEq] at this
    case isFalse =>
      replace ⟨bty, bty₂, htx, hty₂, h₆⟩ := h₆
      have hci₂ : CapabilitiesInvariantPred (c₁ ∪ rc₁) it request entities :=
        capability_union_invariant_pred hci hprod₁
      have ⟨ig₂, _, _, _⟩ := ih₂ hnr hci₂ h₂ hit h₄b
      have hprod₂ : CapabilitiesInvariantPred rc₂ it request entities := ig₂ hx₂
      split at h₆ <;> (have ⟨_, hc⟩ := h₆; subst hc)
      · exact empty_capabilities_invariant_pred it request entities
      · exact capability_union_invariant_pred hprod₁ hprod₂
  · -- VALUE + INSTANCE
    split at h₆
    case isTrue h₇ =>
      -- bty₁ = .ff: result is x₁ itself (c' = ∅), which evaluates to false or errors.
      subst h₇
      have ⟨hty, hc⟩ := h₆
      subst hty hc
      rw [h₅]
      -- b₁ must be false (instance of .ff).
      have h₈ := instance_of_ff_is_false ih₁₃
      simp only [Value.prim.injEq, Prim.bool.injEq] at h₈
      rcases ih₁₂ with ⟨err, ih₁₂⟩ | ih₁₂
      · exact ⟨_, EvaluatesToPred.error (pred_and_eval_err₁ ih₁₂), type_is_inhabited_bool.choose_spec⟩
      · subst h₈
        exact ⟨Value.prim (.bool false), Or.inr (pred_and_eval_false₁ ih₁₂), false_is_instance_of_ff⟩
    case isFalse h₇ =>
      replace ⟨bty, bty₂, htx, hty₂, h₆⟩ := h₆
      subst htx
      simp only [TypedExpr.typeOf]
      rcases ih₁₂ with ⟨err, ih₁₂⟩ | ih₁₂
      · exact ⟨_, EvaluatesToPred.error (pred_and_eval_err₁ ih₁₂), type_is_inhabited_bool.choose_spec⟩
      · cases b₁
        case false =>
          refine ⟨Value.prim (.bool false), Or.inr (pred_and_eval_false₁ ih₁₂), ?_⟩
          split at h₆ <;> (have ⟨hbty, _⟩ := h₆; subst hbty)
          case isTrue => exact false_is_instance_of_ff
          case isFalse => apply instance_of_lubBool; simp [ih₁₃]
        case true =>
          have hci₂ : CapabilitiesInvariantPred (c₁ ∪ rc₁) it request entities :=
            capability_union_invariant_pred hci (ig₁ ih₁₂)
          have ⟨_, v₂, ih₂₂, ih₂₃⟩ := ih₂ hnr hci₂ h₂ hit h₄b
          rw [hty₂] at ih₂₃
          rcases ih₂₂ with ⟨err₂, ih₂₂⟩ | ih₂₂
          · exact ⟨_, EvaluatesToPred.error (pred_and_eval_err₂ ih₁₂ ih₂₂),
              type_is_inhabited_bool.choose_spec⟩
          · have ⟨b₂, hb₂⟩ := instance_of_bool_is_bool ih₂₃
            subst hb₂
            refine ⟨Value.prim (.bool b₂), Or.inr (pred_and_eval_true₁ ih₁₂ ih₂₂), ?_⟩
            split at h₆
            case isTrue hbty₂ =>
              have ⟨hbty, _⟩ := h₆
              subst hbty hbty₂
              have h₈ := instance_of_ff_is_false ih₂₃
              simp only [Value.prim.injEq, Prim.bool.injEq] at h₈; subst h₈
              exact false_is_instance_of_ff
            case isFalse =>
              have ⟨hbty, _⟩ := h₆
              subst hbty
              apply instance_of_lubBool; simp [ih₂₃]

end Cedar.Thm
