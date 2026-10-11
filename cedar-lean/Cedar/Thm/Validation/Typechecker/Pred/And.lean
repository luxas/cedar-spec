/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
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
    ∃ tx₁ bty₁ c₁,
      typeOfPred x₁ itTy c env = .ok (tx₁, c₁) ∧
      tx₁.typeOf = .bool bty₁ ∧
      if bty₁ = BoolType.ff
      then tx = tx₁ ∧ c' = ∅
      else ∃ bty tx₂ bty₂ c₂,
        tx = (.and tx₁ tx₂ (.bool bty)) ∧
        typeOfPred x₂ itTy (c ∪ c₁) env = .ok (tx₂, c₂) ∧
        tx₂.typeOf = .bool bty₂ ∧
        if bty₂ = BoolType.ff
        then bty = BoolType.ff ∧ c' = ∅
        else bty = lubBool bty₁ bty₂ ∧ c' = c₁ ∪ c₂ := by
  simp only [typeOfPred] at h₁
  simp_do_let (typeOfPred x₁ itTy c env) as h₂ at h₁
  rename_i res₁
  obtain ⟨tr₁, cr₁⟩ := res₁
  simp only [typeOfAnd, List.empty_eq] at h₁
  split at h₁ <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h₁
  case h_1 h₃ =>
    have ⟨ hl₁, hr₁ ⟩ := h₁
    subst hl₁ hr₁
    refine ⟨tr₁, BoolType.ff, cr₁, h₂, h₃, ?_⟩
    simp only [↓reduceIte, and_self]
  case h_2 bty₁ h₃ h₄ =>
    refine ⟨tr₁, bty₁, cr₁, h₂, h₄, ?_⟩
    rw [if_neg h₃]
    cases h₅ : typeOfPred x₂ itTy (c ∪ cr₁) env <;> simp only [h₅, Except.bind_ok,
      Except.bind_err, reduceCtorEq] at h₁
    rename_i res₂
    obtain ⟨tr₂, cr₂⟩ := res₂
    split at h₁ <;> simp only [ok, err, Except.ok.injEq, reduceCtorEq, Prod.mk.injEq] at h₁ <;>
    have ⟨hty, hc⟩ := h₁ <;> subst hty hc
    case h_1 hty₂ =>
      exact ⟨.ff, tr₂, .ff, cr₂, rfl, h₅, hty₂, by simp⟩
    case h_2 hty₂ =>
      refine ⟨bty₁, tr₂, BoolType.tt, cr₂, rfl, h₅, hty₂, ?_⟩
      cases bty₁
      case ff => exact absurd rfl h₃
      all_goals simp [lubBool]
    case h_3 bty₂ h₆ h₇ hty₂ =>
      refine ⟨.anyBool, tr₂, bty₂, cr₂, rfl, h₅, hty₂, ?_⟩
      have hbty₂ : bty₂ = .anyBool := by cases bty₂ <;> simp at h₆ h₇ ⊢
      subst hbty₂
      rw [if_neg (by simp)]
      cases bty₁ <;> simp [lubBool]

/-- `.and` predicate soundness (pred twin of `type_of_and_is_sound`), full-mirror form. -/
theorem type_of_pred_and_is_sound {x₁ x₂ : PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.and x₁ x₂) itTy c₁ env = Except.ok (tx, c₂))
    (ih₁ : TypeOfPredIsSound x₁)
    (ih₂ : TypeOfPredIsSound x₂) :
    GuardedCapabilitiesInvariantPred (.and x₁ x₂) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.and x₁ x₂) it request entities v ∧ InstanceOfType env v tx.typeOf := by
  have ⟨tx₁, bty₁, rc₁, h₄, h₅, h₆⟩ := type_of_pred_and_inversion h₃
  have ⟨ig₁, v₁, ih₁₂, ih₁₃⟩ := ih₁ hci h₂ hit h₄
  rw [h₅] at ih₁₃
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃
  subst hb₁
  -- A single bool-or-error fact about x₁'s evaluation, reused for value and guard.
  have hx₁val : evaluatePred x₁ it request entities = .ok (.prim (.bool b₁)) ∨
      ∃ err, evaluatePred x₁ it request entities = .error err := by
    rcases ih₁₂ with ⟨err, h⟩ | h
    · exact Or.inr ⟨err, h⟩
    · exact Or.inl h
  refine ⟨?_, ?_⟩
  · -- GUARDED CONCLUSION
    intro htrue
    simp only [evaluatePred, Result.as, Coe.coe, Value.asBool] at htrue
    rcases hx₁val with hx₁ | ⟨err, hx₁⟩
    · rw [hx₁] at htrue
      cases b₁ <;> simp only [Bool.not_false, Bool.not_true, ite_true, ite_false,
        Except.ok.injEq, reduceCtorEq] at htrue
      -- b₁ = true ⇒ x₂ evaluates to true
      cases hx₂ : evaluatePred x₂ it request entities with
      | error e => rw [hx₂] at htrue; simp only [Except.bind_err, reduceCtorEq] at htrue
      | ok v₂ =>
        rw [hx₂] at htrue
        cases v₂ <;> simp only [Except.bind_ok, reduceCtorEq] at htrue
        rename_i p; cases p <;> simp only [reduceCtorEq] at htrue
        rename_i b; cases b <;> simp only [Except.ok.injEq, reduceCtorEq] at htrue
        -- both true: produce c₂'s invariant from the two IH guarded productions
        have hprod₁ : CapabilitiesInvariantPred rc₁ it request entities := ig₁ hx₁
        split at h₆
        case isTrue hff => exact absurd h₅ (by rw [hff]; exact (ih₁₃ ▸ (by
          have := instance_of_tt_is_true (by rw [← h₅] at ih₁₃; exact ih₁₃)
          simp_all)))
        case isFalse =>
          replace ⟨bty, tx₂, bty₂, rc₂, htx, htx₂, hty₂, h₆⟩ := h₆
          have hci₂ : CapabilitiesInvariantPred (c₁ ∪ rc₁) it request entities :=
            capability_union_invariant_pred hci hprod₁
          have ⟨ig₂, _, _, _⟩ := ih₂ hci₂ h₂ hit htx₂
          have hprod₂ : CapabilitiesInvariantPred rc₂ it request entities := ig₂ hx₂
          split at h₆ <;> (have ⟨_, hc⟩ := h₆; subst hc)
          · exact empty_capabilities_invariant_pred it request entities
          · exact capability_union_invariant_pred hprod₁ hprod₂
    · rw [hx₁] at htrue; simp only [Except.bind_err, reduceCtorEq] at htrue
  · -- VALUE + INSTANCE
    simp only [EvaluatesToPred, evaluatePred, Result.as, Coe.coe, Value.asBool] at ih₁₂ ⊢
    split at h₆
    case isTrue h₇ =>
      subst h₇
      have ⟨hty, hc⟩ := h₆
      subst hty hc
      rw [h₅]
      have h₈ := instance_of_ff_is_false ih₁₃
      simp only [InstanceOfBoolType] at h₈
      rcases ih₁₂ with ⟨err, ih₁₂⟩ | ih₁₂
      · exact ⟨_, EvaluatesToPred.error (by simp only [evaluatePred, Result.as, Coe.coe, Value.asBool, ih₁₂]; rfl), type_is_inhabited_bool.choose_spec⟩
      · subst h₈
        refine ⟨Value.prim (.bool false), Or.inr ?_, false_is_instance_of_ff⟩
        simp only [evaluatePred, Result.as, Coe.coe, Value.asBool, ih₁₂]
    case isFalse h₇ =>
      replace ⟨bty, tx₂, bty₂, rc₂, htx, htx₂, hty₂, h₆⟩ := h₆
      subst htx
      simp only [TypedExpr.typeOf]
      rcases ih₁₂ with ⟨err, ih₁₂⟩ | ih₁₂
      · refine ⟨_, EvaluatesToPred.error ?_, type_is_inhabited_bool.choose_spec⟩
        simp only [evaluatePred, Result.as, Coe.coe, Value.asBool, ih₁₂]
      · cases b₁
        case false =>
          refine ⟨Value.prim (.bool false), Or.inr ?_, ?_⟩
          · simp only [evaluatePred, Result.as, Coe.coe, Value.asBool, ih₁₂]
          · split at h₆ <;> (have ⟨hbty, _⟩ := h₆; subst hbty)
            case isTrue => exact false_is_instance_of_ff
            case isFalse => apply instance_of_lubBool; simp [ih₁₃]
        case true =>
          have hci₂ : CapabilitiesInvariantPred (c₁ ∪ rc₁) it request entities :=
            capability_union_invariant_pred hci (ig₁ ih₁₂)
          have ⟨_, v₂, ih₂₂, ih₂₃⟩ := ih₂ hci₂ h₂ hit htx₂
          rw [hty₂] at ih₂₃
          rcases ih₂₂ with ⟨err₂, ih₂₂⟩ | ih₂₂
          · refine ⟨_, EvaluatesToPred.error ?_, type_is_inhabited_bool.choose_spec⟩
            simp only [evaluatePred, Result.as, Coe.coe, Value.asBool, ih₁₂, ih₂₂]
          · have ⟨b₂, hb₂⟩ := instance_of_bool_is_bool ih₂₃
            subst hb₂
            refine ⟨Value.prim (.bool b₂), Or.inr ?_, ?_⟩
            · simp only [evaluatePred, Result.as, Coe.coe, Value.asBool, ih₁₂, ih₂₂]
            · split at h₆ <;> (have ⟨hbty, _⟩ := h₆; subst hbty)
              case isTrue hbty₂ =>
                have h₈ := instance_of_ff_is_false ih₂₃
                simp only [InstanceOfBoolType] at h₈; subst h₈
                exact false_is_instance_of_ff
              case isFalse => apply instance_of_lubBool; simp [ih₂₃]

end Cedar.Thm
