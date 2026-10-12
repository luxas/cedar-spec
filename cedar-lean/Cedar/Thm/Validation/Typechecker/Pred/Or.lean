/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Pred.SupportC
import Cedar.Thm.Validation.Typechecker.Or

/-!
# Predicate type soundness — `.or` arm (Phase 9c, D-97 option b)

Mirror of `type_of_or_is_sound` (`Typechecker/Or.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the STRONG form (D-97): carries the
predicate capability invariant `CapabilitiesInvariantPred c₁ …` and concludes the
guarded production of `CapabilitiesInvariantPred c₂`.

`typeOfPred (.or x₁ x₂)` peels `typeOfPred x₁`, then `typeOfPred x₂ itTy c env`
(x₂ typed under the OUTER caps, exactly as the expression typechecker does), then
`typeOfOr`. `evaluatePred (.or x₁ x₂)` short-circuits: evaluate `x₁` as `Bool`; if
`true` yield `true`, else yield `(evaluatePred x₂).as Bool`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- Inversion of `typeOfPred (.or x₁ x₂)` (pred twin of `type_of_or_inversion`). -/
theorem type_of_pred_or_inversion {x₁ x₂ : PredExpr} {itTy : CedarType} {c c' : Capabilities}
    {env : TypeEnv} {tx : TypedExpr}
    (h₁ : typeOfPred (.or x₁ x₂) itTy c env = Except.ok (tx, c')) :
    ∃ tx₁ bty₁ c₁,
      typeOfPred x₁ itTy c env = .ok (tx₁, c₁) ∧
      tx₁.typeOf = .bool bty₁ ∧
      if bty₁ = BoolType.tt
      then tx = tx₁ ∧ c' = ∅
      else ∃ bty tx₂ bty₂ c₂,
        tx = (.or tx₁ tx₂ (.bool bty)) ∧
        typeOfPred x₂ itTy c env = .ok (tx₂, c₂) ∧
        tx₂.typeOf = .bool bty₂ ∧
        if bty₁ = BoolType.ff
        then bty = bty₂ ∧ c' = c₂
        else if bty₂ = BoolType.tt
        then bty = BoolType.tt ∧ c' = ∅
        else if bty₂ = BoolType.ff
        then bty = BoolType.anyBool ∧ c' = c₁
        else bty = BoolType.anyBool ∧ c' = c₁ ∩ c₂ := by
  simp only [typeOfPred] at h₁
  simp_do_let (typeOfPred x₁ itTy c env) as h₂ at h₁
  rename_i res₁
  obtain ⟨tr₁, cr₁⟩ := res₁
  simp_do_let (typeOfPred x₂ itTy c env) as h₂b at h₁
  rename_i res₂
  obtain ⟨tr₂, cr₂⟩ := res₂
  simp only [typeOfOr] at h₁
  split at h₁ <;> simp only [ok, err, Except.ok.injEq, reduceCtorEq] at h₁ <;>
    rename_i hr₁
  case h_1 =>
    refine ⟨tr₁, BoolType.tt, cr₁, rfl, hr₁, ?_⟩
    simp only [↓reduceIte]
    obtain ⟨ht, hc⟩ := Prod.mk.inj h₁
    exact ⟨ht.symm, hc.symm⟩
  case h_2 =>
    refine ⟨tr₁, BoolType.ff, cr₁, rfl, hr₁, ?_⟩
    rw [if_neg (by simp)]
    simp only [bind, Except.bind] at h₁
    split at h₁ <;> simp only [ok, err, Except.ok.injEq, reduceCtorEq, Prod.mk.injEq] at h₁
    rename_i bty₂ hty₂
    obtain ⟨hty, hc⟩ := h₁
    subst hty hc
    refine ⟨bty₂, tr₂, bty₂, cr₂, by rw [hty₂], rfl, hty₂, ?_⟩
    rw [if_pos rfl]; exact ⟨rfl, rfl⟩
  case h_3 bty₁ hneq₁ hneq₂ =>
    cases bty₁ <;> simp only [reduceCtorEq, not_false_eq_true, forall_const] at hneq₁ hneq₂ ⊢
    refine ⟨tr₁, BoolType.anyBool, cr₁, rfl, hr₁, ?_⟩
    rw [if_neg (by simp)]
    simp only [bind, Except.bind] at h₁
    split at h₁ <;> simp only [ok, err, Except.ok.injEq, reduceCtorEq, Prod.mk.injEq] at h₁ <;>
      rename_i hty₂ <;> obtain ⟨hty, hc⟩ := h₁ <;> subst hty hc
    case h_1 =>
      refine ⟨BoolType.tt, tr₂, BoolType.tt, cr₂, rfl, rfl, hty₂, ?_⟩
      rw [if_neg (by simp), if_pos rfl]; exact ⟨rfl, rfl⟩
    case h_2 =>
      refine ⟨BoolType.anyBool, tr₂, BoolType.ff, cr₂, rfl, rfl, hty₂, ?_⟩
      rw [if_neg (by simp), if_neg (by simp), if_pos rfl]; exact ⟨rfl, rfl⟩
    case h_3 bty₂ hneq₃ hneq₄ =>
      have hbty₂ : bty₂ = .anyBool := by cases bty₂ <;> simp at hneq₃ hneq₄ ⊢
      subst hbty₂
      refine ⟨BoolType.anyBool, tr₂, BoolType.anyBool, cr₂, rfl, rfl, hty₂, ?_⟩
      rw [if_neg (by simp), if_neg (by simp), if_neg (by simp)]; exact ⟨rfl, rfl⟩

/-- `.or` predicate soundness (pred twin of `type_of_or_is_sound`), STRONG form. -/
theorem type_of_pred_or_is_sound {x₁ x₂ : PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
    (hnr : NoReservedItKey env)
    (hitwf : itTy.WellFormed env)
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.or x₁ x₂) itTy c₁ env = Except.ok (tx, c₂))
    (ih₁ : TypeOfPredIsSound x₁)
    (ih₂ : TypeOfPredIsSound x₂) :
    GuardedCapabilitiesInvariantPred (.or x₁ x₂) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.or x₁ x₂) it request entities v ∧ InstanceOfType env v tx.typeOf := by
  have ⟨tx₁, bty₁, rc₁, h₄, h₅, h₆⟩ := type_of_pred_or_inversion h₃
  have ⟨ig₁, v₁, ih₁₂, ih₁₃⟩ := ih₁ hnr hitwf hci h₂ hit h₄
  rw [h₅] at ih₁₃
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃
  subst hb₁
  refine ⟨?_, ?_⟩
  · -- GUARDED CONCLUSION
    intro htrue
    -- `.or` true ⇒ x₁ true, or x₁ false and x₂ true.
    rcases pred_or_eval_true_inv htrue with hx₁ | ⟨hx₁, hx₂⟩
    · -- x₁ true ⇒ bty₁ ≠ ff; its production carries the caps when the output is c₁'s.
      split at h₆
      case isTrue h₇ =>
        -- bty₁ = tt: output caps are ∅.
        have ⟨_, hc⟩ := h₆; subst hc
        exact empty_capabilities_invariant_pred it request entities
      case isFalse h₇ =>
        replace ⟨bty, tx₂, bty₂, rc₂, htx, h₄b, hty₂, h₆⟩ := h₆
        have hprod₁ : CapabilitiesInvariantPred rc₁ it request entities := ig₁ hx₁
        -- With x₁ = true and bty₁ ≠ tt, bty₁ must be .anyBool (ff is impossible: a
        -- .ff-typed sub-predicate never evaluates to true).
        split at h₆
        case isTrue hff =>
          exfalso; subst hff
          -- x₁ = true but bty₁ = ff: instance of .ff forces b₁ = false.
          have hb₁f : b₁ = false := by
            have := instance_of_ff_is_false ih₁₃
            simpa only [Value.prim.injEq, Prim.bool.injEq] using this
          subst hb₁f
          rcases ih₁₂ with ⟨err, he⟩ | he <;> rw [hx₁] at he <;>
            simp only [reduceCtorEq, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at he
        case isFalse hff =>
          split at h₆
          case isTrue =>
            have ⟨_, hc⟩ := h₆; subst hc
            exact empty_capabilities_invariant_pred it request entities
          case isFalse =>
            split at h₆ <;> (have ⟨_, hc⟩ := h₆; subst hc)
            · exact hprod₁
            · exact capability_intersection_invariant_pred (Or.inl hprod₁)
    · -- x₁ false, x₂ true.
      have hb₁f := hx₁
      split at h₆
      case isTrue h₇ =>
        -- bty₁ = tt impossible with x₁ = false.
        exfalso; subst h₇
        have hb₁t : b₁ = true := by
          have := instance_of_tt_is_true ih₁₃
          simpa only [Value.prim.injEq, Prim.bool.injEq] using this
        subst hb₁t
        rcases ih₁₂ with ⟨err, he⟩ | he <;> rw [hx₁] at he <;>
          simp only [reduceCtorEq, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at he
      case isFalse h₇ =>
        replace ⟨bty, tx₂, bty₂, rc₂, htx, h₄b, hty₂, h₆⟩ := h₆
        have ⟨ig₂, _v₂, ih₂₂, ih₂₃⟩ := ih₂ hnr hitwf hci h₂ hit h₄b
        rw [hty₂] at ih₂₃
        have hprod₂ : CapabilitiesInvariantPred rc₂ it request entities := ig₂ hx₂
        split at h₆
        case isTrue hff =>
          -- bty₁ = ff ⇒ c' = c₂ (x₂'s caps, invariant since x₂ = true).
          have ⟨_, hc⟩ := h₆; subst hc
          exact hprod₂
        case isFalse hff =>
          split at h₆
          case isTrue =>
            -- bty₂ = tt ⇒ c' = ∅.
            have ⟨_, hc⟩ := h₆; subst hc
            exact empty_capabilities_invariant_pred it request entities
          case isFalse hbty₂ff =>
            split at h₆
            case isTrue hff₂ =>
              -- bty₂ = ff is impossible: x₂ = true but instance of .ff is false.
              exfalso; subst hff₂
              have hv₂f : _v₂ = .prim (.bool false) := instance_of_ff_is_false ih₂₃
              rcases ih₂₂ with ⟨err, he⟩ | he <;> rw [hx₂] at he <;>
                simp only [reduceCtorEq, Except.ok.injEq, hv₂f, Value.prim.injEq,
                  Prim.bool.injEq] at he
            case isFalse =>
              -- bty₂ = anyBool ⇒ c' = c₁ ∩ c₂; use x₂'s invariant on the right.
              have ⟨_, hc⟩ := h₆; subst hc
              exact capability_intersection_invariant_pred (Or.inr hprod₂)
  · -- VALUE + INSTANCE
    split at h₆
    case isTrue h₇ =>
      -- bty₁ = tt: result is x₁ itself; evaluates to true or errors.
      subst h₇
      have ⟨hty, hc⟩ := h₆
      subst hty hc
      rw [h₅]
      have h₈ := instance_of_tt_is_true ih₁₃
      simp only [Value.prim.injEq, Prim.bool.injEq] at h₈
      rcases ih₁₂ with ⟨err, ih₁₂⟩ | ih₁₂
      · exact ⟨_, EvaluatesToPred.error (pred_or_eval_err₁ ih₁₂), type_is_inhabited_bool.choose_spec⟩
      · subst h₈
        exact ⟨Value.prim (.bool true), Or.inr (pred_or_eval_true₁ ih₁₂), true_is_instance_of_tt⟩
    case isFalse h₇ =>
      replace ⟨bty, tx₂, bty₂, rc₂, htx, h₄b, hty₂, h₆⟩ := h₆
      subst htx
      simp only [TypedExpr.typeOf]
      rcases ih₁₂ with ⟨err, ih₁₂⟩ | ih₁₂
      · exact ⟨_, EvaluatesToPred.error (pred_or_eval_err₁ ih₁₂), type_is_inhabited_bool.choose_spec⟩
      · cases b₁
        case true =>
          -- x₁ true ⇒ .or short-circuits to true. The result type contains tt.
          refine ⟨Value.prim (.bool true), Or.inr (pred_or_eval_true₁ ih₁₂), ?_⟩
          -- bty₁ ≠ tt (isFalse), and x₁ = true forces bty₁ = anyBool.
          split at h₆ <;> rename_i hff
          · -- bty₁ = ff impossible with x₁ = true
            exfalso; subst hff
            have := instance_of_ff_is_false ih₁₃
            simp only [Value.prim.injEq, Prim.bool.injEq, reduceCtorEq] at this
          · split at h₆ <;> rename_i hty₂tt
            · have ⟨hbty, _⟩ := h₆; subst hbty; exact true_is_instance_of_tt
            · split at h₆ <;> (have ⟨hbty, _⟩ := h₆; subst hbty) <;>
                exact bool_is_instance_of_anyBool _
        case false =>
          -- x₁ false ⇒ result is x₂'s boolean (or error).
          have ⟨_, v₂, ih₂₂, ih₂₃⟩ := ih₂ hnr hitwf hci h₂ hit h₄b
          rw [hty₂] at ih₂₃
          rcases ih₂₂ with ⟨err₂, ih₂₂⟩ | ih₂₂
          · exact ⟨_, EvaluatesToPred.error (pred_or_eval_err₂ ih₁₂ ih₂₂),
              type_is_inhabited_bool.choose_spec⟩
          · have ⟨b₂, hb₂⟩ := instance_of_bool_is_bool ih₂₃
            subst hb₂
            refine ⟨Value.prim (.bool b₂), Or.inr (pred_or_eval_false₁ ih₁₂ ih₂₂), ?_⟩
            split at h₆ <;> rename_i hff
            · -- bty₁ = ff ⇒ bty = bty₂.
              have ⟨hbty, _⟩ := h₆; subst hbty; exact ih₂₃
            · split at h₆ <;> rename_i hty₂tt
              · -- bty₂ = tt ⇒ bty = tt ⇒ b₂ = true.
                subst hty₂tt
                have ⟨hbty, _⟩ := h₆; subst hbty
                have := instance_of_tt_is_true ih₂₃
                simp only [Value.prim.injEq, Prim.bool.injEq] at this; subst this
                exact true_is_instance_of_tt
              · split at h₆ <;> (have ⟨hbty, _⟩ := h₆; subst hbty) <;>
                  exact bool_is_instance_of_anyBool _

end Cedar.Thm
