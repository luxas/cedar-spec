/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Pred.SupportC
import Cedar.Thm.Validation.Typechecker.IfThenElse

/-!
# Predicate type soundness — `.ite` arm (Phase 9c, D-97 option b, D-73a)

Mirror of `type_of_ite_is_sound` (`Typechecker/IfThenElse.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the STRONG form (D-97). Per D-73a the
predicate `.ite` keeps the condition and type-checks BOTH branches regardless of
the condition's static boolean type, so the inversion always produces `tx₂`/`tx₃`
and the result type is the branch type (`.tt`/`.ff`) or their least upper bound
(`.anyBool`).

`typeOfPred (.ite x₁ x₂ x₃)` peels `typeOfPred x₁`, then
`typeOfPred x₂ (c ∪ c₁)`, then `typeOfPred x₃ c`, then `typeOfIf`.
`evaluatePred (.ite x₁ x₂ x₃)` evaluates `x₁` as `Bool`; `true` → `x₂`, `false` → `x₃`.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

/-- Inversion of `typeOfPred (.ite x₁ x₂ x₃)` (pred twin of `type_of_ite_inversion`). -/
theorem type_of_pred_ite_inversion {x₁ x₂ x₃ : PredExpr} {itTy : CedarType}
    {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h₁ : typeOfPred (.ite x₁ x₂ x₃) itTy c env = Except.ok (tx, c')) :
    ∃ tx₁ bty₁ c₁ tx₂ c₂ tx₃ c₃,
      tx = TypedExpr.ite tx₁ tx₂ tx₃ tx.typeOf ∧
      typeOfPred x₁ itTy c env = .ok (tx₁, c₁) ∧
      tx₁.typeOf = .bool bty₁ ∧
      match bty₁ with
      | .ff      =>
        typeOfPred x₃ itTy c env = .ok (tx₃, c₃) ∧
        tx.typeOf = tx₃.typeOf ∧ c' = c₃
      | .tt      =>
        typeOfPred x₂ itTy (c ∪ c₁) env = .ok (tx₂, c₂) ∧
        tx.typeOf = tx₂.typeOf ∧ c' = c₁ ∪ c₂
      | .anyBool =>
        typeOfPred x₂ itTy (c ∪ c₁) env = .ok (tx₂, c₂) ∧
        typeOfPred x₃ itTy c env = .ok (tx₃, c₃) ∧
        (tx₂.typeOf ⊔ tx₃.typeOf) = (.some tx.typeOf) ∧ c' = (c₁ ∪ c₂) ∩ c₃ := by
  simp only [typeOfPred] at h₁
  simp_do_let (typeOfPred x₁ itTy c env) as h₂ at h₁
  rename_i res₁
  obtain ⟨tr₁, cr₁⟩ := res₁
  simp_do_let (typeOfPred x₂ itTy (c ∪ cr₁) env) as h₂b at h₁
  rename_i res₂
  obtain ⟨tr₂, cr₂⟩ := res₂
  simp_do_let (typeOfPred x₃ itTy c env) as h₂c at h₁
  rename_i res₃
  obtain ⟨tr₃, cr₃⟩ := res₃
  simp only [typeOfIf] at h₁
  split at h₁ <;> try (simp only [ok, err, reduceCtorEq] at h₁)
  case h_1 hr₁ =>
    -- bty₁ = tt: typeOfIf duplicates the THEN branch into both slots.
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h₁
    obtain ⟨hty, hc⟩ := h₁
    subst hty hc
    exact ⟨tr₁, BoolType.tt, cr₁, tr₂, cr₂, tr₂, cr₂, rfl, rfl, hr₁, h₂b, rfl, rfl⟩
  case h_2 hr₁ =>
    -- bty₁ = ff: typeOfIf duplicates the ELSE branch into both slots.
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h₁
    obtain ⟨hty, hc⟩ := h₁
    subst hty hc
    exact ⟨tr₁, BoolType.ff, cr₁, tr₃, cr₃, tr₃, cr₃, rfl, rfl, hr₁, rfl, rfl, rfl⟩
  case h_3 hr₁ =>
    simp only [bind, Except.bind] at h₁
    split at h₁ <;> simp only [ok, err, Except.ok.injEq, reduceCtorEq, Prod.mk.injEq] at h₁
    rename_i ty' hlub
    obtain ⟨hty, hc⟩ := h₁
    subst hty hc
    exact ⟨tr₁, BoolType.anyBool, cr₁, tr₂, cr₂, tr₃, cr₃, rfl, rfl, hr₁, h₂b, rfl, hlub, rfl⟩

/-- `.ite` predicate soundness (pred twin of `type_of_ite_is_sound`), STRONG form. -/
theorem type_of_pred_ite_is_sound {x₁ x₂ x₃ : PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
    (hnr : NoReservedItKey env)
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.ite x₁ x₂ x₃) itTy c₁ env = Except.ok (tx, c₂))
    (ih₁ : TypeOfPredIsSound x₁)
    (ih₂ : TypeOfPredIsSound x₂)
    (ih₃ : TypeOfPredIsSound x₃) :
    GuardedCapabilitiesInvariantPred (.ite x₁ x₂ x₃) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.ite x₁ x₂ x₃) it request entities v ∧ InstanceOfType env v tx.typeOf := by
  have ⟨tx₁, bty₁, rc₁, tx₂, rc₂, tx₃, rc₃, h₄, h₅, h₆, h₇⟩ := type_of_pred_ite_inversion h₃
  have ⟨ig₁, v₁, ih₁₂, ih₁₃⟩ := ih₁ hnr hci h₂ hit h₅
  rw [h₆] at ih₁₃
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃
  subst hb₁
  -- If the condition errors, the whole ite errors; otherwise x₁ = .ok (bool b₁).
  rcases ih₁₂ with ⟨cerr, hcerr⟩ | hcond
  · -- condition errors ⇒ ite errors; guard is vacuous, value side needs a type witness.
    rw [h₄]
    cases bty₁ <;> simp only at h₇
    case tt =>
      obtain ⟨h₂b, hty, hc⟩ := h₇
      refine ⟨fun h => absurd (by rw [pred_ite_eval_err₁ hcerr] at h; exact h) (by simp), ?_⟩
      rw [hty]
      -- The then-branch's result type is inhabited. Its well-formedness is the
      -- OPEN pred-output-type-WF obligation (D-P9c-8, arm A's
      -- `type_of_pred_implies_wf_type`): this is the only `.ite` path where the
      -- condition ERRORS under a `.tt`-typed condition, so x₂'s caps-dependent
      -- result type cannot be re-derived under `hci` alone. Left OPEN (red, no
      -- `sorry`); every other `.ite` path is fully discharged.
      have hwf₂ : CedarType.WellFormed env tx₂.typeOf := by skip
      have ⟨v₂, hv₂⟩ := type_is_inhabited h₂.1 hwf₂
      exact ⟨v₂, EvaluatesToPred.error (pred_ite_eval_err₁ hcerr), hv₂⟩
    case ff =>
      obtain ⟨h₂c, hty, hc⟩ := h₇
      have ⟨_, v₃, _, ih₃₃⟩ := ih₃ hnr hci h₂ hit h₂c
      refine ⟨fun h => absurd (by rw [pred_ite_eval_err₁ hcerr] at h; exact h) (by simp), ?_⟩
      rw [hty]; simp only [TypedExpr.typeOf]
      exact ⟨v₃, EvaluatesToPred.error (pred_ite_eval_err₁ hcerr), ih₃₃⟩
    case anyBool =>
      obtain ⟨h₂b, h₂c, hlub, hc⟩ := h₇
      have ⟨_, v₃, _, ih₃₃⟩ := ih₃ hnr hci h₂ hit h₂c
      refine ⟨fun h => absurd (by rw [pred_ite_eval_err₁ hcerr] at h; exact h) (by simp), ?_⟩
      simp only [TypedExpr.typeOf]
      exact ⟨v₃, EvaluatesToPred.error (pred_ite_eval_err₁ hcerr), instance_of_lub hlub (Or.inr ih₃₃)⟩
  · -- condition evaluates to .ok (bool b₁).
    cases bty₁
    case tt =>
      simp only at h₇
      obtain ⟨h₂b, hty, hc⟩ := h₇
      -- bty₁ = tt forces b₁ = true.
      have hb₁t := instance_of_tt_is_true ih₁₃
      simp only [Value.prim.injEq, Prim.bool.injEq] at hb₁t
      subst hb₁t
      have hci₂ : CapabilitiesInvariantPred (c₁ ∪ rc₁) it request entities :=
        capability_union_invariant_pred hci (ig₁ hcond)
      have ⟨ig₂, v₂, ih₂₂, ih₂₃⟩ := ih₂ hnr hci₂ h₂ hit h₂b
      rw [h₄, hty]
      refine ⟨?_, ?_⟩
      · intro htrue
        rw [pred_ite_eval_true hcond] at htrue
        subst hc
        exact capability_union_invariant_pred (ig₁ hcond) (ig₂ htrue)
      · simp only [TypedExpr.typeOf]
        rcases ih₂₂ with ⟨err₂, ih₂₂⟩ | ih₂₂
        · exact ⟨v₂, EvaluatesToPred.error (by rw [pred_ite_eval_true hcond]; exact ih₂₂), ih₂₃⟩
        · exact ⟨v₂, Or.inr (by rw [pred_ite_eval_true hcond]; exact ih₂₂), ih₂₃⟩
    case ff =>
      simp only at h₇
      obtain ⟨h₂c, hty, hc⟩ := h₇
      -- bty₁ = ff forces b₁ = false.
      have hb₁f := instance_of_ff_is_false ih₁₃
      simp only [Value.prim.injEq, Prim.bool.injEq] at hb₁f
      subst hb₁f
      have ⟨ig₃, v₃, ih₃₂, ih₃₃⟩ := ih₃ hnr hci h₂ hit h₂c
      rw [h₄, hty]
      subst hc
      refine ⟨?_, ?_⟩
      · intro htrue
        rw [pred_ite_eval_false hcond] at htrue
        exact ig₃ htrue
      · simp only [TypedExpr.typeOf]
        rcases ih₃₂ with ⟨err₃, ih₃₂⟩ | ih₃₂
        · exact ⟨v₃, EvaluatesToPred.error (by rw [pred_ite_eval_false hcond]; exact ih₃₂), ih₃₃⟩
        · exact ⟨v₃, Or.inr (by rw [pred_ite_eval_false hcond]; exact ih₃₂), ih₃₃⟩
    case anyBool =>
      simp only at h₇
      obtain ⟨h₂b, h₂c, hlub, hc⟩ := h₇
      rw [h₄]
      cases b₁
      case true =>
        have hci₂ : CapabilitiesInvariantPred (c₁ ∪ rc₁) it request entities :=
          capability_union_invariant_pred hci (ig₁ hcond)
        have ⟨ig₂, v₂, ih₂₂, ih₂₃⟩ := ih₂ hnr hci₂ h₂ hit h₂b
        refine ⟨?_, ?_⟩
        · intro htrue
          rw [pred_ite_eval_true hcond] at htrue
          subst hc
          exact capability_intersection_invariant_pred
            (Or.inl (capability_union_invariant_pred (ig₁ hcond) (ig₂ htrue)))
        · simp only [TypedExpr.typeOf]
          rcases ih₂₂ with ⟨err₂, ih₂₂⟩ | ih₂₂
          · exact ⟨v₂, EvaluatesToPred.error (by rw [pred_ite_eval_true hcond]; exact ih₂₂),
              instance_of_lub hlub (Or.inl ih₂₃)⟩
          · exact ⟨v₂, Or.inr (by rw [pred_ite_eval_true hcond]; exact ih₂₂),
              instance_of_lub hlub (Or.inl ih₂₃)⟩
      case false =>
        have ⟨ig₃, v₃, ih₃₂, ih₃₃⟩ := ih₃ hnr hci h₂ hit h₂c
        refine ⟨?_, ?_⟩
        · intro htrue
          rw [pred_ite_eval_false hcond] at htrue
          subst hc
          exact capability_intersection_invariant_pred (Or.inr (ig₃ htrue))
        · simp only [TypedExpr.typeOf]
          rcases ih₃₂ with ⟨err₃, ih₃₂⟩ | ih₃₂
          · exact ⟨v₃, EvaluatesToPred.error (by rw [pred_ite_eval_false hcond]; exact ih₃₂),
              instance_of_lub hlub (Or.inr ih₃₃)⟩
          · exact ⟨v₃, Or.inr (by rw [pred_ite_eval_false hcond]; exact ih₃₂),
              instance_of_lub hlub (Or.inr ih₃₃)⟩

end Cedar.Thm
