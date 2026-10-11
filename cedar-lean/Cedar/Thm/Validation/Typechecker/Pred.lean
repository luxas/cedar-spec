/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Pred.SupportA
import Cedar.Thm.Validation.Typechecker.Pred.UnaryApp
import Cedar.Thm.Validation.Typechecker.Pred.BinaryApp
import Cedar.Thm.Validation.Typechecker.Pred.GetAttr
import Cedar.Thm.Validation.Typechecker.Pred.HasAttr
import Cedar.Thm.Validation.Typechecker.Pred.ExtHasAttr
import Cedar.Thm.Validation.Typechecker.Pred.Record
import Cedar.Thm.Validation.Typechecker.Pred.Call
import Cedar.Thm.Validation.Typechecker.Pred.And
import Cedar.Thm.Validation.Typechecker.Pred.Or
import Cedar.Thm.Validation.Typechecker.Pred.Ite

/-!
# Predicate type soundness — dispatcher (D-74 option A, Phase 9c)

`type_of_pred_is_sound` : the full predicate analogue of `type_of_is_sound`,
assembled by structural recursion over `PredExpr` from the per-operator arm
lemmas. Each arm is `type_of_pred_<op>_is_sound`; the recursive arms receive the
dispatcher as their induction hypothesis (`TypeOfPredIsSound`). `termination_by
sizeOf p`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_pred_is_sound {p : PredExpr} : TypeOfPredIsSound p := by
  intro itTy it c₁ c₂ env ty request entities hnr hitwf hci h₂ hit h₃
  match p with
  | .item => exact type_of_pred_item_is_sound hit h₃
  | .lit l => exact type_of_pred_lit_is_sound h₃
  | .var v => exact type_of_pred_var_is_sound h₂ h₃
  | .ite x₁ x₂ x₃ =>
    have ih₁ := @type_of_pred_is_sound x₁
    have ih₂ := @type_of_pred_is_sound x₂
    have ih₃ := @type_of_pred_is_sound x₃
    exact type_of_pred_ite_is_sound hnr hitwf hci h₂ hit h₃ ih₁ ih₂ ih₃
  | .and x₁ x₂ =>
    have ih₁ := @type_of_pred_is_sound x₁
    have ih₂ := @type_of_pred_is_sound x₂
    exact type_of_pred_and_is_sound hnr hitwf hci h₂ hit h₃ ih₁ ih₂
  | .or x₁ x₂ =>
    have ih₁ := @type_of_pred_is_sound x₁
    have ih₂ := @type_of_pred_is_sound x₂
    exact type_of_pred_or_is_sound hnr hitwf hci h₂ hit h₃ ih₁ ih₂
  | .unaryApp op x₁ =>
    have ih := @type_of_pred_is_sound x₁
    exact type_of_pred_unaryApp_is_sound hnr hitwf hci h₂ hit h₃ ih
  | .binaryApp op x₁ x₂ =>
    have ih₁ := @type_of_pred_is_sound x₁
    have ih₂ := @type_of_pred_is_sound x₂
    exact type_of_pred_binaryApp_is_sound hnr hitwf hci h₂ hit h₃ ih₁ ih₂
  | .hasAttr x₁ a =>
    have ih := @type_of_pred_is_sound x₁
    exact type_of_pred_hasAttr_is_sound hnr hitwf hci h₂ hit h₃ ih
  | .extHasAttr x₁ a attrs =>
    have ih := @type_of_pred_is_sound x₁
    exact type_of_pred_extHasAttr_is_sound hnr hitwf hci h₂ hit h₃ ih
  | .getAttr x₁ a =>
    have ih := @type_of_pred_is_sound x₁
    exact type_of_pred_getAttr_is_sound hnr hitwf hci h₂ hit h₃ ih
  | .record axs =>
    have ih : ∀ a x, (a, x) ∈ axs → TypeOfPredIsSound x := by
      intro a x hᵢ
      have _ : sizeOf x < 1 + sizeOf axs := by
        have := List.sizeOf_snd_lt_sizeOf_list hᵢ
        omega
      exact @type_of_pred_is_sound x
    exact type_of_pred_record_is_sound hnr hitwf hci h₂ hit h₃ ih
  | .call xfn xs =>
    have ih : ∀ x, x ∈ xs → TypeOfPredIsSound x := by
      intro x _
      exact @type_of_pred_is_sound x
    exact type_of_pred_call_is_sound hci h₂ hit h₃ ih
termination_by sizeOf p

end Cedar.Thm
