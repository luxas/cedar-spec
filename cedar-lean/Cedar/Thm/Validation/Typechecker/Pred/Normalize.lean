/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred

/-!
# `normalize_evaluatePred` (Phase 9c, M4, D-74 option A / D-73b)

`PredExpr.normalize` folds the dead `.and`/`.or`/`.ite` branches that `typeOfPred`
short-circuited past. This file proves the fold preserves evaluation: for a
predicate that type-checks, `evaluatePred (normalize p …) it = evaluatePred p it`.
Only `.and`/`.or`/`.ite` actually change the term; each fold is justified by
`type_of_pred_is_sound`, which pins the folded-away branch's evaluation to
`false`/`true`-or-error. Every other arm is a structural identity.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- A `.bool .ff`-typed predicate evaluates to `false` or errors. -/
private theorem pred_ff_eval_false_or_err {x : PredExpr} {itTy : CedarType} {it : Value}
    {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
    (hnr : NoReservedItKey env) (hitwf : itTy.WellFormed env)
    (hci : CapabilitiesInvariantPred c it request entities)
    (hwfenv : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (hty : typeOfPred x itTy c env = Except.ok (tx, c'))
    (hff : tx.typeOf = .bool .ff) :
    evaluatePred x it request entities = .ok (.prim (.bool false)) ∨
    ∃ err, evaluatePred x it request entities = .error err := by
  have ⟨_, v, hev, hinst⟩ := type_of_pred_is_sound hnr hitwf hci hwfenv hit hty
  rw [hff] at hinst
  have hfalse := instance_of_ff_is_false hinst
  rcases hev with ⟨err, hev⟩ | hev
  · exact Or.inr ⟨err, hev⟩
  · subst hfalse; exact Or.inl hev

/-- A `.bool .tt`-typed predicate evaluates to `true` or errors. -/
private theorem pred_tt_eval_true_or_err {x : PredExpr} {itTy : CedarType} {it : Value}
    {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
    (hnr : NoReservedItKey env) (hitwf : itTy.WellFormed env)
    (hci : CapabilitiesInvariantPred c it request entities)
    (hwfenv : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (hty : typeOfPred x itTy c env = Except.ok (tx, c'))
    (htt : tx.typeOf = .bool .tt) :
    evaluatePred x it request entities = .ok (.prim (.bool true)) ∨
    ∃ err, evaluatePred x it request entities = .error err := by
  have ⟨_, v, hev, hinst⟩ := type_of_pred_is_sound hnr hitwf hci hwfenv hit hty
  rw [htt] at hinst
  have htrue := instance_of_tt_is_true hinst
  rcases hev with ⟨err, hev⟩ | hev
  · exact Or.inr ⟨err, hev⟩
  · subst htrue; exact Or.inl hev

/--
**M4.** `PredExpr.normalize` preserves evaluation on a type-checking predicate.
Structural recursion on `p`; the `.and`/`.or`/`.ite` folds use the ff/tt
evaluation lemmas above, every other arm recurses.
-/
theorem normalize_evaluatePred {p : PredExpr} {itTy : CedarType} {it : Value}
    {c : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
    (hnr : NoReservedItKey env) (hitwf : itTy.WellFormed env)
    (hci : CapabilitiesInvariantPred c it request entities)
    (hwfenv : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (hok : ∃ tx c', typeOfPred p itTy c env = Except.ok (tx, c')) :
    evaluatePred (PredExpr.normalize p itTy c env) it request entities =
    evaluatePred p it request entities := by
  match p with
  | .item => simp only [PredExpr.normalize]
  | .lit _ => simp only [PredExpr.normalize]
  | .var _ => simp only [PredExpr.normalize]
  | .unaryApp op x =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hx : typeOfPred x itTy c env <;> simp only [hx, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r
    have ihx := normalize_evaluatePred (p := x) hnr hitwf hci hwfenv hit ⟨r.1, r.2, hx⟩
    simp only [PredExpr.normalize, evaluatePred, ihx]
  | .getAttr x attr =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hx : typeOfPred x itTy c env <;> simp only [hx, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r
    have ihx := normalize_evaluatePred (p := x) hnr hitwf hci hwfenv hit ⟨r.1, r.2, hx⟩
    simp only [PredExpr.normalize, evaluatePred, ihx]
  | .hasAttr x attr =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hx : typeOfPred x itTy c env <;> simp only [hx, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r
    have ihx := normalize_evaluatePred (p := x) hnr hitwf hci hwfenv hit ⟨r.1, r.2, hx⟩
    simp only [PredExpr.normalize, evaluatePred, ihx]
  | .extHasAttr x attr attrs =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hx : typeOfPred x itTy c env <;> simp only [hx, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r
    have ihx := normalize_evaluatePred (p := x) hnr hitwf hci hwfenv hit ⟨r.1, r.2, hx⟩
    simp only [PredExpr.normalize, evaluatePred, ihx]
  | .binaryApp op x₁ x₂ =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hx₁ : typeOfPred x₁ itTy c env <;> simp only [hx₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₁
    cases hx₂ : typeOfPred x₂ itTy c env <;> simp only [hx₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₂
    have ih₁ := normalize_evaluatePred (p := x₁) hnr hitwf hci hwfenv hit ⟨r₁.1, r₁.2, hx₁⟩
    have ih₂ := normalize_evaluatePred (p := x₂) hnr hitwf hci hwfenv hit ⟨r₂.1, r₂.2, hx₂⟩
    simp only [PredExpr.normalize, evaluatePred, ih₁, ih₂]
  | .record axs =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hm : axs.mapM₂ (λ x => (typeOfPred x.1.snd itTy c env).map (λ (ty, _) => (x.1.fst, ty)))
      <;> simp only [hm, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    simp only [PredExpr.normalize, evaluatePred]
    -- RHS: collapse `mapM₂`/`map₂` wrappers to plain `mapM`/`map` (projection-form bodies).
    rw [show (axs.map₂ (fun x => (x.1.fst, PredExpr.normalize x.1.snd itTy c env)))
          = axs.map (fun p : Attr × PredExpr => (p.fst, PredExpr.normalize p.snd itTy c env))
        from List.map₂_eq_map (fun p : Attr × PredExpr => (p.fst, PredExpr.normalize p.snd itTy c env))]
    rw [List.mapM₂_eq_mapM (fun p : Attr × PredExpr => bindAttr p.fst (evaluatePred p.snd it request entities)),
        List.mapM₂_eq_mapM (fun p : Attr × PredExpr => bindAttr p.fst (evaluatePred p.snd it request entities)),
        List.mapM_map]
    apply congrArg (f := fun r => r >>= fun avs => Except.ok (Value.record (Map.make avs)))
    apply List.mapM_congr
    intro x hx
    obtain ⟨a, e⟩ := x
    have hety : ∃ b, (typeOfPred e itTy c env).map (λ (ty, _) => (a, ty)) = Except.ok b := by
      simp only [List.mapM₂_eq_mapM
        (λ (x : Attr × PredExpr) =>
          Except.map (fun x₁ : (TypedExpr × Capabilities) => (x.fst, x₁.fst)) (typeOfPred x.snd itTy c env))] at hm
      have := List.mapM_ok_implies_all_ok hm (a, e) hx
      obtain ⟨b, _, hb⟩ := this
      exact ⟨b, by simpa only [Except.map] using hb⟩
    obtain ⟨b, hety⟩ := hety
    cases he : typeOfPred e itTy c env <;> simp only [he, Except.map, reduceCtorEq] at hety
    rename_i r
    have := List.sizeOf_snd_lt_sizeOf_list hx
    have ihe := normalize_evaluatePred (p := e) hnr hitwf hci hwfenv hit ⟨r.1, r.2, he⟩
    simp only [Function.comp_apply, bindAttr, ihe]
  | .call f xs =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hm : xs.mapM₁ (λ x => justType (typeOfPred x.1 itTy c env))
      <;> simp only [hm, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    simp only [PredExpr.normalize, evaluatePred]
    rw [List.map₁_eq_map (fun p : PredExpr => PredExpr.normalize p itTy c env),
        List.mapM₁_eq_mapM (fun p : PredExpr => evaluatePred p it request entities),
        List.mapM₁_eq_mapM (fun p : PredExpr => evaluatePred p it request entities),
        List.mapM_map]
    apply congrArg (f := fun r => r >>= fun vs => call f vs)
    apply List.mapM_congr
    intro x hx
    have hety : ∃ b, justType (typeOfPred x itTy c env) = Except.ok b := by
      simp only [List.mapM₁_eq_mapM (λ x => justType (typeOfPred x itTy c env))] at hm
      have := List.mapM_ok_implies_all_ok hm x hx
      obtain ⟨b, _, hb⟩ := this; exact ⟨b, hb⟩
    obtain ⟨b, hety⟩ := hety
    cases he : typeOfPred x itTy c env <;> simp only [he, justType, Except.map, reduceCtorEq] at hety
    rename_i r
    have := List.sizeOf_lt_of_mem hx
    have ihx := normalize_evaluatePred (p := x) hnr hitwf hci hwfenv hit ⟨r.1, r.2, he⟩
    simp only [Function.comp_apply, ihx]
  | .and x₁ x₂ =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hx₁ : typeOfPred x₁ itTy c env <;> simp only [hx₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₁
    cases hx₂ : typeOfPred x₂ itTy (c ∪ r₁.2) env <;> simp only [hx₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₂
    have ih₁ := normalize_evaluatePred (p := x₁) hnr hitwf hci hwfenv hit ⟨r₁.1, r₁.2, hx₁⟩
    have ⟨ig₁, _⟩ := type_of_pred_is_sound hnr hitwf hci hwfenv hit hx₁
    simp only [PredExpr.normalize, hx₁]
    split
    · -- `.bool .ff` left: normalize folds to `x₁'`; eval of `.and` short-circuits.
      rename_i hff
      rcases pred_ff_eval_false_or_err hnr hitwf hci hwfenv hit hx₁ hff with hfe | ⟨err, hfe⟩
      · rw [ih₁]
        conv => rhs; rw [evaluatePred]
        rw [hfe]
        simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Bool.not_false, ↓reduceIte]
      · rw [ih₁]
        conv => rhs; rw [evaluatePred]
        rw [hfe]
        simp only [Result.as, Coe.coe, Value.asBool, Except.bind_err]
    · -- non-ff: `.and x₁' x₂'`. Case on x₁'s evaluation; x₂/x₂' only run when x₁ = true.
      rename_i hnotff
      simp only [evaluatePred, ih₁]
      cases he₁ : evaluatePred x₁ it request entities with
      | error e => simp only [Result.as, Coe.coe, Value.asBool, he₁, Except.bind_err]
      | ok v₁ =>
        -- x₁ is Bool-typed, so v₁ = .prim (.bool b₁)
        have ⟨_, w₁, hw₁, hwi₁⟩ := type_of_pred_is_sound hnr hitwf hci hwfenv hit hx₁
        have ⟨bty₁, hbty₁⟩ : ∃ bty, r₁.1.typeOf = .bool bty := by
          -- `typeOfAnd` succeeds only when the left operand is `.bool _`.
          simp only [typeOfAnd] at hty
          split at hty
          · exact ⟨_, by assumption⟩
          · exact ⟨_, by assumption⟩
          · simp only [err, reduceCtorEq] at hty
        rw [hbty₁] at hwi₁
        simp only [EvaluatesToPred, he₁] at hw₁
        rcases hw₁ with ⟨err, hw₁⟩ | hw₁
        · simp only [reduceCtorEq] at hw₁
        · rw [Except.ok.injEq] at hw₁; subst hw₁
          have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool hwi₁; subst hb₁
          cases b₁
          · -- b₁ = false: `.and` short-circuits to `.ok false`; x₂'/x₂ never run.
            simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Bool.not_false, ↓reduceIte]
          · -- b₁ = true: both reduce to evaluating the right operand; use ih₂.
            have hci₂ : CapabilitiesInvariantPred (c ∪ r₁.2) it request entities :=
              capability_union_invariant_pred hci (ig₁ (by simp only [he₁]))
            have ih₂ := normalize_evaluatePred (p := x₂) hnr hitwf hci₂ hwfenv hit ⟨r₂.1, r₂.2, hx₂⟩
            simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Bool.not_true, ↓reduceIte, ih₂]
  | .or x₁ x₂ =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hx₁ : typeOfPred x₁ itTy c env <;> simp only [hx₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₁
    cases hx₂ : typeOfPred x₂ itTy c env <;> simp only [hx₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₂
    have ih₁ := normalize_evaluatePred (p := x₁) hnr hitwf hci hwfenv hit ⟨r₁.1, r₁.2, hx₁⟩
    have ih₂ := normalize_evaluatePred (p := x₂) hnr hitwf hci hwfenv hit ⟨r₂.1, r₂.2, hx₂⟩
    simp only [PredExpr.normalize, hx₁]
    split
    · -- `.bool .tt` left: normalize folds to `x₁'`; eval of `.or` short-circuits on true.
      rename_i htt
      rcases pred_tt_eval_true_or_err hnr hitwf hci hwfenv hit hx₁ htt with hte | ⟨err, hte⟩
      · simp only [evaluatePred, ih₁, hte, Result.as, Coe.coe, Value.asBool, Except.bind_ok, if_true]
      · simp only [evaluatePred, ih₁, hte, Result.as, Coe.coe, Value.asBool, Except.bind_err]
    · -- non-tt: structural `.or x₁' x₂'` (x₂ typed under `c`, no cap extension).
      simp only [evaluatePred, ih₁, ih₂]
  | .ite x₁ x₂ x₃ =>
    obtain ⟨tx, c', hty⟩ := hok
    simp only [typeOfPred] at hty
    cases hx₁ : typeOfPred x₁ itTy c env <;> simp only [hx₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₁
    cases hx₂ : typeOfPred x₂ itTy (c ∪ r₁.2) env <;> simp only [hx₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₂
    cases hx₃ : typeOfPred x₃ itTy c env <;> simp only [hx₃, Except.bind_err, Except.bind_ok, reduceCtorEq] at hty
    rename_i r₃
    have ih₁ := normalize_evaluatePred (p := x₁) hnr hitwf hci hwfenv hit ⟨r₁.1, r₁.2, hx₁⟩
    have ih₃ := normalize_evaluatePred (p := x₃) hnr hitwf hci hwfenv hit ⟨r₃.1, r₃.2, hx₃⟩
    have ⟨ig₁, _⟩ := type_of_pred_is_sound hnr hitwf hci hwfenv hit hx₁
    simp only [PredExpr.normalize, hx₁]
    -- all three normalize arms are `.ite x₁' <t-arm> <e-arm>`; eval splits on x₁.
    have key : ∀ (t e : PredExpr),
        evaluatePred (PredExpr.ite (PredExpr.normalize x₁ itTy c env) t e) it request entities =
        (do let b ← (evaluatePred x₁ it request entities).as Bool
            if b then evaluatePred t it request entities else evaluatePred e it request entities) := by
      intro t e; simp only [evaluatePred, ih₁]
    have hcond_tt : evaluatePred x₁ it request entities = .ok (.prim (.bool true)) →
        CapabilitiesInvariantPred (c ∪ r₁.2) it request entities := by
      intro hb; exact capability_union_invariant_pred hci (ig₁ hb)
    split
    · -- `.bool .tt` condition: `.ite x₁' t' t'` where t' = normalize x₂ (c∪c₁).
      rename_i htt
      rw [key]
      rcases pred_tt_eval_true_or_err hnr hitwf hci hwfenv hit hx₁ htt with hte | ⟨err, hte⟩
      · have ih₂ := normalize_evaluatePred (p := x₂) hnr hitwf (hcond_tt hte) hwfenv hit ⟨r₂.1, r₂.2, hx₂⟩
        simp only [hte, Result.as, Coe.coe, Value.asBool, Except.bind_ok, if_true, evaluatePred, ih₁, ih₂]
      · simp only [hte, Result.as, Coe.coe, Value.asBool, Except.bind_err, evaluatePred, ih₁]
    · -- `.bool .ff` condition: `.ite x₁' e' e'`.
      rename_i hff
      rw [key]
      rcases pred_ff_eval_false_or_err hnr hitwf hci hwfenv hit hx₁ hff with hfe | ⟨err, hfe⟩
      · simp only [hfe, Result.as, Coe.coe, Value.asBool, Except.bind_ok, Bool.false_eq_true,
          if_false, evaluatePred, ih₁, ih₃]
      · simp only [hfe, Result.as, Coe.coe, Value.asBool, Except.bind_err, evaluatePred, ih₁]
    · -- general condition: `.ite x₁' t' e'`, both branches kept.
      rw [key]
      conv => rhs; rw [evaluatePred]
      cases he₁ : evaluatePred x₁ it request entities with
      | error e => simp only [Result.as, Coe.coe, Value.asBool, he₁, Except.bind_err]
      | ok v₁ =>
        have ⟨_, w₁, hw₁, hwi₁⟩ := type_of_pred_is_sound hnr hitwf hci hwfenv hit hx₁
        simp only [EvaluatesToPred, he₁] at hw₁
        rcases hw₁ with ⟨err, hw₁⟩ | hw₁
        · simp only [reduceCtorEq] at hw₁
        · rw [Except.ok.injEq] at hw₁; subst hw₁
          -- need v₁ Bool; from the general (non-tt/ff) branch, condition type is bool anyBool
          have ⟨bty₁, hbty₁⟩ : ∃ bty, r₁.1.typeOf = .bool bty := by
            simp only [typeOfIf] at hty
            split at hty
            · exact ⟨_, by assumption⟩
            · exact ⟨_, by assumption⟩
            · exact ⟨_, by assumption⟩
            · simp only [err, reduceCtorEq] at hty
          rw [hbty₁] at hwi₁
          have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool hwi₁; subst hb₁
          cases b₁
          · simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Bool.false_eq_true,
              ↓reduceIte, ih₃]
          · have ih₂ := normalize_evaluatePred (p := x₂) hnr hitwf (hcond_tt he₁) hwfenv hit ⟨r₂.1, r₂.2, hx₂⟩
            simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, ↓reduceIte, ih₂]
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals (first | (have := List.sizeOf_snd_lt_sizeOf_list hx; omega) | (have := List.sizeOf_lt_of_mem hx; omega) | omega)

end Cedar.Thm
