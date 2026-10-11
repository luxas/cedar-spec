/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.GetAttr

/-!
# Predicate type soundness — `.getAttr` arm (Phase 9c, WEAK form D-94)

Mirror of `type_of_getAttr_is_sound` (`Typechecker/GetAttr.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the WEAK form: no capability
invariant, the error side admits ANY error. `typeOfPred (.getAttr x₁ a)` peels to
`typeOfPred x₁` then the SAME `typeOfGetAttr ty₁ x₁.toExpr a c env` helper the
expression typechecker uses, and `evaluatePred (.getAttr x₁ a)` is
`evaluatePred x₁ >>= getAttr · a es`.

Key simplification vs the Expr proof: weak soundness admits any error, so the
attribute-missing case is discharged as an error instead of being ruled out by
`capability_implies_record_attribute` / `capability_implies_entity_attribute`.
Only the attribute-present case needs a type fact, reused verbatim from the Expr
proof (`instance_of_attribute_type`, `well_typed_entity_attributes`,
`instance_of_record_type_is_record`, `instance_of_entity_type_is_entity`). The
error branches still need an inhabitant of the returned type, supplied by
`type_is_inhabited` on the attribute type's well-formedness (derived from the
schema for the entity receiver, and from the sub-expression's record type for the
record receiver).
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Inversion of `typeOfPred (.getAttr x₁ a)` (pred twin of
`type_of_getAttr_inversion`). Keeps `x₁.toExpr` where `typeOfGetAttr` needs the
underlying `Expr` for its (weak-form unused) capability lookup.
-/
theorem type_of_pred_getAttr_inversion {x₁ : PredExpr} {a : Attr} {itTy : CedarType}
  {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOfPred (PredExpr.getAttr x₁ a) itTy c₁ env = Except.ok (tx, c₂)) :
  c₂ = ∅ ∧
  ∃ tx₁ c₁',
    typeOfPred x₁ itTy c₁ env = .ok (tx₁, c₁') ∧
    tx = .getAttr tx₁ a tx.typeOf ∧
      ((∃ ety, tx₁.typeOf = .entity ety) ∨
       (∃ rty, tx₁.typeOf = .record rty))
:= by
  simp [typeOfPred] at h₁
  cases h₂ : typeOfPred x₁ itTy c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfGetAttr, bind, Except.bind] at h₁
    split at h₁ <;> try contradiction
    · simp only [List.empty_eq, Except.ok.injEq, Prod.mk.injEq, exists_and_right, exists_and_left,
      exists_eq', and_true, exists_eq_left']
      split at h₁ <;> simp [ok] at h₁
      rename_i heq₁ _ _ heq₂
      simp [heq₁, ← h₁]
      simp [TypedExpr.typeOf]
      apply getAttrInRecord_has_empty_capabilities heq₂
    · simp only [List.empty_eq, Except.ok.injEq, Prod.mk.injEq, exists_and_right]
      split at h₁ <;> try simp [err] at h₁
      split at h₁ <;> simp [ok] at h₁
      rename_i heq₁ _ _ _ _ _ heq₃
      simp [heq₁, ← h₁]
      simp [TypedExpr.typeOf]
      apply getAttrInRecord_has_empty_capabilities heq₃

/--
`.getAttr` predicate soundness — record receiver (weak form). Mirrors
`type_of_getAttr_is_sound_for_records`, but the attr-missing case is an admitted
error with an inhabitant of the attribute type (`hwfrty` gives its
well-formedness). The attr-present case is verbatim.
-/
theorem type_of_pred_getAttr_is_sound_for_records {a : Attr} {c₁ : Capabilities}
  {env : TypeEnv} {rty : RecordType} {entities : Entities} {v₁ : Value} {tx₁ ty : TypedExpr}
  (hwf : env.WellFormed)
  (h₂ : typeOfGetAttr tx₁ e a c₁ env = Except.ok (ty, ∅))
  (h₃ : tx₁.typeOf = CedarType.record rty)
  (hwfrty : CedarType.WellFormed env (.record rty))
  (h₅ : InstanceOfType env v₁ (CedarType.record rty)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.error Error.attrDoesNotExist ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType env v ty.typeOf
:= by
  have ⟨r, h₆⟩ := instance_of_record_type_is_record h₅
  subst h₆
  simp only [getAttr, attrsOf, Except.bind_ok, Map.findOrErr]
  simp only [typeOfGetAttr, h₃, getAttrInRecord, List.empty_eq, bind, Except.bind] at h₂
  -- resolve the attribute lookup in the record type
  cases hfind : rty.find? a with
  | none =>
    simp only [hfind, Validation.err, reduceCtorEq] at h₂
  | some qty =>
    -- the attribute type is well-formed, giving an inhabitant for error branches
    have hwfaty : CedarType.WellFormed env qty.getType :=
      qty_wf_implies_type_of_wf (wf_record_implies_wf_attr hwfrty hfind)
    cases hq : qty with
    | required aty =>
      simp only [hfind, hq, Validation.ok, Except.ok.injEq] at h₂
      -- ty = .getAttr tx₁ a aty, so ty.typeOf = aty = qty.getType
      have htyty : ty.typeOf = aty := by simp only [← h₂, TypedExpr.typeOf]
      have hinh : ∃ v, InstanceOfType env v ty.typeOf := by
        rw [htyty]; exact type_is_inhabited hwf (by simpa [hq, Qualified.getType] using hwfaty)
      cases h₈ : Map.find? r a with
      | none =>
        have ⟨w, hw⟩ := hinh
        exact ⟨w, by simp only [h₈]; tauto, hw⟩
      | some vₐ =>
        refine ⟨vₐ, by simp only [h₈]; tauto, ?_⟩
        rw [htyty]
        exact instance_of_attribute_type h₅ hfind (by simp [hq, Qualified.getType]) h₈
    | optional aty =>
      simp only [hfind, hq] at h₂
      split at h₂ <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, reduceCtorEq] at h₂
      have htyty : ty.typeOf = aty := by simp only [← h₂, TypedExpr.typeOf]
      have hinh : ∃ v, InstanceOfType env v ty.typeOf := by
        rw [htyty]; exact type_is_inhabited hwf (by simpa [hq, Qualified.getType] using hwfaty)
      cases h₈ : Map.find? r a with
      | none =>
        have ⟨w, hw⟩ := hinh
        exact ⟨w, by simp only [h₈]; tauto, hw⟩
      | some vₐ =>
        refine ⟨vₐ, by simp only [h₈]; tauto, ?_⟩
        rw [htyty]
        exact instance_of_attribute_type h₅ hfind (by simp [hq, Qualified.getType]) h₈

/--
`.getAttr` predicate soundness — entity receiver (weak form). Mirrors
`type_of_getAttr_is_sound_for_entities`, but the entity-missing / attr-missing
cases are admitted errors with an inhabitant of the returned type (from the
schema), and the attr-present case reuses `well_typed_entity_attributes` +
`instance_of_attribute_type`.
-/
theorem type_of_pred_getAttr_is_sound_for_entities {a : Attr} {c₁ : Capabilities}
  {env : TypeEnv} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value}
  {tx₁ ty : TypedExpr}
  (hwfenv : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOfGetAttr tx₁ e a c₁ env = Except.ok (ty, ∅))
  (h₄ : tx₁.typeOf = CedarType.entity ety)
  (h₆ : InstanceOfType env v₁ (CedarType.entity ety)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.error Error.attrDoesNotExist ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType env v ty.typeOf
:= by
  have hwf := hwfenv.1
  have ⟨uid, h₇, h₈⟩ := instance_of_entity_type_is_entity h₆
  subst h₈
  simp only [getAttr, attrsOf, Entities.attrs, Except.bind_ok, Map.findOrErr]
  -- schema attrs for ety; needed both for the inhabitant and the present case
  simp only [typeOfGetAttr, h₄, bind, Except.bind] at h₃
  split at h₃ <;> try (simp only [Validation.err, reduceCtorEq] at h₃)
  rename_i rty hattrs
  have hwfrty : CedarType.WellFormed env (.record rty) := wf_env_implies_wf_attrs hwf hattrs
  simp only [getAttrInRecord, List.empty_eq] at h₃
  have hinh : ∃ v, InstanceOfType env v ty.typeOf := by
    split at h₃ <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, Prod.mk.injEq,
      reduceCtorEq] at h₃
    all_goals (
      first
      | (split at h₃ <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, Prod.mk.injEq,
          reduceCtorEq] at h₃)
      | skip)
    all_goals (
      rename_i hfind _
      apply type_is_inhabited hwf
      simp only [← h₃.1, TypedExpr.typeOf]
      apply qty_wf_implies_type_of_wf
      exact wf_record_implies_wf_attr hwfrty hfind )
  cases h₈ : Map.find? entities uid
  case none =>
    -- entity not found ⇒ entityDoesNotExist
    have ⟨w, hw⟩ := hinh
    exact ⟨w, by simp only [h₈, Except.bind_err, Except.error.injEq, true_or], hw⟩
  case some d =>
    subst h₇
    simp only [Except.bind_ok]
    have hdattrs : InstanceOfType env d.attrs (.record rty) :=
      well_typed_entity_attributes hwfenv h₈ hattrs
    cases h₉ : Map.find? d.attrs a
    case none =>
      have ⟨w, hw⟩ := hinh
      exact ⟨w, by simp only [h₉, Except.error.injEq, reduceCtorEq, or_true, true_or]; tauto, hw⟩
    case some vₐ =>
      simp only [Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
      split at h₃ <;> simp only [Validation.ok, Validation.err, reduceCtorEq] at h₃
      rename_i hfind
      split at h₃ <;> try simp only [reduceCtorEq] at h₃
      case h_1 _ _ hreq =>
        cases h₃; subst ty
        apply instance_of_attribute_type hdattrs hreq (by simp only [Qualified.getType, TypedExpr.typeOf]) h₉
      case h_2 _ _ hopt =>
        split at h₃ <;> simp only [Validation.ok, Validation.err, reduceCtorEq] at h₃
        cases h₃; subst ty
        apply instance_of_attribute_type hdattrs hopt (by simp only [Qualified.getType, TypedExpr.typeOf]) h₉

/--
`.getAttr` predicate soundness (pred twin of `type_of_getAttr_is_sound`), WEAK
form.
-/
theorem type_of_pred_getAttr_is_sound {x1 : PredExpr} {a : Attr}
  {itTy it c1 c2 env ty request entities}
  (h2 : InstanceOfWellFormedEnvironment request entities env)
  (hit : InstanceOfType env it itTy)
  (h3 : typeOfPred (PredExpr.getAttr x1 a) itTy c1 env = Except.ok (ty, c2))
  (ih : TypeOfPredIsSound x1) :
  ∃ v, EvaluatesToPred (PredExpr.getAttr x1 a) it request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h5, tx₁, c1', h4, h6, h7⟩ := type_of_pred_getAttr_inversion h3
  subst h5
  have ⟨v₁, hev₁, hinst₁⟩ := ih h2 hit h4
  simp only [EvaluatesToPred, evaluatePred] at hev₁ ⊢
  -- re-expose typeOfGetAttr equation on x1.toExpr
  have h3' : typeOfGetAttr tx₁ x1.toExpr a c1 env = Except.ok (ty, ∅) := by
    simp only [typeOfPred, h4, Except.bind_ok] at h3; exact h3
  rcases h7 with ⟨ety, h7⟩ | ⟨rty, h7⟩
  · have hinst₁' : InstanceOfType env v₁ (CedarType.entity ety) := h7 ▸ hinst₁
    rcases hev₁ with ⟨err, hev₁⟩ | hev₁
    · have ⟨w, hd, hw⟩ := type_of_pred_getAttr_is_sound_for_entities (e := x1.toExpr)
        h2 h3' h7 hinst₁'
      exact ⟨w, Or.inl ⟨err, by simp only [hev₁, Except.bind_err]⟩, hw⟩
    · have ⟨w, hd, hw⟩ := type_of_pred_getAttr_is_sound_for_entities (e := x1.toExpr)
        h2 h3' h7 hinst₁'
      refine ⟨w, ?_, hw⟩
      simp only [hev₁, Except.bind_ok]
      rcases hd with hd | hd | hd | hd | hd <;> simp only [hd, Except.error.injEq, Except.ok.injEq]
      <;> first | (exact Or.inl ⟨_, rfl⟩) | (exact Or.inr rfl)
  · have hinst₁' : InstanceOfType env v₁ (CedarType.record rty) := h7 ▸ hinst₁
    have hwfrty : CedarType.WellFormed env (.record rty) := by
      -- The record receiver's record type is `tx₁.typeOf`, the output type of
      -- `typeOfPred x1`.  Its well-formedness is the general pred-output-type-WF
      -- fact, NOT yet available: the Expr route via `TypedExpr.WellTyped`
      -- (`typechecked_has_well_formed_type`) is unavailable because `.item` types
      -- to `.var .principal itTy`, which is `TypedExpr.WellTyped` only when `itTy`
      -- is the request principal type; a direct induction needs an
      -- `itTy.WellFormed env` hypothesis this weak statement does not carry
      -- (D-95-adjacent).  The entity receiver below is fully discharged from the
      -- schema; this record receiver's type WF is the only open obligation.
      have hpwt : PredExpr.WellTyped env x1 := typeOfPred_implies_wellTyped h4
      -- Remaining goal: `CedarType.WellFormed env (.record rty)`.  Left OPEN
      -- (red, no `sorry`): needs pred-output-type-WF infrastructure.
      skip
    rcases hev₁ with ⟨err, hev₁⟩ | hev₁
    · have ⟨w, hd, hw⟩ := type_of_pred_getAttr_is_sound_for_records (e := x1.toExpr)
        h2.1 h3' h7 hwfrty hinst₁'
      exact ⟨w, Or.inl ⟨err, by simp only [hev₁, Except.bind_err]⟩, hw⟩
    · have ⟨w, hd, hw⟩ := type_of_pred_getAttr_is_sound_for_records (e := x1.toExpr)
        h2.1 h3' h7 hwfrty hinst₁'
      refine ⟨w, ?_, hw⟩
      simp only [hev₁, Except.bind_ok]
      rcases hd with hd | hd | hd | hd | hd <;> simp only [hd, Except.error.injEq, Except.ok.injEq]
      <;> first | (exact Or.inl ⟨_, rfl⟩) | (exact Or.inr rfl)

end Cedar.Thm
