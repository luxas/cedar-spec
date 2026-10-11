/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.HasAttr

/-!
# Predicate type soundness — `.hasAttr` arm (Phase 9c, D-97 option b)

Full mirror of `type_of_hasAttr_is_sound` (`Typechecker/HasAttr.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the STRONG form (D-97): it carries the
predicate capability invariant `CapabilitiesInvariantPred c₁ …` and concludes the
guarded production of `CapabilitiesInvariantPred c₂`.

`typeOfPred (.hasAttr x₁ a)` peels to `typeOfPred x₁` then the SAME `typeOfHasAttr
ty₁ x₁.toCapKey a` helper the expression typechecker uses (NOTE: the capability
key is `x₁.toCapKey`, not `x₁.toExpr`), and `evaluatePred (.hasAttr x₁ a)` is
`evaluatePred x₁ >>= hasAttr · a es`.

The capability-`.tt` case — unprovable under the earlier WEAK statement — is now
provable: `typeOfHasAttr` returns `.tt` because `(x₁.toCapKey, .attr a) ∈ c₁`, and
`hci.1 x₁.toCapKey a <mem> x₁ rfl : EvaluatesToPred (.hasAttr x₁ a) it … true`
gives exactly `evaluatePred (.hasAttr x₁ a) it = .ok true` (or an error), which
forces the returned bool `b = true`, closing the `.tt` instance.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
`hasAttrInRecord` only ever produces a `.bool _` result type (pred-file copy of
the fact used by the Expr twin's inversion).
-/
theorem hasAttrInRecord_result_is_bool {rty : RecordType} {x : Expr} {a : Attr}
    {c c' : Capabilities} {kn : Bool} {ty' : CedarType}
    (h : hasAttrInRecord rty x a c kn = Except.ok (ty', c')) :
    ∃ bty, ty' = .bool bty := by
  simp only [hasAttrInRecord, Validation.ok] at h
  split at h
  · split at h <;>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      exact ⟨_, h.left.symm⟩
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨_, h.left.symm⟩

/--
Inversion of `typeOfPred (.hasAttr x₁ a)` (pred twin of
`type_of_hasAttr_inversion`). Full mirror: tracks the output-capability shape
(empty or the singleton keyed by `x₁.toCapKey`) and the operand record/entity
disjunction.
-/
theorem type_of_pred_hasAttr_inversion {x₁ : PredExpr} {a : Attr} {itTy : CedarType}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h₁ : typeOfPred (.hasAttr x₁ a) itTy c₁ env = Except.ok (tx, c₂)) :
    (c₂ = ∅ ∨ c₂ = Capabilities.singleton x₁.toCapKey (.attr a)) ∧
    (∃ bty, tx.typeOf = .bool bty) ∧
    ∃ tx₁ c₁',
      typeOfPred x₁ itTy c₁ env = .ok (tx₁, c₁') ∧
      tx = .hasAttr tx₁ a tx.typeOf ∧
      ((∃ ety, tx₁.typeOf = .entity ety) ∨
       (∃ rty, tx₁.typeOf = .record rty))
:= by
  simp only [typeOfPred] at h₁
  cases h₂ : typeOfPred x₁ itTy c₁ env <;>
    simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp only [typeOfHasAttr, bind, Except.bind] at h₁
    split at h₁ <;> try contradiction
    · split at h₁ <;> simp [ok] at h₁
      rename_i heq₁ _ _ heq₂
      obtain ⟨htx, hc⟩ := h₁
      have hbty := hasAttrInRecord_result_is_bool heq₂
      refine ⟨?_, ?_, ty₁, c₁', rfl, ?_, Or.inr ⟨_, heq₁⟩⟩
      · subst hc
        exact hasAttrInRecord_has_empty_or_singleton_capabilities heq₂
      · obtain ⟨bty, hbty⟩ := hbty
        exact ⟨bty, by simp only [← htx, TypedExpr.typeOf, hbty]⟩
      · simp only [← htx, TypedExpr.typeOf]
    · split at h₁
      · split at h₁ <;> simp [ok] at h₁
        rename_i heq₁ _ _ _ _ _ heq₃
        obtain ⟨htx, hc⟩ := h₁
        have hbty := hasAttrInRecord_result_is_bool heq₃
        refine ⟨?_, ?_, ty₁, c₁', rfl, ?_, Or.inl ⟨_, heq₁⟩⟩
        · subst hc
          exact hasAttrInRecord_has_empty_or_singleton_capabilities heq₃
        · obtain ⟨bty, hbty⟩ := hbty
          exact ⟨bty, by simp only [← htx, TypedExpr.typeOf, hbty]⟩
        · simp only [← htx, TypedExpr.typeOf]
      · split at h₁ <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h₁
        rename_i heq₁ _ _ heq₃
        refine ⟨Or.inl h₁.right.symm, ⟨.ff, ?_⟩, ty₁, c₁', rfl, ?_, Or.inl ⟨_, heq₁⟩⟩ <;>
          simp only [← h₁.left, TypedExpr.typeOf]

/--
Value half for the record case (pred twin of
`type_of_hasAttr_is_sound_for_records`). The `.tt` capability subcase is
discharged with `hci.1 x₁.toCapKey a h₇ x₁ rfl` + `evaluatePred`.
-/
theorem type_of_pred_hasAttr_is_sound_for_records {x₁ : PredExpr} {a : Attr} {itTy : CedarType}
    {c₁ c₁' c₂ : Capabilities} {env : TypeEnv} {rty : RecordType} {it : Value}
    {request : Request} {entities : Entities} {v₁ : Value} {ty : TypedExpr}
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (hofk : PredExpr.ofCapKey x₁.toCapKey = x₁)
    (h₂ : typeOfPred (.hasAttr x₁ a) itTy c₁ env = Except.ok (ty, c₂))
    (h₃ : (typeOfPred x₁ itTy c₁ env).typeOf = Except.ok (CedarType.record rty, c₁'))
    (h₄ : evaluatePred x₁ it request entities = Except.ok v₁)
    (h₅ : InstanceOfType env v₁ (CedarType.record rty)) :
    ∃ v,
    (hasAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
     hasAttr v₁ a entities = Except.error Error.extensionError ∨
     hasAttr v₁ a entities = Except.error Error.arithBoundsError ∨
     hasAttr v₁ a entities = Except.ok v) ∧
    InstanceOfType env v ty.typeOf
:= by
  have ⟨r, h₅⟩ := instance_of_record_type_is_record h₅
  subst h₅
  simp [hasAttr, attrsOf]
  split_type_of h₃ ; rename_i h₃ hl₃ _
  simp [typeOfPred, hl₃, h₃, typeOfHasAttr, hasAttrInRecord] at h₂
  split at h₂
  case h_1 =>
    split at h₂ <;> simp [ok] at h₂ <;> simp [←h₂.left]
    case isFalse => exact bool_is_instance_of_anyBool _
    cases h₆ : (Map.contains r a)
    case true => exact true_is_instance_of_tt
    rename_i h₇
    cases h₇
    case inl _ h₇ =>
      -- capability `.tt` case: the predicate capability invariant provides the
      -- hasAttr-true fact over `evaluatePred`, replacing the Expr `h₁.left`.
      have hev := hci.1 x₁.toCapKey a h₇
      rw [hofk] at hev
      simp [EvaluatesToPred, evaluatePred, h₄, hasAttr, attrsOf, h₆] at hev
    case inr h₇ h₈ =>
      simp [Qualified.isRequired] at h₈
      split at h₈ <;> simp at h₈
      have h₉ := required_attribute_is_present h₅ h₇
      simp [←Map.contains_iff_some_find?, h₆] at h₉
  case h_2 =>
    simp [ok] at h₂
    have ⟨h₂, _⟩ := h₂
    simp [←h₂]
    cases h₆ : (Map.contains r a)
    case false => exact false_is_instance_of_ff
    rename_i _ h₇ _ _
    have h₇ := absent_attribute_is_absent h₅ h₇
    simp [Map.contains_iff_some_find?, h₇] at h₆

/--
Value half for the entity case (pred twin of
`type_of_hasAttr_is_sound_for_entities`). The `.tt` capability subcase is
discharged with `hci.1 x₁.toCapKey a h₉ x₁ rfl` + `evaluatePred`.
-/
theorem type_of_pred_hasAttr_is_sound_for_entities {x₁ : PredExpr} {a : Attr} {itTy : CedarType}
    {c₁ c₁' c₂ : Capabilities} {env : TypeEnv} {ety : EntityType} {it : Value}
    {request : Request} {entities : Entities} {v₁ : Value} {ty : TypedExpr}
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (hofk : PredExpr.ofCapKey x₁.toCapKey = x₁)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (h₃ : typeOfPred (.hasAttr x₁ a) itTy c₁ env = Except.ok (ty, c₂))
    (h₄ : (typeOfPred x₁ itTy c₁ env).typeOf = Except.ok (CedarType.entity ety, c₁'))
    (h₅ : evaluatePred x₁ it request entities = Except.ok v₁)
    (h₆ : InstanceOfType env v₁ (CedarType.entity ety)) :
    ∃ v,
    (hasAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
     hasAttr v₁ a entities = Except.error Error.extensionError ∨
     hasAttr v₁ a entities = Except.error Error.arithBoundsError ∨
     hasAttr v₁ a entities = Except.ok v) ∧
     InstanceOfType env v ty.typeOf
:= by
  have ⟨uid, h₆, h₇⟩ := instance_of_entity_type_is_entity h₆
  subst h₆ h₇
  simp [hasAttr, attrsOf]
  split_type_of h₄ ; rename_i h₄ hl₄ _
  simp [typeOfPred, h₄, hl₄, typeOfHasAttr] at h₃
  split at h₃ <;> try simp [err, hasAttrInRecord] at h₃
  rename_i _ rty h₇
  split at h₃
  case h_1 =>
    split at h₃ <;> rcases h₃ with ⟨h₃, _⟩
    case isFalse => exact bool_is_instance_of_anyBool _
    cases h₈ : Map.contains (Entities.attrsOrEmpty entities uid) a
    case true => exact true_is_instance_of_tt
    rename_i _ _ _ _  h₉
    -- capability `.tt` case over `evaluatePred`.
    have hev := hci.1 x₁.toCapKey a h₉
    rw [hofk] at hev
    simp [EvaluatesToPred, evaluatePred, h₅, hasAttr, attrsOf, h₈] at hev
  case h_2 =>
    simp [ok] at h₃
    have ⟨h₃, _⟩ := h₃
    simp [←h₃]
    cases h₈ : Map.contains (Entities.attrsOrEmpty entities uid) a
    case false => exact false_is_instance_of_ff
    rename_i _ _ h₉ _ _
    simp [Entities.attrsOrEmpty] at h₈
    split at h₈
    case h_1 _ _ _ _ _ h₁₀ =>
      have h₁₁ := well_typed_entity_attributes h₂ h₁₀ h₇
      have h₁₂ := absent_attribute_is_absent h₁₁ h₉
      simp [Map.contains_iff_some_find?, h₁₂] at h₈
    case h_2 =>
      rcases (Map.not_contains_of_empty a) with _
      contradiction
  case h_2 =>
    simp [ok] at h₃
    split at h₃ <;> try simp at h₃
    replace ⟨h₃, _⟩ := h₃
    simp [←h₃]
    unfold Entities.attrsOrEmpty
    rename_i _ h₇ _ _
    simp [EntitySchema.attrs?] at h₇
    replace ⟨_, _, h₂⟩ := h₂
    cases h₈ : Map.find? entities uid
    case none => exact false_is_instance_of_ff
    cases h₂.1 uid _ h₈ with
    | inl h₂ =>
      replace ⟨_, h₈, _⟩ := h₂
      rw [h₇] at h₈
      contradiction
    | inr h₂ =>
      simp only [h₂.left]
      exact false_is_instance_of_ff

/--
`.hasAttr` predicate soundness (pred twin of `type_of_hasAttr_is_sound`), STRONG
form (D-97). Carries `CapabilitiesInvariantPred c₁` and concludes the guarded
production of `CapabilitiesInvariantPred c₂`.
-/
theorem type_of_pred_hasAttr_is_sound {x₁ : PredExpr} {a : Attr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (hnr : NoReservedItKey env)
    (hitwf : itTy.WellFormed env)
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.hasAttr x₁ a) itTy c₁ env = Except.ok (ty, c₂))
    (ih : TypeOfPredIsSound x₁) :
    GuardedCapabilitiesInvariantPred (.hasAttr x₁ a) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.hasAttr x₁ a) it request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₅, ⟨bty, hbtyeq⟩, ty₁, c₁', hty₁, hty, h₄⟩ := type_of_pred_hasAttr_inversion h₃
  -- `x₁` has no reserved `it` access, so `ofCapKey x₁.toCapKey = x₁`.
  have hx1nr : x₁.NoReservedItAccess = true := type_of_pred_implies_no_reserved hnr hty₁
  have hofk : PredExpr.ofCapKey x₁.toCapKey = x₁ := ofCapKey_toCapKey hx1nr
  apply And.intro
  case left =>
    -- Guarded capabilities: output caps are empty or the singleton keyed by
    -- `x₁.toCapKey`; under the hasAttr-true guard the singleton is invariant.
    intro hguard
    rcases h₅ with h₅ | h₅ <;> subst h₅
    · exact empty_capabilities_invariant_pred it request entities
    · constructor
      · intro e k hmem
        simp only [Capabilities.singleton, List.mem_singleton, Prod.mk.injEq, Key.attr.injEq] at hmem
        obtain ⟨he, hk⟩ := hmem
        subst he; subst hk
        -- Producer field (ofCapKey form): must show
        -- `EvaluatesToPred (.hasAttr (ofCapKey x₁.toCapKey) a) it … true`.
        -- `ofCapKey x₁.toCapKey = x₁`, so this is exactly the guard.
        rw [hofk]
        exact Or.inr hguard
      · intro e k hmem
        simp only [Capabilities.singleton, List.mem_singleton, Prod.mk.injEq, reduceCtorEq,
          and_false] at hmem
  case right =>
    rcases h₄ with ⟨ety, h₄⟩ | ⟨rty, h₄⟩ <;>
    have ⟨_, v₁, h₆, h₇⟩ := ih hnr hitwf hci h₂ hit hty₁ <;>
    simp only [EvaluatesToPred] at h₆ <;>
    rw [h₄] at h₇
    · -- entity operand
      rcases h₆ with ⟨err, h₆⟩ | h₆
      · -- operand errors ⇒ whole predicate errors; result is a bool, inhabited.
        have ⟨v, hv⟩ := @type_is_inhabited_bool env bty
        refine ⟨v, Or.inl ⟨err, ?_⟩, hbtyeq ▸ hv⟩
        simp only [evaluatePred, h₆, Except.bind_err]
      · have h₈ : (typeOfPred x₁ itTy c₁ env).typeOf = Except.ok (CedarType.entity ety, c₁') := by
          simp [h₄, hty₁, ResultType.typeOf, Except.map]
        have ⟨v, hd, hi⟩ := type_of_pred_hasAttr_is_sound_for_entities hci hofk h₂ h₃ h₈ h₆ h₇
        refine ⟨v, ?_, hi⟩
        simp only [EvaluatesToPred, evaluatePred, h₆, Except.bind_ok]
        rcases hd with h | h | h | h <;> simp [h]
    · -- record operand
      rcases h₆ with ⟨err, h₆⟩ | h₆
      · have ⟨v, hv⟩ := @type_is_inhabited_bool env bty
        refine ⟨v, Or.inl ⟨err, ?_⟩, hbtyeq ▸ hv⟩
        simp only [evaluatePred, h₆, Except.bind_err]
      · have h₈ : (typeOfPred x₁ itTy c₁ env).typeOf = Except.ok (CedarType.record rty, c₁') := by
          simp [h₄, hty₁, ResultType.typeOf, Except.map]
        have ⟨v, hd, hi⟩ := type_of_pred_hasAttr_is_sound_for_records hci hofk h₃ h₈ h₆ h₇
        refine ⟨v, ?_, hi⟩
        simp only [EvaluatesToPred, evaluatePred, h₆, Except.bind_ok]
        rcases hd with h | h | h | h <;> simp [h]

end Cedar.Thm
