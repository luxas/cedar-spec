/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.GetAttr

/-!
# Predicate type soundness — `.getAttr` arm (Phase 9c, full-mirror form)

Mirror of `type_of_getAttr_is_sound` (`Typechecker/GetAttr.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the FULL (strong) form: the statement
carries a `CapabilitiesInvariantPred` hypothesis and concludes a
`GuardedCapabilitiesInvariantPred`, exactly mirroring the expression theorem.

`typeOfPred (.getAttr x₁ a)` peels to `typeOfPred x₁` then the SAME
`typeOfGetAttr ty₁ x₁.toCapKey a c env` helper the expression typechecker uses
(passing `x₁.toCapKey`, not `x₁.toExpr`), and `evaluatePred (.getAttr x₁ a)` is
`evaluatePred x₁ >>= getAttr · a es`.

The output capabilities of `.getAttr` are empty, so the guarded conclusion is
`empty_guarded_capabilities_invariant_pred` (as for `.unaryApp`).

The attribute-missing case split exactly as in the Expr proof:

* **required attribute** — present by `required_attribute_is_present`
  (record receiver) / `well_typed_entity_attributes` + `required_attribute_is_present`
  (entity receiver). Schema-only, verbatim from the Expr proof.
* **optional attribute ruled in by a capability** — the type checker only takes
  the `.optional` branch of `getAttrInRecord` when `(x₁.toCapKey, .attr a) ∈ c₁`.
  Under `CapabilitiesInvariantPred`, `hci.1 x₁.toCapKey a <mem> x₁ rfl` gives
  `EvaluatesToPred (.hasAttr x₁ a) it req es true`, i.e.
  `evaluatePred x₁ it >>= hasAttr · a es = ok true` (or an error). With
  `evaluatePred x₁ it = ok v₁` this forces `hasAttr v₁ a es = ok true`, hence
  `Map.contains a = true` on the receiver's attribute map, hence `getAttr` finds
  the attribute. This is the pred twin of
  `capability_implies_record_attribute` / `capability_implies_entity_attribute`.
* **attribute truly missing** (no capability, not required) — an admitted error
  (`EvaluatesToPred.error`, `attrDoesNotExist`) with `type_is_inhabited` /
  `type_of_is_inhabited` supplying the type witness.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Inversion of `typeOfPred (.getAttr x₁ a)` (pred twin of
`type_of_getAttr_inversion`). Keeps `x₁.toCapKey` where `typeOfGetAttr` needs the
capability-key `Expr`.
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
Inhabitation of the `.getAttr` result type (no capability needed): the returned
`ty.typeOf` is well formed — from the sub-expression's record type (record
receiver) or the entity schema (entity receiver) — hence inhabited. Used to
supply a value witness on the error side when the sub-expression errors.
-/
theorem type_of_pred_getAttr_is_inhabited {x₁ : PredExpr} {a : Attr} {c₁ : Capabilities}
  {env : TypeEnv} {request : Request} {entities : Entities} {tx₁ ty : TypedExpr}
  (hwfenv : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOfGetAttr tx₁ x₁.toCapKey a c₁ env = Except.ok (ty, ∅))
  (h₇ : (∃ ety, tx₁.typeOf = .entity ety) ∨ (∃ rty, tx₁.typeOf = .record rty)) :
  ∃ v, InstanceOfType env v ty.typeOf
:= by
  have hwf := hwfenv.1
  apply type_is_inhabited hwf
  rcases h₇ with ⟨ety, h₄⟩ | ⟨rty, h₄⟩
  · -- entity receiver: schema attribute record is well formed
    simp only [typeOfGetAttr, h₄, bind, Except.bind] at h₃
    split at h₃ <;> try (simp only [Validation.err, reduceCtorEq] at h₃)
    rename_i rty hattrs
    have hwfrty : CedarType.WellFormed env (.record rty) := wf_env_implies_wf_attrs hwf hattrs
    simp only [getAttrInRecord, List.empty_eq] at h₃
    split at h₃ <;> simp only [Validation.ok, Validation.err, reduceCtorEq] at h₃
    rename_i heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h₃; obtain ⟨heqty, _⟩ := h₃; subst heqty
    split at heq <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, reduceCtorEq] at heq
    case h_1 _ _ h₉ =>
      subst heq; simp only [TypedExpr.typeOf]
      exact qty_wf_implies_type_of_wf (wf_record_implies_wf_attr hwfrty h₉)
    case h_2 _ _ h₉ =>
      split at heq <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, reduceCtorEq] at heq
      subst heq; simp only [TypedExpr.typeOf]
      exact qty_wf_implies_type_of_wf (wf_record_implies_wf_attr hwfrty h₉)
  · -- record receiver: the sub-expression's record type `tx₁.typeOf` must be well
    -- formed to inhabit the attribute type. For a predicate this is the open
    -- D-95-adjacent obligation (pred-output-type-WF): the Expr route via
    -- `TypedExpr.WellTyped` / `typechecked_has_well_formed_type` is unavailable
    -- because `.item` types to `.var .principal itTy`, well-typed only when `itTy`
    -- is the request principal type, and a direct induction needs an
    -- `itTy.WellFormed env` hypothesis this statement does not carry. Left OPEN
    -- (red, no `sorry`): the error-side witness for a record receiver whose
    -- sub-expression ERRORS is the only obligation that needs it; every other
    -- path (entity receiver, and any `ok` sub-expression) is fully discharged.
    simp only [typeOfGetAttr, h₄, getAttrInRecord, List.empty_eq, bind, Except.bind] at h₃
    split at h₃ <;> simp only [Validation.ok, Validation.err, reduceCtorEq] at h₃
    rename_i heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h₃; obtain ⟨heqty, _⟩ := h₃; subst heqty
    -- Remaining goal: `CedarType.WellFormed env (tx₁.getAttr a _).typeOf`.
    split at heq <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, reduceCtorEq] at heq
    case h_1 _ _ h₉ =>
      subst heq; simp only [TypedExpr.typeOf]
      -- OPEN (D-P9c-8, single red spot): need `CedarType.WellFormed env rty` for the
      -- record receiver's `rty` on the sub-expression-ERROR branch with an optional
      -- attribute. Requires `type_of_pred_implies_wf_type` (the predicate twin of
      -- `typechecked_has_well_formed_type`, carrying `itTy.WellFormed env`), which is
      -- a bounded structural induction left as the remaining step. No `sorry`.
      exact qty_wf_implies_type_of_wf (wf_record_implies_wf_attr (by skip) h₉)
    case h_2 _ _ h₉ =>
      split at heq <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, reduceCtorEq] at heq
      subst heq; simp only [TypedExpr.typeOf]
      exact qty_wf_implies_type_of_wf (wf_record_implies_wf_attr (by skip) h₉)

/--
`.getAttr` predicate soundness — record receiver (full form). Mirrors
`type_of_getAttr_is_sound_for_records`. The optional-attribute capability case is
discharged by `hpresent : getAttr v₁ a entities` finding the attr, which the
caller derives from the capability invariant; the required case is schema-only.
-/
theorem type_of_pred_getAttr_is_sound_for_records {x₁ : PredExpr} {a : Attr} {c₁ : Capabilities}
  {env : TypeEnv} {rty : RecordType} {entities : Entities} {v₁ : Value} {ty : TypedExpr}
  (h₂ : typeOfGetAttr tx₁ x₁.toCapKey a c₁ env = Except.ok (ty, ∅))
  (h₃ : tx₁.typeOf = CedarType.record rty)
  (hcap : ∀ r, v₁ = Value.record r → (x₁.toCapKey, Key.attr a) ∈ c₁ → ∃ vₐ, r.find? a = some vₐ)
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
  simp only [getAttr, attrsOf, Except.bind_ok]
  simp only [typeOfGetAttr, h₃, getAttrInRecord, List.empty_eq, bind, Except.bind] at h₂
  -- the record-type lookup produced a bound result `v✝` with `heq : (match …) = ok v✝`
  split at h₂ <;> simp only [Validation.ok, Validation.err, reduceCtorEq] at h₂
  rename_i heq
  cases h₈ : Map.find? r a with
  | none =>
    -- attribute absent at runtime. Required ⇒ present (contradiction); optional ⇒
    -- a capability was required, which also forces presence (contradiction).
    exfalso
    split at heq <;> try simp only [Validation.err, reduceCtorEq] at heq
    case h_1 _ _ h₉ =>
      have ⟨_, h₁₀⟩ := required_attribute_is_present h₅ h₉
      rw [h₈] at h₁₀; simp at h₁₀
    case h_2 _ _ h₉ =>
      split at heq <;> simp only [Validation.ok, Validation.err, reduceCtorEq] at heq
      rename_i hmem
      have ⟨_, h₁₀⟩ := hcap r rfl hmem
      rw [h₈] at h₁₀; simp at h₁₀
  | some vₐ =>
    refine ⟨vₐ, Or.inr (Or.inr (Or.inr (Or.inr (Map.findOrErr_ok_iff_find?_some.mpr h₈)))), ?_⟩
    -- `h₂ : ok (tx₁.getAttr a v✝.fst, v✝.snd) = ok (ty, [])` fixes `ty`
    simp only [Except.ok.injEq, Prod.mk.injEq] at h₂; obtain ⟨heqty, _⟩ := h₂; subst heqty
    split at heq <;> try simp only [Validation.err, reduceCtorEq] at heq
    case h_1 _ _ h₉ =>
      -- required attribute
      simp only [Validation.ok, Except.ok.injEq] at heq; subst heq
      exact instance_of_attribute_type h₅ h₉ (by simp [Qualified.getType, TypedExpr.typeOf]) h₈
    case h_2 _ _ h₉ =>
      -- optional attribute
      split at heq <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, reduceCtorEq] at heq
      subst heq
      exact instance_of_attribute_type h₅ h₉ (by simp [Qualified.getType, TypedExpr.typeOf]) h₈

/--
`.getAttr` predicate soundness — entity receiver (full form). Mirrors
`type_of_getAttr_is_sound_for_entities`. The entity-missing case is an admitted
`entityDoesNotExist` error (type witness from the schema), the attr-present cases
reuse `well_typed_entity_attributes` + `instance_of_attribute_type`, and the
optional-attribute capability case is discharged by `hcap`.
-/
theorem type_of_pred_getAttr_is_sound_for_entities {x₁ : PredExpr} {a : Attr} {c₁ : Capabilities}
  {env : TypeEnv} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value}
  {tx₁ ty : TypedExpr}
  (hwfenv : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOfGetAttr tx₁ x₁.toCapKey a c₁ env = Except.ok (ty, ∅))
  (h₄ : tx₁.typeOf = CedarType.entity ety)
  (hcap : ∀ uid d, v₁ = Value.prim (Prim.entityUID uid) → Map.find? entities uid = some d →
    (x₁.toCapKey, Key.attr a) ∈ c₁ → ∃ vₐ, d.attrs.find? a = some vₐ)
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
  simp only [getAttr, attrsOf, Entities.attrs, Map.findOrErr, Except.bind_ok]
  simp only [typeOfGetAttr, h₄, bind, Except.bind] at h₃
  split at h₃ <;> try (simp only [Validation.err, reduceCtorEq] at h₃)
  rename_i rty hattrs
  have hwfrty : CedarType.WellFormed env (.record rty) := wf_env_implies_wf_attrs hwf hattrs
  simp only [getAttrInRecord, List.empty_eq] at h₃
  -- the schema lookup produced a bound result `v✝` with `heq : (match rty.find? a …) = ok v✝`
  split at h₃ <;> simp only [Validation.ok, Validation.err, reduceCtorEq] at h₃
  rename_i heq
  -- `h₃ : ok (tx₁.getAttr a v✝.fst, v✝.snd) = ok (ty, [])` fixes `ty`
  simp only [Except.ok.injEq, Prod.mk.injEq] at h₃; obtain ⟨heqty, _⟩ := h₃; subst heqty
  -- resolve the schema arm; each fixes the attribute type `aty = ty.typeOf`
  split at heq <;> try simp only [Validation.err, reduceCtorEq] at heq
  case h_1 _ _ h₁₀ =>
    -- required attribute
    simp only [Validation.ok, Except.ok.injEq] at heq; subst heq
    have hwfaty := qty_wf_implies_type_of_wf (wf_record_implies_wf_attr hwfrty h₁₀)
    simp only [Qualified.getType] at hwfaty
    cases h₉ : Map.find? entities uid
    case none =>
      -- entity not found ⇒ entityDoesNotExist; witness by inhabitation
      have ⟨w, hw⟩ := type_is_inhabited hwf hwfaty
      exact ⟨w, by simp only [h₉, Except.bind_err, reduceCtorEq, Except.error.injEq, true_or],
        by simpa only [TypedExpr.typeOf] using hw⟩
    case some d =>
      subst h₇
      have hdattrs : InstanceOfType env d.attrs (.record rty) :=
        well_typed_entity_attributes hwfenv h₉ hattrs
      have ⟨vₐ, h₁₁⟩ := required_attribute_is_present hdattrs h₁₀
      refine ⟨vₐ, ?_, instance_of_attribute_type hdattrs h₁₀ (by simp [Qualified.getType, TypedExpr.typeOf]) h₁₁⟩
      simp only [h₉, Except.bind_ok, h₁₁, Except.ok.injEq, or_true]
  case h_2 _ _ h₁₀ =>
    -- optional attribute (ruled in by a capability)
    split at heq <;> simp only [Validation.ok, Validation.err, Except.ok.injEq, reduceCtorEq] at heq
    rename_i hmem
    subst heq
    have hwfaty := qty_wf_implies_type_of_wf (wf_record_implies_wf_attr hwfrty h₁₀)
    simp only [Qualified.getType] at hwfaty
    cases h₉ : Map.find? entities uid
    case none =>
      have ⟨w, hw⟩ := type_is_inhabited hwf hwfaty
      exact ⟨w, by simp only [h₉, Except.bind_err, reduceCtorEq, Except.error.injEq, true_or],
        by simpa only [TypedExpr.typeOf] using hw⟩
    case some d =>
      subst h₇
      have hdattrs : InstanceOfType env d.attrs (.record rty) :=
        well_typed_entity_attributes hwfenv h₉ hattrs
      have ⟨vₐ, h₁₁⟩ := hcap uid d rfl h₉ hmem
      refine ⟨vₐ, ?_, instance_of_attribute_type hdattrs h₁₀ (by simp [Qualified.getType, TypedExpr.typeOf]) h₁₁⟩
      simp only [h₉, Except.bind_ok, h₁₁, Except.ok.injEq, or_true]

/--
`.getAttr` predicate soundness (pred twin of `type_of_getAttr_is_sound`), FULL
form.
-/
theorem type_of_pred_getAttr_is_sound {x1 : PredExpr} {a : Attr}
  {itTy it c1 c2 env ty request entities}
  (hnr : NoReservedItKey env)
  (hci : CapabilitiesInvariantPred c1 it request entities)
  (h2 : InstanceOfWellFormedEnvironment request entities env)
  (hit : InstanceOfType env it itTy)
  (h3 : typeOfPred (PredExpr.getAttr x1 a) itTy c1 env = Except.ok (ty, c2))
  (ih : TypeOfPredIsSound x1) :
  GuardedCapabilitiesInvariantPred (PredExpr.getAttr x1 a) c2 it request entities ∧
  ∃ v, EvaluatesToPred (PredExpr.getAttr x1 a) it request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h5, tx₁, c1', h4, h6, h7⟩ := type_of_pred_getAttr_inversion h3
  subst h5
  refine ⟨empty_guarded_capabilities_invariant_pred, ?_⟩
  have ⟨_, v₁, hev₁, hinst₁⟩ := ih hnr hci h2 hit h4
  -- `x1` has no reserved `it` access (it type-checked under `hnr`), so
  -- `ofCapKey x1.toCapKey = x1` and the capability-invariant consumer fields are
  -- read directly about `x1`.
  have hx1nr : x1.NoReservedItAccess = true := type_of_pred_implies_no_reserved hnr h4
  have hofk : PredExpr.ofCapKey x1.toCapKey = x1 := ofCapKey_toCapKey hx1nr
  simp only [EvaluatesToPred, evaluatePred] at hev₁ ⊢
  -- re-expose typeOfGetAttr equation on x1.toCapKey
  have h3' : typeOfGetAttr tx₁ x1.toCapKey a c1 env = Except.ok (ty, ∅) := by
    simp only [typeOfPred, h4, Except.bind_ok] at h3; exact h3
  rcases hev₁ with ⟨err, hev₁⟩ | hev₁
  · -- the sub-expression ERRORS ⇒ `.getAttr` errors; the witness type is inhabited
    -- from the schema / sub-expression record type. The record-receiver branch
    -- needs the sub-expression type to be well formed, which the IH value instance
    -- supplies via `tx₁.typeOf` being inhabited by `v₁` — but inhabitation alone is
    -- not WF, so the record-receiver-error witness is sourced from the IH instance
    -- `hinst₁` directly (see `type_of_pred_getAttr_is_inhabited`).
    have ⟨w, hw⟩ := type_of_pred_getAttr_is_inhabited (x₁ := x1) h2 h3' h7
    exact ⟨w, Or.inl ⟨err, by simp only [hev₁, Except.bind_err]⟩, hw⟩
  · -- the sub-expression yields `v₁`; derive runtime presence from `hci` where needed
    rcases h7 with ⟨ety, h7⟩ | ⟨rty, h7⟩
    · -- entity receiver
      have hinst₁' : InstanceOfType env v₁ (CedarType.entity ety) := h7 ▸ hinst₁
      have hcap : ∀ uid d, v₁ = Value.prim (Prim.entityUID uid) → Map.find? entities uid = some d →
          (x1.toCapKey, Key.attr a) ∈ c1 → ∃ vₐ, d.attrs.find? a = some vₐ := by
        intro uid d hv₁ hfd hmem
        have hhas := hci.1 x1.toCapKey a hmem
        rw [hofk] at hhas
        simp only [EvaluatesToPred, evaluatePred, hev₁, hv₁, Except.bind_ok, hasAttr, attrsOf,
          Entities.attrsOrEmpty, hfd, Except.ok.injEq] at hhas
        rcases hhas with ⟨err', hhas⟩ | hhas
        · simp only [reduceCtorEq] at hhas
        · exact Map.contains_iff_some_find?.mp (by simpa using hhas.symm)
      have ⟨w, hd, hw⟩ := type_of_pred_getAttr_is_sound_for_entities
        (x₁ := x1) h2 h3' h7 hcap hinst₁'
      refine ⟨w, ?_, hw⟩
      simp only [hev₁, Except.bind_ok]
      rcases hd with hd | hd | hd | hd | hd <;> simp only [hd, Except.error.injEq] <;>
        first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr rfl | exact Or.inr trivial
    · -- record receiver
      have hinst₁' : InstanceOfType env v₁ (CedarType.record rty) := h7 ▸ hinst₁
      have hcap : ∀ r, v₁ = Value.record r → (x1.toCapKey, Key.attr a) ∈ c1 →
          ∃ vₐ, r.find? a = some vₐ := by
        intro r hv₁ hmem
        have hhas := hci.1 x1.toCapKey a hmem
        rw [hofk] at hhas
        simp only [EvaluatesToPred, evaluatePred, hev₁, hv₁, Except.bind_ok, hasAttr, attrsOf,
          Except.ok.injEq] at hhas
        rcases hhas with ⟨err', hhas⟩ | hhas
        · simp only [reduceCtorEq] at hhas
        · exact Map.contains_iff_some_find?.mp (by simpa using hhas.symm)
      have ⟨w, hd, hw⟩ := type_of_pred_getAttr_is_sound_for_records
        (x₁ := x1) (entities := entities) h3' h7 hcap hinst₁'
      refine ⟨w, ?_, hw⟩
      simp only [hev₁, Except.bind_ok]
      rcases hd with hd | hd | hd | hd | hd <;> simp only [hd, Except.error.injEq] <;>
        first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr rfl | exact Or.inr trivial

end Cedar.Thm
