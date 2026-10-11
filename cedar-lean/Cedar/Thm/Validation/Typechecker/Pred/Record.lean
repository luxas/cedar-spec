/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Record

/-!
# Predicate type soundness — `.record` arm (Phase 9c, M-record)

Mirror of `type_of_record_is_sound` (`Typechecker/Record.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the full-mirror form (D-74 option A):
takes `CapabilitiesInvariantPred c₁ it …` and concludes
`GuardedCapabilitiesInvariantPred (.record axs) c₂ …` AND existence of a value of
the inferred type. The error side admits ANY error (weak soundness, D-94).

`typeOfPred (.record axs)` maps `typeOfPred` over the attr-exprs and builds a
record type via `Map.make`; `evaluatePred (.record axs)` maps `evaluatePred` and
builds the value via `Map.make`. The value-level machinery
(`AttrValueHasAttrType`, `mk_vals_instance_of_mk_types`) is shared verbatim with
the expression proof — it is about `List.Forall₂ AttrValueHasAttrType` and is
independent of HOW the values were produced. Only the inversion and the
"evaluated values instance of the inferred types" bridge need pred twins.

The `.record` arm produces EMPTY output capabilities, so the guarded invariant is
discharged by `empty_guarded_capabilities_invariant_pred`. Because weak soundness
admits any error, the error arm needs only *a* witness of the inferred record
type: an erroring `axs.mapM₂` makes `evaluatePred (.record axs)` error, and
`EvaluatesToPred.error` closes the goal for any witness, which is assembled from
the per-element induction hypotheses (each child type is inhabited by the value
its IH produces).
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
The pred twin of `AttrExprHasAttrType`: the attribute key matches and the
attr-predicate types to the given typed expr (capabilities dropped — weak form).
-/
def AttrPredHasAttrType (itTy : CedarType) (c : Capabilities) (env : TypeEnv) (ax : Attr × PredExpr) (atx : Attr × TypedExpr) : Prop :=
  ax.fst = atx.fst ∧
  ∃ c', (typeOfPred ax.snd itTy c env) = Except.ok (atx.snd, c')

/-- Inversion of the `axs.mapM₂` in `typeOfPred (.record axs)` into a `Forall₂`. -/
theorem type_of_pred_record_inversion_forall {axs : List (Attr × PredExpr)} {itTy : CedarType} {c : Capabilities} {env : TypeEnv} {rtx : List (Attr × TypedExpr)}
  (h₁ : axs.mapM (λ x => (typeOfPred x.snd itTy c env).map (λ (ty, _) => (x.fst, ty))) = Except.ok rtx) :
  List.Forall₂ (AttrPredHasAttrType itTy c env) axs rtx
:= by
  cases axs
  case nil =>
    simp [pure, Except.pure] at h₁ ; subst h₁ ; apply List.Forall₂.nil
  case cons hd tl =>
    cases rtx
    case nil =>
      simp [←List.mapM'_eq_mapM] at h₁
      cases h₂ : Except.map (fun x => (hd.fst, x.fst)) (typeOfPred hd.snd itTy c env) <;> simp [h₂] at h₁
      cases h₃ : List.mapM' (fun x => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOfPred x.snd itTy c env)) tl <;> simp [h₃] at h₁
    case cons hd' tl' =>
      apply List.Forall₂.cons
      {
        simp [←List.mapM'_eq_mapM] at h₁
        cases h₂ : Except.map (fun x => (hd.fst, x.fst)) (typeOfPred hd.snd itTy c env) <;> simp [h₂] at h₁
        cases h₃ : List.mapM' (fun x => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOfPred x.snd itTy c env)) tl <;> simp [h₃] at h₁
        have ⟨hl₁, hr₁⟩ := h₁
        rw [eq_comm] at hl₁ hr₁ ; subst hl₁ hr₁
        simp [Except.map] at h₂
        split at h₂ <;> simp at h₂
        subst h₂
        rename_i _ r _
        simp [AttrPredHasAttrType]
        exists r.snd
      }
      {
        apply type_of_pred_record_inversion_forall
        simp [←List.mapM'_eq_mapM] at *
        cases h₂ : Except.map (fun x => (hd.fst, x.fst)) (typeOfPred hd.snd itTy c env) <;> simp [h₂] at h₁
        cases h₃ : List.mapM' (fun x => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOfPred x.snd itTy c env)) tl <;> simp [h₃] at h₁
        simp only [h₁]
      }

/-- Inversion of `typeOfPred (.record axs)` (pred twin of `type_of_record_inversion`). -/
theorem type_of_pred_record_inversion {axs : List (Attr × PredExpr)} {itTy : CedarType} {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOfPred (.record axs) itTy c env = Except.ok (tx, c')) :
  c' = ∅ ∧
  ∃ (atxs : List (Attr × TypedExpr)),
    tx = .record atxs (.record (Map.make (atxs.map λ (a, tx) => (a, .required tx.typeOf)))) ∧
    List.Forall₂ (AttrPredHasAttrType itTy c env) axs atxs
:= by
  simp [typeOfPred, ok] at h₁
  cases h₂ : axs.mapM₂ fun x => Except.map (fun x_1 => (x.1.fst, x_1.fst)) (typeOfPred x.1.snd itTy c env) <;> simp [h₂] at h₁
  rename_i rty
  simp [h₁]
  exists rty
  simp [←h₁]
  simp [List.mapM₂_eq_mapM λ (x : Attr × PredExpr) => Except.map (fun x₁ : (TypedExpr × Capabilities) => (x.fst, x₁.fst)) (typeOfPred x.snd itTy c env)] at h₂
  exact type_of_pred_record_inversion_forall h₂

/--
Head element: a successfully-bound attr value is an instance of the inferred
required type. Pred twin of `head_of_vals_instance_of_head_of_types`, weak form:
no capability hypothesis.
-/
theorem head_of_pred_vals_instance_of_head_of_types {xhd : Attr × PredExpr} {itTy : CedarType} {it : Value} {c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities} {rhd : Attr × TypedExpr} {vhd : Attr × Value}
  (h₁ : TypeOfPredIsSound xhd.snd)
  (hci : CapabilitiesInvariantPred c₁ it request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (hit : InstanceOfType env it itTy)
  (h₄ : AttrPredHasAttrType itTy c₁ env xhd rhd)
  (h₅ : bindAttr xhd.fst (evaluatePred xhd.snd it request entities) = Except.ok vhd) :
  AttrValueHasAttrType (env := env) vhd (rhd.fst, .required rhd.snd.typeOf)
:= by
  simp [TypeOfPredIsSound] at h₁
  replace ⟨h₄, _, h₆⟩ := h₄ ; rw [←h₄]
  specialize h₁ hci h₂ hit h₆
  have ⟨_, v, h₁, h₇⟩ := h₁
  simp [bindAttr] at h₅
  cases h₈ : evaluatePred xhd.snd it request entities <;> simp [h₈] at h₅
  simp [EvaluatesToPred, h₈] at h₁ ; subst h₁ h₅
  simp [AttrValueHasAttrType, Qualified.getType, h₇]

/--
All successfully-bound attr values are instances of the inferred required types.
Pred twin of `vals_instance_of_types`, weak form.
-/
theorem pred_vals_instance_of_types {axs : List (Attr × PredExpr)} {itTy : CedarType} {it : Value} {c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities} {rtx : List (Attr × TypedExpr)} {avs : List (Attr × Value)}
  (ih : ∀ a x, (a, x) ∈ axs → TypeOfPredIsSound x)
  (hci : CapabilitiesInvariantPred c₁ it request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (hit : InstanceOfType env it itTy)
  (h₃ : List.Forall₂ (AttrPredHasAttrType itTy c₁ env) axs rtx)
  (h₄ : (axs.mapM fun x => bindAttr x.fst (evaluatePred x.snd it request entities)) = Except.ok avs) :
  List.Forall₂ (AttrValueHasAttrType (env := env)) avs (rtx.map λ (a, tx) => (a, .required tx.typeOf))
:= by
  cases h₃
  case nil =>
    simp [←List.mapM'_eq_mapM, pure, Except.pure] at h₄
    subst h₄
    simp [List.map_nil]
  case cons xhd rhd xtl rtl h₅ h₆ =>
    simp [pure, Except.pure] at h₄
    cases h₇ : bindAttr xhd.fst (evaluatePred xhd.snd it request entities) <;> simp [h₇] at h₄
    cases h₈ : List.mapM (fun x => bindAttr x.fst (evaluatePred x.snd it request entities)) xtl <;> simp [h₈] at h₄
    subst h₄
    rename_i vhd vtl
    apply List.Forall₂.cons
    {
      apply head_of_pred_vals_instance_of_head_of_types _ hci h₂ hit h₅ h₇
      apply ih xhd.fst xhd.snd
      simp only [List.mem_cons, true_or]
    }
    {
      apply @pred_vals_instance_of_types xtl itTy it c₁ env request entities rtl vtl _ hci h₂ hit h₆ h₈
      intro a x h₉ ; apply ih a x ; simp [h₉]
    }

/--
Error-branch inhabitant for the `.record` result type, built from the per-element
induction hypotheses rather than a type well-formedness lemma.

Weak soundness still requires *a* witness value of the inferred record type on the
error side (the value is discarded by `EvaluatesToPred.error`, but the existential
`∃ v, … ∧ InstanceOfType env v ty.typeOf` demands one). The record type is
`.record (Map.make (rty.map λ (a,tx) => (a, .required tx.typeOf)))`.

Instead of reconstructing well-formedness of each child type (which would require a
pred twin of `typechecked_has_well_formed_type` in `Pred/Basic.lean`, forbidden
here), we observe that every child already typed (`h₅ : Forall₂ AttrPredHasAttrType
axs rty`) and `TypeOfPredIsSound` therefore *produces* a value instance of each
child type. Collecting those witnesses gives a `Forall₂ AttrValueHasAttrType` over
the required-typed children, which `mk_vals_instance_of_mk_types` turns into a
record instance — exactly the OK-path construction, but with the witnesses coming
from the IHs instead of the actual (erroring) evaluation. This needs no capability
plumbing beyond `hci`, which it threads into each element IH.
-/
theorem type_of_pred_record_type_is_inhabited {axs : List (Attr × PredExpr)} {itTy : CedarType} {it : Value}
    {c₁ : Capabilities} {env : TypeEnv} {rty : List (Attr × TypedExpr)} {request : Request} {entities : Entities}
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (ih : ∀ a x, (a, x) ∈ axs → TypeOfPredIsSound x)
    (h₅ : List.Forall₂ (AttrPredHasAttrType itTy c₁ env) axs rty) :
    ∃ v, InstanceOfType env v (CedarType.record (Map.make (rty.map λ (a, tx) => (a, .required tx.typeOf)))) := by
  -- First collect, by induction on the inversion `Forall₂`, a list of attr values
  -- that is `Forall₂ AttrValueHasAttrType` over the required-typed children.
  suffices h : ∃ avs : List (Attr × Value),
      List.Forall₂ (AttrValueHasAttrType (env := env)) avs (rty.map λ (a, tx) => (a, .required tx.typeOf)) by
    have ⟨avs, hforall⟩ := h
    refine ⟨Value.record (Map.make avs), ?_⟩
    apply mk_vals_instance_of_mk_types
    let p := fun (v : Value) (qty : QualifiedType) => InstanceOfType env v qty.getType
    have h₈ := List.canonicalize_preserves_forallᵥ p avs (rty.map λ (a, tx) => (a, .required tx.typeOf))
    simp [List.Forallᵥ] at h₈
    exact h₈ hforall
  -- The collection, by induction on `h₅`.
  induction h₅
  case nil => exact ⟨[], by simp [List.map_nil]⟩
  case cons xhd rhd xtl rtl h₆ h₇ ihtl =>
    have ⟨vtl, hvtl⟩ := ihtl (by intro a x hx; exact ih a x (by simp [hx]))
    -- the head element types, so its IH gives a value instance of the head type.
    obtain ⟨hkey, c', h₈⟩ := h₆
    have ihhd : TypeOfPredIsSound xhd.snd :=
      ih xhd.fst xhd.snd (by simp only [List.mem_cons, true_or])
    have hsound := ihhd (itTy := itTy) (it := it) (c₁ := c₁) (c₂ := c')
      (env := env) (ty := rhd.snd) (request := request) (entities := entities)
      hci h₂ hit h₈
    obtain ⟨_, vhd, _, hinst⟩ := hsound
    refine ⟨(rhd.fst, vhd) :: vtl, ?_⟩
    simp only [List.map_cons]
    apply List.Forall₂.cons _ hvtl
    simp only [AttrValueHasAttrType, Qualified.getType]
    exact ⟨trivial, hinst⟩

/--
`.record` predicate soundness (pred twin of `type_of_record_is_sound`), full-mirror
form (D-74 option A). The `.record` arm produces EMPTY output capabilities, so the
guarded invariant is discharged by `empty_guarded_capabilities_invariant_pred`.
On success every attr value is an instance of the inferred required type, so the
built record is an instance of the record type; on any error the whole expression
errors, which `EvaluatesToPred.error` admits for any witness, the witness being
drawn from the per-element IHs.
-/
theorem type_of_pred_record_is_sound {axs : List (Attr × PredExpr)} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.record axs) itTy c₁ env = Except.ok (ty, c₂))
    (ih : ∀ a x, (a, x) ∈ axs → TypeOfPredIsSound x) :
    GuardedCapabilitiesInvariantPred (.record axs) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.record axs) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have ⟨hc, rty, h₄, h₅⟩ := type_of_pred_record_inversion h₃
  subst hc h₄
  refine ⟨empty_guarded_capabilities_invariant_pred, ?_⟩
  simp only [TypedExpr.typeOf]
  simp only [EvaluatesToPred, evaluatePred]
  let f := fun (x : Attr × PredExpr) => bindAttr x.fst (evaluatePred x.snd it request entities)
  rw [List.mapM₂_eq_mapM f]
  cases h₆ : (axs.mapM f) <;> simp only [Except.bind_err, Except.bind_ok]
  case error err =>
    have ⟨v, hv⟩ := type_of_pred_record_type_is_inhabited hci h₂ hit ih h₅
    refine ⟨v, Or.inl ⟨err, by simp only [f] at h₆; simp only [h₆]⟩, hv⟩
  case ok avs =>
    refine ⟨Value.record (Map.make avs), Or.inr rfl, ?_⟩
    apply mk_vals_instance_of_mk_types
    let p := fun (v : Value) (qty : QualifiedType) => InstanceOfType env v qty.getType
    have h₇ := pred_vals_instance_of_types ih hci h₂ hit h₅ (by simp only [f] at h₆; exact h₆)
    have h₈ := List.canonicalize_preserves_forallᵥ p avs (rty.map λ (a, tx) => (a, .required tx.typeOf))
    simp [List.Forallᵥ] at h₈
    exact h₈ h₇

end Cedar.Thm
