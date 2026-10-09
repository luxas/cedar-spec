import Cedar.Thm.Data.Map
import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.ofType
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Term.TypeOf

/-!
This file contains the `getAttr` arm lemma for `compilePred_well_typed`
(Phase 5B, D-72 step 3). It is a standalone file; the integrator imports it
into the dispatcher of `compilePred_well_typed`.

It reuses the public lemmas `ofEnv_preserves_entity_attr` (Env/ofEnv.lean),
`wf_app`, `wf_record_get`, `wf_option_get` (Term/WF.lean),
`typeOf_ifSome_option` (Term/TypeOf.lean), and `compilePred_wf`
(Compiler/WF.lean) from the existing tree.

NOTE: it does NOT import `Cedar.Thm.SymCC.Compiler.WellTyped` because that file
is a WIP that is RED at HEAD (unsolved goals at WellTyped.lean:2271, the
recursive arms of `compilePred_well_typed` still building). The one helper this
arm needs from there, `ofRecordType_preserves_attr`, is copied below as a
`private` twin so this file stays green independently.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

/--
twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:ofRecordType_preserves_attr
(copied verbatim because WellTyped.lean is red at HEAD and cannot be imported).

If some attribute exists in a record type, then it should still exist after
applying `TermType.ofRecordType`.
-/
private theorem ofRecordType_preserves_attr
  {rty : RecordType} {attr : Attr} {qty : Qualified CedarType} {ty : CedarType}
  (hattr_exists : Data.Map.find? rty attr = some qty)
  (hattr_ty : qty.getType = ty) :
  ∃ attr_ty : TermType,
    (Data.Map.mk (TermType.ofRecordType rty.1)).find? attr = some attr_ty ∧
    match attr_ty with
    | .option attr_ty' => TermType.ofType ty = attr_ty' ∧ ¬qty.isRequired
    | _ => TermType.ofType ty = attr_ty ∧ qty.isRequired
:= by
  cases rty with | mk rty_1 =>
  induction rty_1
  case nil => simp [Data.Map.find?] at hattr_exists
  case cons head tail ih =>
    have ⟨k, v⟩ := head
    simp only [Data.Map.find?, List.find?, TermType.ofRecordType, Data.Map.toList_mk_id, Bool.not_eq_true]
    simp only [Data.Map.find?, List.find?, Data.Map.toList_mk_id, Bool.not_eq_true] at hattr_exists ih
    cases e : k == attr
    case false =>
      simp only [e] at ⊢ hattr_exists
      apply ih hattr_exists
    case true =>
      simp only [e, Option.some.injEq] at hattr_exists
      simp only [hattr_exists, Option.some.injEq, exists_eq_left']
      cases qty with
      | optional =>
        simp only [TermType.ofQualifiedType, Qualified.isRequired, and_true]
        simp only [Qualified.getType] at hattr_ty
        simp [hattr_ty]
      | required =>
        simp only [
          TermType.ofQualifiedType, Qualified.isRequired,
          Bool.true_eq_false, and_false, and_true,
        ]
        simp only [Qualified.getType] at hattr_ty
        simp only [hattr_ty]
        -- TermType.ofType never produces an option type
        unfold TermType.ofType
        split
        case h_1 hof_type =>
          split at hof_type
          all_goals contradiction
        simp

/--
Decompose a successful `getAttrInRecord` lookup into the record-type `find?`
fact it rests on.
-/
theorem getAttrInRecord_ok_find
    {ty : CedarType} {rty : RecordType} {x : Expr} {a : Attr} {c c₂ : Capabilities} {aty : CedarType}
    (h : Cedar.Validation.getAttrInRecord ty rty x a c = .ok (aty, c₂)) :
    ∃ qty, rty.find? a = some qty ∧ qty.getType = aty := by
  simp only [Cedar.Validation.getAttrInRecord] at h
  split at h
  case _ aty' hfind =>
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨_, hfind, by simp only [Qualified.getType, h.1]⟩
  case _ aty' hfind =>
    split at h
    · simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨_, hfind, by simp only [Qualified.getType, h.1]⟩
    · simp only [Validation.err, reduceCtorEq] at h
  case _ hfind => simp only [Validation.err, reduceCtorEq] at h

theorem compilePred_well_typed_getAttr
    {a : Attr} {x₁ : Cedar.Spec.PredExpr} {ty₁ typ : TypedExpr}
    {c c' : Capabilities} {Γ : TypeEnv} {it t₁ : Term}
    (hwε : (SymEnv.ofEnv Γ).WellFormed)
    (hitw : it.WellFormed (SymEnv.ofEnv Γ).entities)
    (hitty : it.typeOf = .option (TermType.ofType ty₁.typeOf))
    (hok₁ : compilePred x₁ it (SymEnv.ofEnv Γ) = .ok t₁)
    (hty₁ : t₁.typeOf = .option (TermType.ofType ty₁.typeOf))
    (htp : typeOfGetAttr ty₁ x₁.toExpr a c Γ = .ok (typ, c')) :
    ∃ t, compilePred (.getAttr x₁ a) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType typ.typeOf) := by
  have ⟨hwf_comp_x, _, _⟩ := compilePred_wf hwε hitw hitty hok₁
  have ⟨hwf_get_comp_x, hty_get_comp_x⟩ := wf_option_get hwf_comp_x hty₁
  simp only [compilePred, hok₁, Except.bind_ok]
  -- Unified compile-side closer: produce the inner `compileGetAttr` term `gt` and its ifSome type.
  suffices h : ∀ (attrs : Term) (rty : RecordType) (aty : CedarType),
      compileAttrsOf (Factory.option.get t₁) (SymEnv.ofEnv Γ).entities = .ok attrs →
      attrs.WellFormed (SymEnv.ofEnv Γ).entities →
      attrs.typeOf = .record (Map.mk (TermType.ofRecordType rty.toList)) →
      (∃ qty, rty.find? a = some qty ∧ qty.getType = aty) →
      ∃ gt, compileGetAttr (Factory.option.get t₁) a (SymEnv.ofEnv Γ).entities = .ok gt ∧
            (Factory.ifSome t₁ gt).typeOf = .option (TermType.ofType aty) by
    unfold typeOfGetAttr at htp
    split at htp
    case _ rty hty_expr =>  -- record receiver
      simp only [Validation.ok, bind, Except.bind] at htp
      split at htp <;> rename_i hgir <;>
        simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at htp
      obtain ⟨htyp, -⟩ := htp; subst typ
      have hattrs_ok : compileAttrsOf (Factory.option.get t₁) (SymEnv.ofEnv Γ).entities
          = .ok (Factory.option.get t₁) := by
        simp only [compileAttrsOf, hty_get_comp_x, hty_expr, TermType.ofType]
      have hty_rt : (Factory.option.get t₁).typeOf = .record (Map.mk (TermType.ofRecordType rty.toList)) := by
        cases rty with | mk rl => simp only [hty_get_comp_x, hty_expr, TermType.ofType, Map.toList_mk_id]
      obtain ⟨gt, hgt, htty⟩ := h _ rty _ hattrs_ok hwf_get_comp_x hty_rt (getAttrInRecord_ok_find hgir)
      exact ⟨Factory.ifSome t₁ gt, by simp only [hgt, Except.bind_ok],
        by simp only [TypedExpr.typeOf]; exact htty⟩
    case _ ety hty_expr =>  -- entity receiver
      split at htp
      case _ rty hattrs_exists =>
        simp only [Validation.ok, bind, Except.bind] at htp
        split at htp <;> rename_i hgir <;>
          simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at htp
        obtain ⟨htyp, -⟩ := htp; subst typ
        have ⟨attrs, hae, hwf_attrs, hattr_arg, hattr_out⟩ :=
          ofEnv_preserves_entity_attr rfl hattrs_exists hwε
        have hattrs_ok : compileAttrsOf (Factory.option.get t₁) (SymEnv.ofEnv Γ).entities
            = .ok (Factory.app attrs (Factory.option.get t₁)) := by
          simp only [compileAttrsOf, hty_get_comp_x, hty_expr, TermType.ofType, hae]
        have hwf_app : (Factory.app attrs (Factory.option.get t₁)).WellFormed (SymEnv.ofEnv Γ).entities :=
          (wf_app hwf_get_comp_x (by simp only [hty_get_comp_x, hty_expr, TermType.ofType, hattr_arg]) hwf_attrs).left
        have hty_app : (Factory.app attrs (Factory.option.get t₁)).typeOf
            = .record (Map.mk (TermType.ofRecordType rty.toList)) := by
          rw [← hattr_out]
          exact (wf_app (εs := (SymEnv.ofEnv Γ).entities) hwf_get_comp_x
            (by simp only [hty_get_comp_x, hty_expr, TermType.ofType, hattr_arg]) hwf_attrs).right
        obtain ⟨gt, hgt, htty⟩ := h _ rty _ hattrs_ok hwf_app hty_app (getAttrInRecord_ok_find hgir)
        exact ⟨Factory.ifSome t₁ gt, by simp only [hgt, Except.bind_ok],
          by simp only [TypedExpr.typeOf]; exact htty⟩
      case _ => exact absurd htp (by simp only [Validation.err, reduceCtorEq, not_false_eq_true])
    case _ => exact absurd htp (by simp only [Validation.err, reduceCtorEq, not_false_eq_true])
  -- Prove the closer.
  intro attrs rty aty hattrs_ok hwf_attrs hty_attrs ⟨qty, hfind, hgt⟩
  have ⟨attr_ty, hfa, hmatch⟩ := ofRecordType_preserves_attr hfind hgt
  unfold compileGetAttr
  rw [hattrs_ok]
  simp only [Except.bind_ok, hty_attrs]
  -- `rty.1` and `Map.toList rty` are the same list, so `hfa` and the split
  -- hypotheses describe the same lookup; `attr_ty` is what `hfa` found.
  have hfa' : (Map.mk (TermType.ofRecordType (Map.toList rty))).find? a = some attr_ty := hfa
  split
  case _ aty' hopt =>  -- symbolic field optional: result is `record.get attrs a`
    rw [hfa'] at hopt
    simp only [Option.some.injEq] at hopt
    subst hopt
    -- `hmatch` on the `.option` branch: `TermType.ofType aty = aty'`.
    simp only at hmatch
    refine ⟨_, rfl, ?_⟩
    apply typeOf_ifSome_option
    rw [(wf_record_get (εs := (SymEnv.ofEnv Γ).entities) hwf_attrs hty_attrs hfa).right]
    simp only [hmatch.1]
  case _ hne =>  -- symbolic field required: result is `⊙(record.get attrs a)`
    -- The split provides a proof that the found type is not an option.
    rename_i hnopt
    rw [hfa'] at hne
    simp only [Option.some.injEq] at hne
    subst hne
    -- `attr_ty` is not an option type, so `hmatch` is the `_` (required) branch.
    have hreq : TermType.ofType aty = attr_ty := by
      cases attr_ty with
      | option a' => exact absurd rfl (hnopt a')
      | _ => exact hmatch.1
    refine ⟨_, rfl, ?_⟩
    apply typeOf_ifSome_option
    simp only [Factory.someOf, Term.typeOf, TermType.option.injEq]
    rw [(wf_record_get (εs := (SymEnv.ofEnv Γ).entities) hwf_attrs hty_attrs hfa).right]
    exact hreq.symm
  case _ hnone =>  -- lookup `none` contradicts `hfa`
    rw [hfa'] at hnone; exact absurd hnone (by simp)

end Cedar.Thm
