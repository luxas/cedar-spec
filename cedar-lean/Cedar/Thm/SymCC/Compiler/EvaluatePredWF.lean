/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

-- Step C support: value well-formedness of an evaluated quantifier predicate.
-- Mirrors `evaluate_wf` (WF.lean) arm by arm; the leaves differ (`.item` returns the
-- bound value `v`, taken WF by hypothesis; `.var` reads the request; `.lit` returns a lit).

import Cedar.SymCC
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.Tactics

namespace Cedar.Thm

open Spec SymCC Data

/-- `v.WellFormed` is preserved by evaluating a well-formed quantifier predicate over the
well-formed bound value `v`. -/
theorem evaluatePred_wf {p : PredExpr} {env : Env} {v r : Value}
    (hwfenv : env.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hrefs : PredExpr.ValidRefs (λ uid => env.entities.contains uid) p)
    (hok : evaluatePred p v env.request env.entities = .ok r) :
    r.WellFormed env.entities := by
  match p, hrefs with
  | .item, _ =>
    simp only [evaluatePred, Except.ok.injEq] at hok; subst hok; exact hvwf
  | .lit l, .lit_valid hvr =>
    simp only [evaluatePred, Except.ok.injEq] at hok; subst hok
    apply Value.WellFormed.prim_wf
    cases l <;> simp only [Prim.WellFormed]
    exact hvr
  | .var vr, _ =>
    have hreq := hwfenv.left
    unfold Request.WellFormed at hreq
    cases vr <;> simp only [evaluatePred, Except.ok.injEq] at hok <;> subst hok
    case principal => apply Value.WellFormed.prim_wf; simp only [Prim.WellFormed, hreq.left]
    case action => apply Value.WellFormed.prim_wf; simp only [Prim.WellFormed, hreq.right.left]
    case resource => apply Value.WellFormed.prim_wf; simp only [Prim.WellFormed, hreq.right.right.left]
    case context => exact hreq.right.right.right
  | .ite x₁ x₂ x₃, .ite_valid hr₁ hr₂ hr₃ =>
    simp only [evaluatePred, Result.as] at hok
    simp_do_let (evaluatePred x₁ v env.request env.entities) as hok₁ at hok
    rename_i v₁
    simp only [Coe.coe, Value.asBool] at hok
    split at hok <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
    split at hok
    · exact evaluatePred_wf hwfenv hvwf hr₂ hok
    · exact evaluatePred_wf hwfenv hvwf hr₃ hok
  | .and x₁ x₂, .and_valid hr₁ hr₂ =>
    simp only [evaluatePred, Result.as] at hok
    simp_do_let (evaluatePred x₁ v env.request env.entities) as hok₁ at hok
    rename_i v₁
    simp only [Coe.coe, Value.asBool] at hok
    split at hok <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
    cases hok₂ : evaluatePred x₂ v env.request env.entities <;>
      simp only [Lean.Internal.coeM, hok₂, Except.bind_err] at hok
    case error =>
      split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
      subst hok; exact value_bool_wf
    case ok =>
      split at hok
      case isTrue => simp only [Except.ok.injEq] at hok; subst hok; exact value_bool_wf
      case isFalse =>
        split at hok <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
        simp only [pure, Except.pure, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe,
          Coe.coe, Except.ok.injEq] at hok
        subst hok; exact value_bool_wf
  | .or x₁ x₂, .or_valid hr₁ hr₂ =>
    simp only [evaluatePred, Result.as] at hok
    simp_do_let (evaluatePred x₁ v env.request env.entities) as hok₁ at hok
    rename_i v₁
    simp only [Coe.coe, Value.asBool] at hok
    split at hok <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
    cases hok₂ : evaluatePred x₂ v env.request env.entities <;>
      simp only [Lean.Internal.coeM, hok₂, Except.bind_err] at hok
    case error =>
      split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
      subst hok; exact value_bool_wf
    case ok =>
      split at hok
      case isTrue => simp only [Except.ok.injEq] at hok; subst hok; exact value_bool_wf
      case isFalse =>
        split at hok <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
        simp only [pure, Except.pure, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe,
          Coe.coe, Except.ok.injEq] at hok
        subst hok; exact value_bool_wf
  | .unaryApp op₁ x₁, .unaryApp_valid hr₁ =>
    simp only [evaluatePred] at hok
    simp_do_let (evaluatePred x₁ v env.request env.entities) at hok
    simp only [apply₁] at hok
    split at hok <;> (try simp only [Except.ok.injEq, reduceCtorEq] at hok)
    case h_1 | h_3 | h_4 | h_5 => subst hok; exact value_bool_wf
    case h_2 => exact intOrErr_ok_wf hok
  | .binaryApp op₂ x₁ x₂, .binaryApp_valid hr₁ hr₂ =>
    simp only [evaluatePred] at hok
    simp_do_let (evaluatePred x₁ v env.request env.entities) at hok
    simp_do_let (evaluatePred x₂ v env.request env.entities) at hok
    simp only [apply₂] at hok
    split at hok <;> (try simp only [Except.ok.injEq, hasTag, reduceCtorEq] at hok)
    any_goals (subst hok ; exact value_bool_wf)
    any_goals (exact intOrErr_ok_wf hok)
    exact inₛ_wf hok
    case _ uid tag h₁ h₂ =>
      simp only [getTag] at hok
      simp_do_let (env.entities.tags uid) at hok
      rename_i heq
      rw [Map.findOrErr_ok_iff_find?_some] at hok
      have hent := hwfenv.right
      simp only [Entities.tags] at heq
      simp_do_let (Map.findOrErr env.entities uid Error.entityDoesNotExist) at heq
      rename_i d hd
      simp only [Except.ok.injEq] at heq
      subst heq
      rw [Map.findOrErr_ok_iff_find?_some] at hd
      replace hent := hent.2 uid d hd
      exact hent.right.right.right.right tag r hok
  | .hasAttr x₁ a, .hasAttr_valid hr₁ =>
    simp only [evaluatePred] at hok
    simp only [hasAttr, attrsOf] at hok
    simp_do_let (evaluatePred x₁ v env.request env.entities) at hok
    split at hok
    case h_3 => simp only [Except.bind_err, reduceCtorEq] at hok
    case h_1 | h_2 =>
      simp only [Except.bind_ok, Except.ok.injEq] at hok; subst hok; exact value_bool_wf
  | .extHasAttr x₁ a l, .extHasAttr_valid hr₁ =>
    simp only [evaluatePred] at hok
    simp_do_let (evaluatePred x₁ v env.request env.entities) at hok
    have ⟨b, hb⟩ := hasAttrs_ok_is_bool hok
    subst hb; exact value_bool_wf
  | .getAttr x₁ a, .getAttr_valid hr₁ =>
    simp only [evaluatePred] at hok
    simp only [getAttr, attrsOf] at hok
    simp_do_let (evaluatePred x₁ v env.request env.entities) at hok
    rename_i hok₁
    have ih₁ := evaluatePred_wf hwfenv hvwf hr₁ hok₁
    split at hok
    case h_1 r' =>
      simp only [Except.bind_ok, Map.findOrErr_ok_iff_find?_some] at hok
      exact value_record_wf_implies_attr_value_wf ih₁ hok
    case h_2 uid =>
      simp_do_let (Entities.attrs env.entities uid) at hok
      rename_i ha
      simp only [Map.findOrErr_ok_iff_find?_some] at hok
      simp only [Entities.attrs] at ha
      simp_do_let (Map.findOrErr env.entities uid Error.entityDoesNotExist) at ha
      rename_i d hd
      simp only [Except.ok.injEq] at ha
      subst ha
      apply value_record_wf_implies_attr_value_wf _ hok
      simp only [Map.findOrErr_ok_iff_find?_some] at hd
      exact (hwfenv.right.2 uid d hd).left
    case h_3 => simp only [Except.bind_err, reduceCtorEq] at hok
  | .call xfn xs, _ =>
    simp only [evaluatePred] at hok
    simp_do_let (List.mapM₁ xs fun x => evaluatePred x.val v env.request env.entities) at hok
    simp only [call] at hok
    split at hok <;> (try simp only [Except.ok.injEq, reduceCtorEq] at hok)
    any_goals (subst hok ; exact value_bool_wf)
    any_goals (subst hok; exact value_int_wf)
    any_goals (subst hok; exact Value.WellFormed.ext_wf)
    all_goals {
      simp only [res] at hok
      split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
      simp only [Coe.coe] at hok
      subst hok
      exact Value.WellFormed.ext_wf
    }
  | .record axs, .record_valid hr =>
    simp only [evaluatePred] at hok
    simp_do_let (List.mapM₂ axs fun x => bindAttr x.1.fst (evaluatePred x.1.snd v env.request env.entities)) at hok
    rename_i vs hvs
    simp only [Except.ok.injEq] at hok
    subst hok
    simp only [List.mapM₂_eq_mapM λ (x : Attr × PredExpr) => bindAttr x.fst (evaluatePred x.snd v env.request env.entities)] at hvs
    rw [← List.mapM'_eq_mapM] at hvs
    apply Value.WellFormed.record_wf _ (Map.make_wf vs)
    intro a v' hv
    replace hv := Map.find?_mem_toList hv
    replace hv := Map.mem_make_mem_list hv
    replace ⟨x, hx, hvs⟩ := List.mapM'_ok_implies_all_from_ok hvs (a, v') hv
    clear hv
    simp only [bindAttr] at hvs
    simp_do_let (evaluatePred x.snd v env.request env.entities) at hvs
    rename_i vx hvx
    simp only [Functor.map, Except.map, pure, Except.pure, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hvs
    obtain ⟨_, rfl⟩ := hvs
    exact evaluatePred_wf hwfenv hvwf (hr x hx) hvx
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have h := ‹(_, _) ∈ _›; replace h := List.sizeOf_snd_lt_sizeOf_list h; omega)
      | (have h := ‹_ ∈ _›; replace h := List.sizeOf_snd_lt_sizeOf_list h; omega)
      | (have h := ‹_ ∈ _›; replace h := List.sizeOf_lt_of_mem h; omega)

end Cedar.Thm
