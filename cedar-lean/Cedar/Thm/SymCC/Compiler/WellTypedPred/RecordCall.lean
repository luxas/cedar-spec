/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Thm.Data.Map
import Cedar.Thm.Data.List
import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.Tactics
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.ofType

/-!
D-72 step (3), recursive list arms of `compilePred_well_typed`: the `.record` and
`.call` arms. These mirror the scalar `compile_well_typed_record` /
`compile_well_typed_call` (Thm/SymCC/Compiler/WellTyped.lean), but drive the
sub-predicate typing from a per-element list hypothesis (the induction hypotheses
the dispatcher supplies) rather than a `cases hwt` on `TypedExpr.WellTyped`
evidence, which the predicate well-typedness relation does not carry.

This file is standalone (it does NOT import the still-red `compilePred_well_typed`
dispatcher in WellTyped.lean); the integrator imports it.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

/--
D-72 step (3), `.record` arm (mirror of `compile_well_typed_record`). The per-field
induction hypothesis is supplied as a `Forall₂` between the predicate fields `axs`
and the typed-field list `atys` that `typeOfPred (.record axs)` produced: each pair
`⟨(a, x), (a', ty)⟩` has `a = a'` and `x` compiles to a `.option (ofType ty.typeOf)`
term. From `typeOfPred (.record axs) = .ok (typ, c')`, `typ.typeOf` is already
`.record (Map.make (atys.map (λ (a, ty) => (a, .required ty.typeOf))))` by
construction, so the type reconciliation mirrors the scalar record arm with that
map playing the role of the scalar's `hrty`.
-/
theorem compilePred_well_typed_record
    {axs : List (Attr × Cedar.Spec.PredExpr)} {atys : List (Attr × TypedExpr)}
    {typ : TypedExpr} {Γ : TypeEnv} {it : Term}
    (ih : List.Forall₂ (λ ax aty => ax.fst = aty.fst ∧
      ∃ t, compilePred ax.snd it (SymEnv.ofEnv Γ) = .ok t ∧
        t.typeOf = .option (TermType.ofType aty.snd.typeOf) ∧
        t.WellFormed (SymEnv.ofEnv Γ).entities) axs atys)
    (htyp : typ = .record atys
      (.record (Map.make (atys.map (λ (a, ty) => (a, Qualified.required ty.typeOf)))))) :
    ∃ t, compilePred (.record axs) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType typ.typeOf) := by
  subst htyp
  simp only [TypedExpr.typeOf, TermType.ofType]
  -- All fields compile successfully.
  have ⟨tcomp_xs, hcomp_xs⟩ :
    ∃ ats : List (Attr × Term),
      List.mapM (fun (p : Attr × Cedar.Spec.PredExpr) =>
        (do Except.ok (p.fst, ← compilePred p.snd it (SymEnv.ofEnv Γ)) : SymCC.Result (Attr × Term))) axs
        = Except.ok ats := by
    apply List.all_ok_implies_mapM_ok
    intro p hx
    have ⟨aty, _, _, t, hcomp, _⟩ := List.forall₂_implies_all_left ih p hx
    exact ⟨(p.fst, t), by simp only [hcomp, Except.bind_ok]⟩
  -- Reduce the compile side to the `mapM`.
  simp only [compilePred, compileRecord]
  simp only [do_eq_ok, Except.ok.injEq]
  rw [List.mapM₂_eq_mapM λ (p : Attr × Cedar.Spec.PredExpr) =>
    (do Except.ok (p.fst, ← compilePred p.snd it (SymEnv.ofEnv Γ)) : SymCC.Result (Attr × Term))]
  -- Association between the typed fields `atys` and the compiled terms `tcomp_xs`.
  have hassoc_comp_xs_simp :
    List.Forallᵥ
      (λ (ty : TypedExpr) (t : Term) =>
        TermType.ofQualifiedType (Qualified.required ty.typeOf) =
        (Factory.option.get t).typeOf)
      atys tcomp_xs := by
    simp only [List.Forallᵥ]
    -- axs ↔ atys (ih) composed with axs ↔ tcomp_xs (hcomp_xs)
    have hat : List.Forall₂
        (λ (ax : Attr × Cedar.Spec.PredExpr) (t : Attr × Term) =>
          (do Except.ok (ax.fst, ← compilePred ax.snd it (SymEnv.ofEnv Γ)) : SymCC.Result (Attr × Term)) = .ok t)
        axs tcomp_xs := by
      apply List.mapM_implies_forall₂ _ hcomp_xs
      intro x y _ h; exact h
    apply List.forall₂_trans_ish ih hat
    intro ax aty t hih hcomp
    obtain ⟨hfst, tc, hcompx, htyx, hwfx⟩ := hih
    simp only [hcompx, Except.bind_ok, Except.ok.injEq] at hcomp
    have htfst : t.fst = ax.fst := by simp [← hcomp]
    have htsnd : t.snd = tc := by simp [← hcomp]
    refine ⟨by rw [htfst]; exact hfst.symm, ?_⟩
    simp only [TermType.ofQualifiedType, htsnd]
    exact Eq.symm (wf_option_get hwfx htyx).right
  -- Swap the association to the `recordOf`-friendly form.
  have hassoc_comp_xs :
    List.Forallᵥ
      (λ (t : Term) (ty : QualifiedType) => t.typeOf = TermType.ofQualifiedType ty)
      (List.map (fun x => (x.fst, Factory.option.get x.snd)) tcomp_xs)
      (List.map (fun x => (x.fst, Qualified.required x.snd.typeOf)) atys) := by
    apply List.forall₂_swap
    apply List.map_preserves_forall₂
    rotate_left
    · simp only [List.Forallᵥ] at hassoc_comp_xs_simp
      apply hassoc_comp_xs_simp
    · simp only [and_imp, Prod.forall]
      intros k1 x k2 y hkeq h
      simp [hkeq, h]
  -- Each compiled term and its `option.get` is well-formed.
  have hwf_comp_xs :
    ∀ (y : Term), y ∈ List.map Prod.snd tcomp_xs →
    Term.WellFormed (SymEnv.ofEnv Γ).entities y ∧
    Term.WellFormed (SymEnv.ofEnv Γ).entities (Factory.option.get y) := by
    simp only [List.mem_map, Prod.exists, exists_eq_right, forall_exists_index]
    intros y k hy
    have ⟨p, hx, hy⟩ := List.mapM_ok_implies_all_from_ok hcomp_xs (k, y) hy
    have ⟨aty, _, _, tc, hcompx, htyx, hwfx⟩ := List.forall₂_implies_all_left ih p hx
    simp only [hcompx, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hy
    simp only [hy.2] at hwfx htyx
    simp only [hwfx, true_and]
    exact (wf_option_get hwfx htyx).left
  -- Discharge the existential (compile succeeds) and the record type.
  simp only [hcomp_xs, Factory.someOf, Except.ok.injEq, exists_eq_left']
  apply (wf_ifAllSome (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_ ?_).right
  · intros g hg
    exact (hwf_comp_xs g hg).left
  · constructor
    apply wf_recordOf
    simp only [
      List.mem_map, Prod.exists, Prod.map_apply,
      id_eq, Prod.mk.injEq, forall_exists_index,
      and_imp,
    ]
    intros k y k2 y2 hy hk_to_k2 hopt_y
    simp only [← hopt_y]
    simp only [List.mem_map, Prod.exists, exists_eq_right, forall_exists_index] at hwf_comp_xs
    exact (hwf_comp_xs y2 k2 hy).right
  · simp only [
      Factory.recordOf, Data.Map.make, Term.typeOf,
      TypedExpr.typeOf, TermType.ofType,
      TermType.option.injEq, TermType.record.injEq,
    ]
    rw [Map.mapOnValues₂_eq_mapOnValues _ Term.typeOf]
    simp only [Map.mapOnValues, Map.toList_mk_id, Map.mk.injEq]
    rw [ofRecordType_as_map]
    simp only [Data.Map.make]
    apply List.forall₂_iff_map_eq.mp
    apply List.Forall₂.imp
    rotate_left
    · apply List.canonicalize_preserves_forallᵥ
      apply hassoc_comp_xs
    · simp

end Cedar.Thm
