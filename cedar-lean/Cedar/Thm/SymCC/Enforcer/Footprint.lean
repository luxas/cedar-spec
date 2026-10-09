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

import Cedar.SymCC.Enforcer
import Cedar.Thm.Data.LT
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.SymCC.Env.SWF
import Cedar.Thm.SymCC.Enforcer.Asserts
import Cedar.Thm.SymCC.Compiler

/-!
This file proves properties of the `footprints` function in `Cedar/SymCC/Enforcer.lean`.
--/

namespace Cedar.SymCC

open Data Spec SymCC Factory

theorem footprint_ofEntity_wf :
  (footprint.ofEntity x εnv).WellFormed
:= by
  simp [footprint.ofEntity]
  split
  · split <;> simp [Set.singleton_wf, Set.empty_wf]
  · exact Set.empty_wf

theorem footprint_ofBranch_wf :
  ft₂.WellFormed →
  ft₃.WellFormed →
  (footprint.ofBranch εnv x ft₁ ft₂ ft₃).WellFormed
:= by
  intro h₂ h₃
  simp [footprint.ofBranch]
  split <;> simp [h₂, h₃, Set.empty_wf, Set.union_wf]

theorem footprintPred_ofEntity_wf {q : PredExpr} {it : Term} {εnv : SymEnv} :
  (footprintPred.ofEntity it εnv q).WellFormed := by
  simp only [footprintPred.ofEntity]
  split
  · exact Set.empty_wf
  · split
    · split <;> simp [Set.singleton_wf, Set.empty_wf]
    · exact Set.empty_wf

theorem footprintPred_ofBranch_wf {q : PredExpr} {it : Term} {εnv : SymEnv} {ft₁ ft₂ ft₃ : Set Term} :
  ft₂.WellFormed → ft₃.WellFormed → (footprintPred.ofBranch it εnv q ft₁ ft₂ ft₃).WellFormed := by
  intro h₂ h₃
  simp only [footprintPred.ofBranch]
  split <;> simp [h₂, h₃, Set.empty_wf, Set.union_wf]

theorem footprintPred_wf (p : PredExpr) (it : Term) (εnv : SymEnv) :
  (footprintPred p it εnv).WellFormed := by
  induction p using footprintPred.induct <;>
    simp only [footprintPred] <;>
    simp [footprintPred_ofEntity_wf, footprintPred_ofBranch_wf,
      List.mapUnion₁_eq_mapUnion (footprintPred · it εnv),
      List.mapUnion₂_eq_mapUnion (λ x => footprintPred x.snd it εnv),
      Set.empty_wf, List.mapUnion_wf, Set.union_wf, *]

theorem footprintAllPred_wf (p : PredExpr) (x₁ : Expr) (εnv : SymEnv) :
  (footprintAllPred p x₁ εnv).WellFormed := by
  simp only [footprintAllPred]
  split
  · split
    · exact footprintPred_wf _ _ _
    · exact Set.empty_wf
  · exact Set.empty_wf

theorem footprint_wf (x : Expr) (εnv : SymEnv) :
  (footprint x εnv).WellFormed
:= by
  cases x
  all_goals simp [footprint, footprint_ofEntity_wf, footprint_ofBranch_wf, footprint_wf,
    List.mapUnion₁_eq_mapUnion (footprint · εnv), List.mapUnion₂_eq_mapUnion (λ x => footprint x.snd εnv),
    Set.empty_wf, List.mapUnion_wf, Set.union_wf]

theorem footprints_wf (xs : List Expr) (εnv : SymEnv) :
  (footprints xs εnv).WellFormed
:= by
  simp [footprints, List.mapUnion_wf]

def SymEntities.SameOn (εs : SymEntities) (ft : Set Term) (I₁ I₂ : Interpretation) : Prop :=
  ∀ ety δ,
    εs.find? ety = some δ →
    δ.attrs.interpret I₁ = δ.attrs.interpret I₂ ∧
    (∀ ancTy ancF,
      δ.ancestors.find? ancTy = some ancF →
      ∀ t ∈ ft, ∀ uid,
        t.interpret I₁ = .some (.entity uid) →
        ety = uid.ty →
        app (ancF.interpret I₁) (Term.entity uid) =
        app (ancF.interpret I₂) (Term.entity uid)) ∧
    (∀ τs, δ.tags = some τs → τs.interpret I₁ = τs.interpret I₂)

def SymEnv.SameOn (εnv : SymEnv) (ft : Set Term) (I₁ I₂ : Interpretation) : Prop :=
  εnv.request.interpret I₁ = εnv.request.interpret I₂ ∧
  εnv.entities.SameOn ft I₁ I₂

end Cedar.SymCC

namespace Cedar.Thm

open Data Spec SymCC Factory

theorem mem_footprints_iff {xs : List Expr} {εnv : SymEnv} {t : Term} :
  t ∈ footprints xs εnv ↔ ∃ x ∈ xs, t ∈ footprint x εnv
:= by
  simp only [footprints, List.mem_mapUnion_iff_mem_exists]

private theorem mem_footprint_ofBranch_mem {x : Expr} {t : Term} {εnv : SymEnv} {ft₁ ft₂ ft₃ : Set Term}
  (hin : t ∈ footprint.ofBranch εnv x ft₁ ft₂ ft₃) :
  t ∈ ft₁ ∨ t ∈ ft₂ ∨ t ∈ ft₃
:= by
  simp only [footprint.ofBranch] at hin
  split at hin
  case h_1 | h_2 =>
    simp only [hin, true_or, or_true]
  case h_3 =>
    simp only [Set.mem_union] at hin
    rw [or_assoc] at hin
    exact hin
  case h_4 =>
    simp only [Set.not_mem_empty] at hin

private theorem mem_footprint_ofEntity_exists_wf {p : Expr → Prop} {x : Expr} {tₑ : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor x)
  (hp  : p x)
  (hin : tₑ ∈ footprint.ofEntity x εnv) :
  ∃ xₑ, εnv.WellFormedFor xₑ ∧ p xₑ ∧ compile xₑ εnv = .ok tₑ
:= by
  simp only [footprint.ofEntity] at hin
  split at hin
  split at hin
  any_goals simp only [Set.not_mem_empty] at hin
  rename_i hok hty
  rw [Set.mem_singleton] at hin
  subst hin
  exists x

private theorem mem_footprint_ofEntity_option_entity {x : Expr} {tₑ : Term} {εnv : SymEnv}
  (hin : tₑ ∈ footprint.ofEntity x εnv) :
  ∃ ety, tₑ.typeOf = .option (.entity ety)
:= by
  simp only [footprint.ofEntity] at hin
  split at hin
  split at hin
  any_goals simp only [Set.not_mem_empty] at hin
  rename_i hty
  rw [Set.mem_singleton] at hin
  subst hin
  exact isOptionEntityType_implies_option_entity_type hty

private theorem mem_footprintPred_ofBranch_mem {q : PredExpr} {it t : Term} {εnv : SymEnv} {ft₁ ft₂ ft₃ : Set Term}
  (hin : t ∈ footprintPred.ofBranch it εnv q ft₁ ft₂ ft₃) :
  t ∈ ft₁ ∨ t ∈ ft₂ ∨ t ∈ ft₃
:= by
  simp only [footprintPred.ofBranch] at hin
  split at hin
  case h_1 | h_2 => simp only [hin, true_or, or_true]
  case h_3 => simp only [Set.mem_union] at hin; rw [or_assoc] at hin; exact hin
  case h_4 => simp only [Set.not_mem_empty] at hin

private theorem mem_footprintPred_ofEntity_option_entity {q : PredExpr} {it tₑ : Term} {εnv : SymEnv}
  (hin : tₑ ∈ footprintPred.ofEntity it εnv q) :
  ∃ ety, tₑ.typeOf = .option (.entity ety)
:= by
  simp only [footprintPred.ofEntity] at hin
  split at hin
  · simp only [Set.not_mem_empty] at hin
  · split at hin
    split at hin
    any_goals simp only [Set.not_mem_empty] at hin
    rename_i hty
    rw [Set.mem_singleton] at hin
    subst hin
    exact isOptionEntityType_implies_option_entity_type hty

theorem mem_footprintPred_option_entity {p : PredExpr} {it : Term} {εnv : SymEnv} {t : Term} :
  t ∈ footprintPred p it εnv → ∃ ety, t.typeOf = .option (.entity ety)
:= by
  intro hin
  induction p using footprintPred.induct <;> simp only [footprintPred] at hin
  case case1 => simp only [Set.not_mem_empty] at hin
  case case2 | case3 =>
    exact mem_footprintPred_ofEntity_option_entity hin
  case case4 ih₁ ih₂ ih₃ =>
    rcases mem_footprintPred_ofBranch_mem hin with hin | hin | hin
    · exact ih₁ hin
    · exact ih₂ hin
    · exact ih₃ hin
  case case5 ih₁ ih₂ =>
    rcases mem_footprintPred_ofBranch_mem hin with hin | hin | hin
    · exact ih₁ hin
    · exact ih₂ hin
    · simp only [Set.not_mem_empty] at hin
  case case6 ih₁ ih₂ =>
    rcases mem_footprintPred_ofBranch_mem hin with hin | hin | hin
    · exact ih₁ hin
    · simp only [Set.not_mem_empty] at hin
    · exact ih₂ hin
  case case7 ih₁ ih₂ =>
    simp only [Set.mem_union] at hin
    rcases hin with (hin | hin) | hin
    · exact mem_footprintPred_ofEntity_option_entity hin
    · exact ih₁ hin
    · exact ih₂ hin
  case case8 ih =>
    simp only [Set.mem_union] at hin
    rcases hin with hin | hin
    · exact mem_footprintPred_ofEntity_option_entity hin
    · exact ih hin
  case case9 ih | case10 ih | case11 ih =>
    exact ih hin
  case case12 ih =>
    simp only [List.mapUnion₁_eq_mapUnion (footprintPred · it εnv), List.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨xᵢ, hinᵢ, hin⟩ := hin
    exact ih xᵢ hinᵢ hin
  case case13 ih =>
    simp only [List.mapUnion₂_eq_mapUnion λ y : Attr × PredExpr => footprintPred y.snd it εnv,
      List.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨(aᵢ, xᵢ), hinᵢ, hin⟩ := hin
    simp only at hin ih
    exact ih aᵢ xᵢ (List.sizeOf_attach₂ hinᵢ) hin

theorem mem_footprintAllPred_option_entity {p : PredExpr} {x₁ : Expr} {εnv : SymEnv} {t : Term} :
  t ∈ footprintAllPred p x₁ εnv → ∃ ety, t.typeOf = .option (.entity ety)
:= by
  intro hin
  simp only [footprintAllPred] at hin
  split at hin
  · split at hin
    · exact mem_footprintPred_option_entity hin
    · simp only [Set.not_mem_empty] at hin
  · simp only [Set.not_mem_empty] at hin

theorem mem_footprint_option_entity {x : Expr} {εnv : SymEnv} {t : Term} :
  t ∈ footprint x εnv → ∃ ety, t.typeOf = .option (.entity ety)
:= by
  intro hin
  induction x using footprint.induct <;> simp only [footprint] at hin
  case case1 | case2 =>
    exact mem_footprint_ofEntity_option_entity hin
  case case3 ih₁ ih₂ ih₃ =>
    replace hin := mem_footprint_ofBranch_mem hin
    rcases hin with hin | hin | hin
    · exact ih₁ hin
    · exact ih₂ hin
    · exact ih₃ hin
  case case4 ih₁ ih₂ | case5 ih₁ ih₂ =>
    replace hin := mem_footprint_ofBranch_mem hin
    simp only [Set.not_mem_empty, or_false, false_or] at hin
    rcases hin with hin | hin
    · exact ih₁ hin
    · exact ih₂ hin
  case case6 ih₁ ih₂ =>
    simp only [Set.mem_union] at hin
    rcases hin with (hin | hin) | hin
    · exact mem_footprint_ofEntity_option_entity hin
    · exact ih₁ hin
    · exact ih₂ hin
  case case7 ih =>
    rw [Set.mem_union] at hin
    rcases hin with hin | hin
    · exact mem_footprint_ofEntity_option_entity hin
    · exact ih hin
  case case8 ih | case9 ih | case10 ih =>
    exact ih hin
  case case11 _ _ ih | case12 _ ih =>
    simp only [List.mapUnion₁_eq_mapUnion (footprint · εnv), List.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨xᵢ, hinᵢ, hin⟩ := hin
    exact ih xᵢ hinᵢ hin
  case case13 _ ih =>
    simp only [List.mapUnion₂_eq_mapUnion λ y : Attr × Expr => footprint y.snd εnv,
      List.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨(aᵢ, xᵢ), hinᵢ, hin⟩ := hin
    simp only at hin ih
    exact ih aᵢ xᵢ (List.sizeOf_attach₂ hinᵢ) hin
  case case14 ih =>
    simp only [Set.mem_union] at hin
    rcases hin with hin | hin
    · exact ih hin
    · exact mem_footprintAllPred_option_entity hin

/--
For an `it`-free predicate `q`, compiling it against any element term `it` equals compiling its
`toExpr` as an ordinary expression (D-70, option A — the `it`-free footprint subterms are groundable
because their compiled form is a closed `compile`).
-/
theorem compilePred_toExpr_eq {q : PredExpr} {it : Term} {εnv : SymEnv}
    (hfree : q.mentionsIt = false) :
    compilePred q it εnv = compile q.toExpr εnv := by
  match q, hfree with
  | .item, hfree => exact absurd hfree (by simp only [PredExpr.mentionsIt, Bool.true_eq_false, not_false_eq_true])
  | .lit l, _ => simp only [compilePred, compile, PredExpr.toExpr]
  | .var v, _ => simp only [compilePred, compile, PredExpr.toExpr]
  | .ite c t e, hfree =>
    simp only [PredExpr.mentionsIt, Bool.or_eq_false_iff] at hfree
    simp only [compilePred, compile, PredExpr.toExpr,
      compilePred_toExpr_eq hfree.1.1, compilePred_toExpr_eq hfree.1.2, compilePred_toExpr_eq hfree.2]
  | .and a b, hfree =>
    simp only [PredExpr.mentionsIt, Bool.or_eq_false_iff] at hfree
    simp only [compilePred, compile, PredExpr.toExpr, compilePred_toExpr_eq hfree.1, compilePred_toExpr_eq hfree.2]
  | .or a b, hfree =>
    simp only [PredExpr.mentionsIt, Bool.or_eq_false_iff] at hfree
    simp only [compilePred, compile, PredExpr.toExpr, compilePred_toExpr_eq hfree.1, compilePred_toExpr_eq hfree.2]
  | .unaryApp o e, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [compilePred, compile, PredExpr.toExpr, compilePred_toExpr_eq hfree]
  | .binaryApp o a b, hfree =>
    simp only [PredExpr.mentionsIt, Bool.or_eq_false_iff] at hfree
    simp only [compilePred, compile, PredExpr.toExpr, compilePred_toExpr_eq hfree.1, compilePred_toExpr_eq hfree.2]
  | .getAttr e a, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [compilePred, compile, PredExpr.toExpr, compilePred_toExpr_eq hfree]
  | .hasAttr e a, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [compilePred, compile, PredExpr.toExpr, compilePred_toExpr_eq hfree]
  | .extHasAttr e a l, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [compilePred, compile, PredExpr.toExpr, compilePred_toExpr_eq hfree]
  | .record axs, hfree =>
    simp only [compilePred, compile, PredExpr.toExpr]
    congr 1
    rw [List.map₂_eq_map (λ p : Attr × PredExpr => (p.fst, p.snd.toExpr))]
    simp only [List.mapM₂_eq_mapM λ (p : Attr × PredExpr) => do .ok (p.fst, ← compilePred p.snd it εnv),
      List.mapM₂_eq_mapM λ (p : Attr × Expr) => do .ok (p.fst, ← compile p.snd εnv),
      List.mapM_map]
    apply List.mapM_congr
    intro x hx
    have hxfree : x.snd.mentionsIt = false := by
      simp only [PredExpr.mentionsIt] at hfree
      have hall : (axs.attach₂.all (fun y => !y.val.snd.mentionsIt)) = true := by
        rw [← List.not_any_eq_all_not]; simp only [hfree, Bool.not_false]
      rw [show (fun (y : {z : Attr × PredExpr // sizeOf z.snd < 1 + sizeOf axs}) => !y.val.snd.mentionsIt)
            = (fun (y : {z : Attr × PredExpr // sizeOf z.snd < 1 + sizeOf axs}) =>
                (fun (p : Attr × PredExpr) => !p.snd.mentionsIt) y.val) from rfl,
          List.all_attach₂ (f := fun (p : Attr × PredExpr) => !p.snd.mentionsIt), List.all_eq_true] at hall
      have := hall x hx
      simp only [Bool.not_eq_true'] at this
      exact this
    simp only [Function.comp, compilePred_toExpr_eq hxfree]
  | .call xfn xs, hfree =>
    simp only [compilePred, compile, PredExpr.toExpr]
    congr 1
    rw [List.map₁_eq_map (λ x : PredExpr => x.toExpr)]
    simp only [List.mapM₁_eq_mapM (λ x => compilePred x it εnv),
      List.mapM₁_eq_mapM (λ x => compile x εnv), List.mapM_map]
    apply List.mapM_congr
    intro x hx
    have hxfree : x.mentionsIt = false := by
      simp only [PredExpr.mentionsIt] at hfree
      rw [List.any_eq_false] at hfree
      have := hfree ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩)
      simp only [Bool.not_eq_true] at this
      exact this
    simp only [Function.comp, compilePred_toExpr_eq hxfree]
termination_by sizeOf q
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have h := ‹_ ∈ _›; have := List.sizeOf_snd_lt_sizeOf_list h; omega)
      | (have h := ‹_ ∈ _›; have := List.sizeOf_lt_of_mem h; omega)

private theorem mem_footprint_exists_wf_prop {p : Expr → Prop} {x : Expr} {tₑ : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor x)
  (hp  : p x)
  (hin : tₑ ∈ footprint x εnv)
  (hite  : ∀ {x₁ x₂ x₃}, p (Expr.ite x₁ x₂ x₃) → p x₁ ∧ p x₂ ∧ p x₃)
  (hand  : ∀ {x₁ x₂}, p (Expr.and x₁ x₂) → p x₁ ∧ p x₂)
  (hor   : ∀ {x₁ x₂}, p (Expr.or x₁ x₂) → p x₁ ∧ p x₂)
  (happ₁ : ∀ {o x₁}, p (Expr.unaryApp o x₁) → p x₁)
  (happ₂ : ∀ {o x₁ x₂}, p (Expr.binaryApp o x₁ x₂) → p x₁ ∧ p x₂)
  (hget  : ∀ {a x₁}, p (Expr.getAttr x₁ a) → p x₁)
  (hhas  : ∀ {a x₁}, p (Expr.hasAttr x₁ a) → p x₁)
  (hexthas : ∀ {a attrs x₁}, p (Expr.extHasAttr x₁ a attrs) → p x₁)
  (hset  : ∀ {xs}, p (Expr.set xs) → ∀ x ∈ xs, p x)
  (hrec  : ∀ {axs}, p (Expr.record axs) → ∀ ax ∈ axs, p ax.snd)
  (hcall : ∀ {f xs}, p (Expr.call f xs) → ∀ x ∈ xs, p x) :
  ∃ xₑ, εnv.WellFormedFor xₑ ∧ p xₑ ∧ compile xₑ εnv = .ok tₑ
:= by
  induction x using footprint.induct <;> simp only [footprint] at hin
  case case1 | case2 =>
    exact mem_footprint_ofEntity_exists_wf hwε hp hin
  case case3 ih₁ ih₂ ih₃ =>
    have ⟨hwε₁, hwε₂, hwε₃⟩ := wf_εnv_for_ite_implies hwε
    have ⟨hwe₁, hwe₂, hwe₃⟩ := hite hp
    replace hin := mem_footprint_ofBranch_mem hin
    rcases hin with hin | hin | hin
    · exact ih₁ hwε₁ hwe₁ hin
    · exact ih₂ hwε₂ hwe₂ hin
    · exact ih₃ hwε₃ hwe₃ hin
  case' case4 =>
    have ⟨hwε₁, hwε₂⟩ := wf_εnv_for_and_implies hwε
    have ⟨hwe₁, hwe₂⟩ := hand hp
  case' case5 =>
    have ⟨hwε₁, hwε₂⟩ := wf_εnv_for_or_implies hwε
    have ⟨hwe₁, hwe₂⟩ := hor hp
  case case4 ih₁ ih₂ | case5 ih₁ ih₂ =>
    replace hin := mem_footprint_ofBranch_mem hin
    simp only [Set.not_mem_empty, or_false, false_or] at hin
    rcases hin with hin | hin
    · exact ih₁ hwε₁ hwe₁ hin
    · exact ih₂ hwε₂ hwe₂ hin
  case case6 ih₁ ih₂ =>
    have ⟨hwε₁, hwε₂⟩ := wf_εnv_for_binaryApp_implies hwε
    have ⟨hwe₁, hwe₂⟩ := happ₂ hp
    simp only [Set.mem_union] at hin
    rcases hin with (hin | hin) | hin
    · exact mem_footprint_ofEntity_exists_wf hwε hp hin
    · exact ih₁ hwε₁ hwe₁ hin
    · exact ih₂ hwε₂ hwe₂ hin
  case case7 ih =>
    rw [Set.mem_union] at hin
    rcases hin with hin | hin
    · exact mem_footprint_ofEntity_exists_wf hwε hp hin
    · exact ih (wf_εnv_for_getAttr_implies hwε) (hget hp) hin
  case case8 ih =>
    exact ih (wf_εnv_for_hasAttr_implies hwε) (hhas hp) hin
  case case9 ih =>
    exact ih (wf_εnv_for_extHasAttr_implies hwε) (hexthas hp) hin
  case case10 ih =>
    exact ih (wf_εnv_for_unaryApp_implies hwε) (happ₁ hp) hin
  case' case11 =>
    replace hwε := wf_εnv_for_call_implies hwε
    replace hwe := hcall hp
  case' case12 =>
    replace hwε := wf_εnv_for_set_implies hwε
    replace hwe := hset hp
  case case11 _ _ ih | case12 _ ih =>
    simp only [List.mapUnion₁_eq_mapUnion (footprint · εnv),
      List.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨xᵢ, hinᵢ, hin⟩ := hin
    exact ih xᵢ hinᵢ (hwε xᵢ hinᵢ) (hwe xᵢ hinᵢ) hin
  case case13 _ ih =>
    replace hwε := wf_εnv_for_record_implies hwε
    replace hwe := hrec hp
    simp only [List.mapUnion₂_eq_mapUnion λ y : Attr × Expr => footprint y.snd εnv,
      List.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨(aᵢ, xᵢ), hinᵢ, hin⟩ := hin
    simp only at hin ih
    exact ih aᵢ xᵢ (List.sizeOf_attach₂ hinᵢ) (hwε _ hinᵢ) (hwe _ hinᵢ) hin
  case case14 =>
    have _ := Set.not_mem_empty tₑ
    contradiction

theorem mem_footprint_exists_wf {x : Expr} {tₑ : Term} {env : Env} {εnv : SymEnv} :
  εnv.WellFormedFor x →
  env.WellFormedFor x →
  tₑ ∈ footprint x εnv →
  ∃ xₑ,
    εnv.WellFormedFor xₑ ∧
    env.WellFormedFor xₑ ∧
    compile xₑ εnv = .ok tₑ
:= by
  intro hwε hwe hin
  exact mem_footprint_exists_wf_prop hwε hwe hin
    wf_env_for_ite_implies wf_env_for_and_implies wf_env_for_or_implies
    wf_env_for_unaryApp_implies wf_env_for_binaryApp_implies
    wf_env_for_getAttr_implies wf_env_for_hasAttr_implies
    wf_env_for_extHasAttr_implies
    wf_env_for_set_implies wf_env_for_record_implies
    wf_env_for_call_implies

theorem mem_footprint_compile_exists_swf {x : Expr} {tₑ : Term} {env : Env} {εnv : SymEnv} :
  εnv.StronglyWellFormedFor x →
  env.StronglyWellFormedFor x →
  tₑ ∈ footprint x εnv →
  ∃ xₑ,
    εnv.StronglyWellFormedFor xₑ ∧
    env.StronglyWellFormedFor xₑ ∧
    compile xₑ εnv = .ok tₑ
:= by
  intro hsε hse hin
  have ⟨xᵢ, hwεᵢ, hweᵢ, h⟩ := mem_footprint_exists_wf (swf_εnv_for_implies_wf_for hsε) (swf_env_for_implies_wf_for hse) hin
  exists xᵢ
  simp only [h, and_true]
  constructor
  · exact And.intro hsε.left hwεᵢ.right
  · exact And.intro hse.left hweᵢ.right

theorem mem_footprint_wf {x : Expr} {tₑ : Term} {εnv : SymEnv} :
  εnv.WellFormedFor x →
  tₑ ∈ footprint x εnv →
  tₑ.WellFormed εnv.entities
:= by
  intro hwε hin
  have ⟨xₑ, hw, _, hr⟩ : ∃ xₑ, εnv.WellFormedFor xₑ ∧ (λ x => True) xₑ ∧ compile xₑ εnv = .ok tₑ := by
    apply mem_footprint_exists_wf_prop hwε _ hin
    all_goals simp only [and_self, imp_self, implies_true]
  simp only [compile_wf hw hr]

theorem mem_footprints_wf {xs : List Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormed)
  (hvr : ∀ x ∈ xs, εnv.entities.ValidRefsFor x)
  (hin : t ∈ footprints xs εnv) :
  t.WellFormed εnv.entities
:= by
  simp only [mem_footprints_iff] at hin
  replace ⟨x, hinₓ, hin⟩ := hin
  exact mem_footprint_wf (And.intro hwε (hvr x hinₓ)) hin

theorem footprints_empty {εnv : SymEnv} :
  footprints [] εnv = ∅
:= by
  simp [footprints, List.mapUnion_nil]

theorem footprints_singleton {x : Expr} {εnv : SymEnv} :
  footprints [x] εnv = footprint x εnv
:= by
  simp [SymCC.footprints, List.mapUnion_singleton (f := (footprint · εnv)) (by simp [footprint_wf])]

theorem footprints_append {xs₁ xs₂ : List Expr} {εnv : SymEnv} :
  footprints (xs₁ ++ xs₂) εnv = footprints xs₁ εnv ++ footprints xs₂ εnv
:= by
  simp [footprints]
  apply List.mapUnion_append
  intro x _ ; apply footprint_wf

theorem footprint_subset_footprints {x : Expr} {xs : List Expr} {εnv : SymEnv} :
  x ∈ xs → footprint x εnv ⊆ footprints xs εnv
:= by
  intro hx
  rw [Set.subset_def]
  intro t ht
  rw [mem_footprints_iff]
  exists x


end Cedar.Thm
