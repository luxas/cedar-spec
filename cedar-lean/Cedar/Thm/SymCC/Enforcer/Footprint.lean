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
    · exact Set.empty_wf
    · split
      · split
        · split
          · exact List.mapUnion_wf
          · exact footprintPred_wf _ _ _
        · exact footprintPred_wf _ _ _
      · exact Set.empty_wf
  · exact Set.empty_wf

/-- D-71 slot reductions: `footprintAllPred` collapses to the matching compile-path slot. -/
theorem footprintAllPred_none_eq {p : PredExpr} {x₁ : Expr} {εnv : SymEnv} {ty : TermType}
  (hr₁ : compile x₁ εnv = .ok (.none ty)) :
  footprintAllPred p x₁ εnv = Set.empty := by
  simp only [footprintAllPred, hr₁]

theorem footprintAllPred_litfold_eq {p : PredExpr} {x₁ : Expr} {εnv : SymEnv} {t₁ : Term} {vs : List Term} {ety : TermType}
  (hr₁ : compile x₁ εnv = .ok t₁) (hsome : ∃ u, t₁ = .some u)
  (hget : Factory.option.get t₁ = .set (Data.Set.mk vs) ety)
  (hlit : vs.all (·.isLiteral) = true) :
  footprintAllPred p x₁ εnv = vs.mapUnion (fun vi => footprintPred p (Factory.someOf vi) εnv) := by
  obtain ⟨u, hu⟩ := hsome; subst hu
  simp only [footprintAllPred, hr₁]
  simp only [Factory.option.get] at hget ⊢
  rw [hget]
  simp only [Term.typeOf, hlit, reduceIte]

theorem footprintAllPred_symbolic_eq {p : PredExpr} {x₁ : Expr} {εnv : SymEnv} {t₁ : Term} {elemTy : TermType}
  (hr₁ : compile x₁ εnv = .ok t₁) (hnotnone : ∀ ty, t₁ ≠ .none ty)
  (hgetty : (Factory.option.get t₁).typeOf = .set elemTy)
  (hnotlit : ∀ vs ety, Factory.option.get t₁ = .set (Data.Set.mk vs) ety → vs.all (·.isLiteral) = false) :
  footprintAllPred p x₁ εnv = footprintPred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv := by
  unfold footprintAllPred
  rw [hr₁]
  cases t₁ with
  | none ty => exact absurd rfl (hnotnone ty)
  | _ =>
    simp only [hgetty]
    generalize hg : Factory.option.get _ = g
    cases g with
    | set s ty => cases s with | mk vs =>
        have := hnotlit vs ty hg
        simp only [this, Bool.false_eq_true, reduceIte]
    | _ => rfl












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

/--
D-70 option A, step (2) bridge: for an `it`-free predicate `q`, its `footprintPred`
against any element term `it` equals the ordinary `footprint` of its `toExpr`. Both
sides key on the same compiled terms (via `compilePred_toExpr_eq`), and the
`q.mentionsIt` guard in `footprintPred.ofEntity` is discharged by `it`-freeness.
-/
theorem footprintPred_toExpr_eq {q : PredExpr} {it : Term} {εnv : SymEnv}
    (hfree : q.mentionsIt = false) :
    footprintPred q it εnv = footprint q.toExpr εnv := by
  match q, hfree with
  | .item, hfree => exact absurd hfree (by simp only [PredExpr.mentionsIt, Bool.true_eq_false, not_false_eq_true])
  | .lit l, _ =>
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred.ofEntity, footprint.ofEntity,
      compilePred_toExpr_eq (q := .lit l), PredExpr.mentionsIt, reduceIte, Bool.false_eq_true, if_false]
  | .var v, _ =>
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred.ofEntity, footprint.ofEntity,
      compilePred_toExpr_eq (q := .var v), PredExpr.mentionsIt, reduceIte, Bool.false_eq_true, if_false]
  | .ite c t e, hfree =>
    simp only [PredExpr.mentionsIt, Bool.or_eq_false_iff] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred.ofBranch, footprint.ofBranch,
      compilePred_toExpr_eq hfree.1.1,
      footprintPred_toExpr_eq hfree.1.1, footprintPred_toExpr_eq hfree.1.2, footprintPred_toExpr_eq hfree.2]
  | .and a b, hfree =>
    simp only [PredExpr.mentionsIt, Bool.or_eq_false_iff] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred.ofBranch, footprint.ofBranch,
      compilePred_toExpr_eq hfree.1, footprintPred_toExpr_eq hfree.1, footprintPred_toExpr_eq hfree.2]
  | .or a b, hfree =>
    simp only [PredExpr.mentionsIt, Bool.or_eq_false_iff] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred.ofBranch, footprint.ofBranch,
      compilePred_toExpr_eq hfree.1, footprintPred_toExpr_eq hfree.1, footprintPred_toExpr_eq hfree.2]
  | .unaryApp o e, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred_toExpr_eq hfree]
  | .hasAttr e a, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred_toExpr_eq hfree]
  | .extHasAttr e a l, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred_toExpr_eq hfree]
  | .binaryApp o a b, hfree =>
    simp only [PredExpr.mentionsIt, Bool.or_eq_false_iff] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred.ofEntity, footprint.ofEntity,
      compilePred_toExpr_eq (q := .binaryApp o a b), PredExpr.mentionsIt, hfree.1, hfree.2, Bool.or_self,
      reduceIte, Bool.false_eq_true, if_false, footprintPred_toExpr_eq hfree.1, footprintPred_toExpr_eq hfree.2]
  | .getAttr e a, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr, footprintPred.ofEntity, footprint.ofEntity,
      compilePred_toExpr_eq (q := .getAttr e a), PredExpr.mentionsIt, hfree, reduceIte, Bool.false_eq_true, if_false,
      footprintPred_toExpr_eq hfree]
  | .record axs, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr]
    rw [List.map₂_eq_map (λ p : Attr × PredExpr => (p.fst, p.snd.toExpr))]
    rw [List.mapUnion₂_eq_mapUnion λ y : Attr × PredExpr => footprintPred y.snd it εnv,
        List.mapUnion₂_eq_mapUnion λ y : Attr × Expr => footprint y.snd εnv, List.mapUnion_map]
    apply List.mapUnion_congr
    intro x hx
    have hxfree : x.snd.mentionsIt = false := by
      have hall : (axs.attach₂.all (fun y => !y.val.snd.mentionsIt)) = true := by
        rw [← List.not_any_eq_all_not]; simp only [hfree, Bool.not_false]
      rw [show (fun (y : {z : Attr × PredExpr // sizeOf z.snd < 1 + sizeOf axs}) => !y.val.snd.mentionsIt)
            = (fun (y : {z : Attr × PredExpr // sizeOf z.snd < 1 + sizeOf axs}) =>
                (fun (p : Attr × PredExpr) => !p.snd.mentionsIt) y.val) from rfl,
          List.all_attach₂ (f := fun (p : Attr × PredExpr) => !p.snd.mentionsIt), List.all_eq_true] at hall
      have := hall x hx; simp only [Bool.not_eq_true'] at this; exact this
    simp only [Function.comp, footprintPred_toExpr_eq hxfree]
  | .call f xs, hfree =>
    simp only [PredExpr.mentionsIt] at hfree
    simp only [footprintPred, footprint, PredExpr.toExpr]
    rw [List.map₁_eq_map (λ e : PredExpr => e.toExpr)]
    rw [List.mapUnion₁_eq_mapUnion (λ x => footprintPred x it εnv),
        List.mapUnion₁_eq_mapUnion (λ x => footprint x εnv), List.mapUnion_map]
    apply List.mapUnion_congr
    intro x hx
    have hxfree : x.mentionsIt = false := by
      rw [List.any_eq_false] at hfree
      have := hfree ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩)
      simp only [Bool.not_eq_true] at this; exact this
    simp only [Function.comp, footprintPred_toExpr_eq hxfree]
termination_by sizeOf q
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have h := ‹_ ∈ _›; have := List.sizeOf_snd_lt_sizeOf_list h; omega)
      | (have h := ‹_ ∈ _›; have := List.sizeOf_lt_of_mem h; omega)

/--
`toExpr` preserves entity-reference validity: a predicate whose refs are all valid
maps to an expression whose refs are all valid (`.item ↦ .var .principal` is
`var_valid`). Needed so the D-70 option-A `.all` footprint witnesses `q.toExpr`
(of `it`-free quantifier subterms) are well-formed.
-/
theorem PredExpr.toExpr_validRefs {validRef : EntityUID → Prop} {q : PredExpr} :
  q.ValidRefs validRef → q.toExpr.ValidRefs validRef
:= by
  intro h
  induction h with
  | item_valid => simp only [PredExpr.toExpr, itExpr]; exact Expr.ValidRefs.var_valid
  | lit_valid h₁ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.lit_valid h₁
  | var_valid => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.var_valid
  | ite_valid _ _ _ ih₁ ih₂ ih₃ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.ite_valid ih₁ ih₂ ih₃
  | and_valid _ _ ih₁ ih₂ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.and_valid ih₁ ih₂
  | or_valid _ _ ih₁ ih₂ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.or_valid ih₁ ih₂
  | binaryApp_valid _ _ ih₁ ih₂ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.binaryApp_valid ih₁ ih₂
  | unaryApp_valid _ ih₁ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.unaryApp_valid ih₁
  | hasAttr_valid _ ih₁ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.hasAttr_valid ih₁
  | extHasAttr_valid _ ih₁ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.extHasAttr_valid ih₁
  | getAttr_valid _ ih₁ => simp only [PredExpr.toExpr]; exact Expr.ValidRefs.getAttr_valid ih₁
  | @record_valid axs h₁ ih =>
    simp only [PredExpr.toExpr]
    rw [List.map₂_eq_map (λ p : Attr × PredExpr => (p.fst, p.snd.toExpr))]
    apply Expr.ValidRefs.record_valid
    intro ax hax
    simp only [List.mem_map] at hax
    replace ⟨⟨a, e⟩, hin, heq⟩ := hax
    subst heq
    exact ih (a, e) hin
  | @call_valid f xs h₁ ih =>
    simp only [PredExpr.toExpr]
    rw [List.map₁_eq_map (λ e : PredExpr => e.toExpr)]
    apply Expr.ValidRefs.call_valid
    intro x hx
    simp only [List.mem_map] at hx
    replace ⟨e, hin, heq⟩ := hx
    subst heq
    exact ih e hin

/--
Leaf of the `.all` predicate-branch witness: a term in `footprintPred.ofEntity`
of an `it`-free quantifier subterm `q` is exactly `compile q.toExpr εnv`, so
`q.toExpr` is the witnessing expression.
-/
private theorem mem_footprintPred_ofEntity_exists {q : PredExpr} {it tₑ : Term} {εnv : SymEnv}
  (hin : tₑ ∈ footprintPred.ofEntity it εnv q) :
  q.mentionsIt = false ∧ compile q.toExpr εnv = .ok tₑ
:= by
  simp only [footprintPred.ofEntity] at hin
  split at hin
  · simp only [Set.not_mem_empty] at hin
  · rename_i hfree
    rw [Bool.not_eq_true] at hfree
    split at hin
    · split at hin
      · rename_i hok _
        rw [Set.mem_singleton] at hin
        subst hin
        exact ⟨hfree, by rw [← compilePred_toExpr_eq hfree]; exact hok⟩
      · simp only [Set.not_mem_empty] at hin
    · simp only [Set.not_mem_empty] at hin


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
    · simp only [Set.not_mem_empty] at hin
    · split at hin
      · split at hin
        · split at hin
          · simp only [List.mem_mapUnion_iff_mem_exists] at hin
            replace ⟨vi, _, hin⟩ := hin
            exact mem_footprintPred_option_entity hin
          · exact mem_footprintPred_option_entity hin
        · exact mem_footprintPred_option_entity hin
      · simp only [Set.not_mem_empty] at hin
  · simp only [Set.not_mem_empty] at hin

/--
Witness for the `.all` predicate branch: every term in `footprintPred p it εnv`
is the compiled `toExpr` of some `it`-free sub-predicate `q` of `p`, and when `p`
has valid refs so does `q`. The witnessing expression `q.toExpr` is therefore a
well-formed ordinary expression compiling to the term (D-70, option A).
-/
theorem mem_footprintPred_exists {p : PredExpr} {it tₑ : Term} {εnv : SymEnv}
  (hin : tₑ ∈ footprintPred p it εnv) :
  ∃ q : PredExpr, q.mentionsIt = false ∧ (∀ vr, p.ValidRefs vr → q.ValidRefs vr) ∧ compile q.toExpr εnv = .ok tₑ
:= by
  induction p using footprintPred.induct generalizing tₑ <;> simp only [footprintPred] at hin
  case case1 => simp only [Set.not_mem_empty] at hin
  case case2 | case3 =>
    have ⟨hfree, hok⟩ := mem_footprintPred_ofEntity_exists hin
    exact ⟨_, hfree, (fun _ h => h), hok⟩
  case case4 ih₁ ih₂ ih₃ =>
    rcases mem_footprintPred_ofBranch_mem hin with hin | hin | hin
    · have ⟨q, hf, himp, hok⟩ := ih₁ hin
      exact ⟨q, hf, (fun _ h => by cases h with | ite_valid hv₁ _ _ => exact himp _ hv₁), hok⟩
    · have ⟨q, hf, himp, hok⟩ := ih₂ hin
      exact ⟨q, hf, (fun _ h => by cases h with | ite_valid _ hv₂ _ => exact himp _ hv₂), hok⟩
    · have ⟨q, hf, himp, hok⟩ := ih₃ hin
      exact ⟨q, hf, (fun _ h => by cases h with | ite_valid _ _ hv₃ => exact himp _ hv₃), hok⟩
  case case5 ih₁ ih₂ =>
    rcases mem_footprintPred_ofBranch_mem hin with hin | hin | hin
    · have ⟨q, hf, himp, hok⟩ := ih₁ hin
      exact ⟨q, hf, (fun _ h => by cases h with | and_valid hv₁ _ => exact himp _ hv₁), hok⟩
    · have ⟨q, hf, himp, hok⟩ := ih₂ hin
      exact ⟨q, hf, (fun _ h => by cases h with | and_valid _ hv₂ => exact himp _ hv₂), hok⟩
    · simp only [Set.not_mem_empty] at hin
  case case6 ih₁ ih₂ =>
    rcases mem_footprintPred_ofBranch_mem hin with hin | hin | hin
    · have ⟨q, hf, himp, hok⟩ := ih₁ hin
      exact ⟨q, hf, (fun _ h => by cases h with | or_valid hv₁ _ => exact himp _ hv₁), hok⟩
    · simp only [Set.not_mem_empty] at hin
    · have ⟨q, hf, himp, hok⟩ := ih₂ hin
      exact ⟨q, hf, (fun _ h => by cases h with | or_valid _ hv₂ => exact himp _ hv₂), hok⟩
  case case7 ih₁ ih₂ =>
    simp only [Set.mem_union] at hin
    rcases hin with (hin | hin) | hin
    · have ⟨hfree, hok⟩ := mem_footprintPred_ofEntity_exists hin
      exact ⟨_, hfree, (fun _ h => h), hok⟩
    · have ⟨q, hf, himp, hok⟩ := ih₁ hin
      exact ⟨q, hf, (fun _ h => by cases h with | binaryApp_valid hv₁ _ => exact himp _ hv₁), hok⟩
    · have ⟨q, hf, himp, hok⟩ := ih₂ hin
      exact ⟨q, hf, (fun _ h => by cases h with | binaryApp_valid _ hv₂ => exact himp _ hv₂), hok⟩
  case case8 ih =>
    simp only [Set.mem_union] at hin
    rcases hin with hin | hin
    · have ⟨hfree, hok⟩ := mem_footprintPred_ofEntity_exists hin
      exact ⟨_, hfree, (fun _ h => h), hok⟩
    · have ⟨q, hf, himp, hok⟩ := ih hin
      exact ⟨q, hf, (fun _ h => by cases h with | getAttr_valid hv₁ => exact himp _ hv₁), hok⟩
  case case9 ih =>
    have ⟨q, hf, himp, hok⟩ := ih hin
    exact ⟨q, hf, (fun _ h => by cases h with | hasAttr_valid hv₁ => exact himp _ hv₁), hok⟩
  case case10 ih =>
    have ⟨q, hf, himp, hok⟩ := ih hin
    exact ⟨q, hf, (fun _ h => by cases h with | extHasAttr_valid hv₁ => exact himp _ hv₁), hok⟩
  case case11 ih =>
    have ⟨q, hf, himp, hok⟩ := ih hin
    exact ⟨q, hf, (fun _ h => by cases h with | unaryApp_valid hv₁ => exact himp _ hv₁), hok⟩
  case case12 ih =>
    simp only [List.mapUnion₁_eq_mapUnion (footprintPred · it εnv), List.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨xᵢ, hinᵢ, hin⟩ := hin
    have ⟨q, hf, himp, hok⟩ := ih xᵢ hinᵢ hin
    exact ⟨q, hf, (fun _ h => by cases h with | call_valid hv => exact himp _ (hv xᵢ hinᵢ)), hok⟩
  case case13 ih =>
    simp only [List.mapUnion₂_eq_mapUnion λ y : Attr × PredExpr => footprintPred y.snd it εnv,
      List.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨(aᵢ, xᵢ), hinᵢ, hin⟩ := hin
    simp only at hin ih
    have ⟨q, hf, himp, hok⟩ := ih aᵢ xᵢ (List.sizeOf_attach₂ hinᵢ) hin
    exact ⟨q, hf, (fun _ h => by cases h with | record_valid hv => exact himp _ (hv (aᵢ, xᵢ) hinᵢ)), hok⟩


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
  (hcall : ∀ {f xs}, p (Expr.call f xs) → ∀ x ∈ xs, p x)
  (hall  : ∀ {x₁ p'}, p (Expr.all x₁ p') → p x₁)
  (hallp : ∀ {x₁ : Expr} {p' q : PredExpr}, p (Expr.all x₁ p') → εnv.WellFormedFor (Expr.all x₁ p') →
            q.mentionsIt = false → (∀ vr, p'.ValidRefs vr → q.ValidRefs vr) →
            εnv.WellFormedFor q.toExpr ∧ p q.toExpr) :
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
  case case14 x₁ p' ih =>
    simp only [Set.mem_union] at hin
    -- receiver well-formedness: εnv.WellFormedFor (.all x₁ p') gives x₁.ValidRefs
    have hwεrecv : εnv.WellFormedFor x₁ := by
      have ⟨hwf, hvr⟩ := hwε
      cases hvr with | all_valid hv₁ _ => exact ⟨hwf, hv₁⟩
    rcases hin with hin | hin
    · exact ih hwεrecv (hall hp) hin
    · -- predicate branch: witness q.toExpr via mem_footprintPred_exists
      simp only [footprintAllPred] at hin
      split at hin
      · split at hin
        · simp only [Set.not_mem_empty] at hin
        · split at hin
          · split at hin
            · split at hin
              · simp only [List.mem_mapUnion_iff_mem_exists] at hin
                replace ⟨vi, _, hin⟩ := hin
                have ⟨q, hfree, himp, hok⟩ := mem_footprintPred_exists hin
                have ⟨hwεq, hpq⟩ := hallp hp hwε hfree himp
                exact ⟨q.toExpr, hwεq, hpq, hok⟩
              · have ⟨q, hfree, himp, hok⟩ := mem_footprintPred_exists hin
                have ⟨hwεq, hpq⟩ := hallp hp hwε hfree himp
                exact ⟨q.toExpr, hwεq, hpq, hok⟩
            · have ⟨q, hfree, himp, hok⟩ := mem_footprintPred_exists hin
              have ⟨hwεq, hpq⟩ := hallp hp hwε hfree himp
              exact ⟨q.toExpr, hwεq, hpq, hok⟩
          · simp only [Set.not_mem_empty] at hin
      · simp only [Set.not_mem_empty] at hin

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
    (fun h => ⟨h.1, by cases h.2 with | all_valid hv₁ _ => exact hv₁⟩)
    (fun he hε hfree himp => by
      refine ⟨⟨hε.1, ?_⟩, ⟨he.1, ?_⟩⟩
      · have hp' := by cases hε.2 with | all_valid _ hv => exact hv
        exact PredExpr.toExpr_validRefs (himp _ hp')
      · have hp' := by cases he.2 with | all_valid _ hv => exact hv
        exact PredExpr.toExpr_validRefs (himp _ hp'))

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
    case hallp =>
      intro x₁ p' q _ hε hfree himp
      refine ⟨⟨hε.1, ?_⟩, trivial⟩
      have hp' := by cases hε.2 with | all_valid _ hv => exact hv
      exact PredExpr.toExpr_validRefs (himp _ hp')
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
