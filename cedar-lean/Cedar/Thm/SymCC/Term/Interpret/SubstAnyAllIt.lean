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

module

import Cedar.Data.SizeOf
public import Cedar.SymCC.Env
public import Cedar.SymCC.Interpretation
public import Cedar.SymCC.Term
import Cedar.Thm.SymCC.Data
import all Cedar.Thm.SymCC.Term.Interpret.Basic
public import Cedar.Thm.SymCC.Term.WF
import all Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Term.PE
import all Cedar.Thm.SymCC.Interpretation

/-! Lemmas relating `Term.substAnyAllIt` and `Term.interpretWith` (D-55). -/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

/-- `interpretWith σ`'s `.app` arm reduces for a non-`set.all` op. -/
theorem interpretWith_app_ne_setAll {σ : Option Term} {I : Interpretation}
  {op : Op} {ts : List Term} {ty : TermType} (hop : op ≠ Op.set.all) :
  Term.interpretWith σ I (.app op ts ty)
    = op.interpret I (ts.map₁ (fun x => Term.interpretWith σ I x.val)) ty := by
  cases op <;> first | exact absurd rfl hop | simp only [Term.interpretWith]

/-- `interpret`'s `.app` arm reduces for a non-`set.all` op. -/
theorem interpret_app_ne_setAll {I : Interpretation}
  {op : Op} {ts : List Term} {ty : TermType} (hop : op ≠ Op.set.all) :
  Term.interpret I (.app op ts ty)
    = op.interpret I (ts.map₁ (fun x => Term.interpret I x.val)) ty := by
  simp only [Term.interpret]
  rw [interpretWith_app_ne_setAll hop]

/-- `Set.map` fusion. -/
theorem set_map_map [LT α] [DecidableLT α] [StrictLT α] [LT β] [DecidableLT β] [StrictLT β]
  [LT γ] [DecidableLT γ] [StrictLT γ] {f : α → β} {g : β → γ} {s : Set α} :
  (s.map f).map g = s.map (g ∘ f) := by
  simp only [Set.map_def]
  rw [Set.make_make_eqv]
  have h1 : (Set.make (s.elts.map f)).elts ≡ s.elts.map f := Set.elts_make_eqv
  have h2 := List.map_equiv g _ _ h1
  rw [List.map_map] at h2
  exact h2

/-- `NoSetAll` extracts to set elements. -/
theorem noSetAll_set {ts : Set Term} {ty : TermType}
  (h : Term.NoSetAll (.set ts ty) = true) : ∀ t ∈ ts.elts, Term.NoSetAll t = true := by
  simp only [Term.NoSetAll, Set.all₁_eq_all, Set.all_eq_true] at h
  intro t ht; exact h t ht

/-- `NoSetAll` extracts to record values. -/
theorem noSetAll_record {ats : Map Attr Term}
  (h : Term.NoSetAll (.record ats) = true) : ∀ p ∈ ats.toList, Term.NoSetAll p.2 = true := by
  simp only [Term.NoSetAll, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at h
  intro p hp; exact h p.1 p.2 hp

/-- A non-`set.all` app with `NoSetAll` extracts to `op ≠ set.all` and its args. -/
theorem noSetAll_app {op : Op} {ts : List Term} {ty : TermType}
  (h : Term.NoSetAll (.app op ts ty) = true) :
  op ≠ Op.set.all ∧ ∀ t ∈ ts, Term.NoSetAll t = true := by
  by_cases hop : op = Op.set.all
  · subst hop; simp only [Term.NoSetAll, Bool.false_eq_true] at h
  · refine ⟨hop, ?_⟩
    have h' : (ts.attach.all (fun x => Term.NoSetAll x.val)) = true := by
      cases op <;> first | exact absurd rfl hop | (simp only [Term.NoSetAll] at h ⊢; exact h)
    rw [List.all_eq_true] at h'
    intro t ht
    exact h' ⟨t, ht⟩ (List.mem_attach ts ⟨t, ht⟩)

/--
**Lemma A.** For a term `t` with no nested `set.all` node (`NoSetAll t`) and an
interpretation-stable substituend `v` (`interpret I v = v`, true for literals),
substituting the bound variable `v` then interpreting equals interpreting with
the bound variable bound to `v`. The `NoSetAll` side condition is essential:
`substAnyAllIt` rebuilds a `set.all` node via the generic `.app` arm, whereas
`interpretWith (some v)` folds it. -/
theorem interpretWith_some_eq_interpret_substAnyAllIt
  {I : Interpretation} {v : Term} (hv : Term.interpret I v = v) :
  ∀ t : Term, Term.NoSetAll t = true →
    Term.interpretWith (some v) I t = Term.interpret I (Term.substAnyAllIt v t)
  | .prim p, _ => by
    simp only [Term.interpretWith, Term.substAnyAllIt, interpret_term_prim]
  | .var w, _ => by
    simp only [Term.interpretWith, Term.substAnyAllIt]
    by_cases h : w.id = "!anyall!it"
    · simp only [h, reduceIte, hv]
    · simp only [h, reduceIte, interpret_term_var]
  | .none ty, _ => by
    simp only [Term.interpretWith, Term.substAnyAllIt, interpret_term_none, noneOf]
  | .some t, hn => by
    have hnt : Term.NoSetAll t = true := by simp only [Term.NoSetAll] at hn; exact hn
    simp only [Term.interpretWith, Term.substAnyAllIt, interpret_term_some, someOf,
      interpretWith_some_eq_interpret_substAnyAllIt hv t hnt]
  | .set ts ty, hn => by
    have hmem := noSetAll_set hn
    simp only [Term.interpretWith, Term.substAnyAllIt, interpret_term_set, Set.map₁_eq_map,
      set_map_map]
    apply congrArg (Term.set · ty)
    apply Set.map_congr
    intro t ht
    simp only [Function.comp_apply]
    exact interpretWith_some_eq_interpret_substAnyAllIt hv t (hmem t ht)
  | .record ats, hn => by
    have hmem := noSetAll_record hn
    simp only [Term.interpretWith, Term.substAnyAllIt, interpret_term_record,
      Map.mapOnValues₂_eq_mapOnValues, Map.mapOnValues_mapOnValues]
    apply congrArg Term.record
    apply Map.mapOnValues_congr
    intro w hw
    rcases Map.in_values_exists_key hw with ⟨a, ha⟩
    simp only [Function.comp_apply]
    exact interpretWith_some_eq_interpret_substAnyAllIt hv w (hmem (a, w) ha)
  | .app op ts ty, hn => by
    have ⟨hop, hmem⟩ := noSetAll_app hn
    rw [interpretWith_app_ne_setAll hop, Term.substAnyAllIt, interpret_app_ne_setAll hop]
    congr 1
    simp only [List.map₁_eq_map, List.map_map]
    apply List.map_congr
    intro t ht
    simp only [Function.comp_apply]
    exact interpretWith_some_eq_interpret_substAnyAllIt hv t (hmem t ht)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts.elts›; omega)
      | (rename_i a ha
         have h1 := List.sizeOf_lt_of_mem ha
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1
         omega)
      | (have := Map.sizeOf_lt_of_toList ats; simp only at *; omega)
      | omega

/--
**Lemma B (typeOf).** `substAnyAllIt v` preserves `typeOf` when `v` has the same
type as every bound-variable occurrence. `.app`/`.set` store their type, so only
`.var "!anyall!it"` leaves can change it. -/
theorem substAnyAllIt_typeOf {v : Term} :
  ∀ t : Term, Term.anyAllItTyped v.typeOf t = true → (Term.substAnyAllIt v t).typeOf = t.typeOf
  | .prim _, _ => by simp only [Term.substAnyAllIt]
  | .var w, ht => by
    simp only [Term.substAnyAllIt]
    by_cases h : w.id = "!anyall!it"
    · simp only [h, reduceIte, Term.typeOf]
      simp only [Term.anyAllItTyped, h, reduceIte, decide_eq_true_eq] at ht
      exact ht.symm
    · simp only [h, reduceIte]
  | .none _, _ => by simp only [Term.substAnyAllIt]
  | .some t, ht => by
    have : Term.anyAllItTyped v.typeOf t = true := by simp only [Term.anyAllItTyped] at ht; exact ht
    simp only [Term.substAnyAllIt, Term.typeOf, substAnyAllIt_typeOf t this]
  | .set _ _, _ => by simp only [Term.substAnyAllIt, Term.typeOf]
  | .app _ _ _, _ => by simp only [Term.substAnyAllIt, Term.typeOf]
  | .record ats, ht => by
    have hmem : ∀ p ∈ ats.toList, Term.anyAllItTyped v.typeOf p.2 = true := by
      simp only [Term.anyAllItTyped, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at ht
      intro p hp; exact ht p.1 p.2 hp
    simp only [Term.substAnyAllIt, Term.typeOf, Map.mapOnValues₂_eq_mapOnValues,
      Map.mapOnValues_mapOnValues]
    apply congrArg (TermType.record ·)
    apply Map.mapOnValues_congr
    intro w hw
    rcases Map.in_values_exists_key hw with ⟨a, ha⟩
    simp only [Function.comp_apply]
    exact substAnyAllIt_typeOf w (hmem (a, w) ha)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (rename_i a ha
         have h1 := List.sizeOf_lt_of_mem ha
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1
         omega)

/-- `ExtOp.WellTyped` transport across `substAnyAllIt`. -/
theorem extOp_wellTyped_substAnyAllIt {v : Term} {xop : ExtOp} {ts : List Term} {ty : TermType}
  (hta : ∀ t : Term, t ∈ ts → Term.anyAllItTyped v.typeOf t = true) :
  ExtOp.WellTyped xop ts ty →
  ExtOp.WellTyped xop (ts.map (Term.substAnyAllIt v)) ty := by
  intro hwt
  have hT : ∀ t : Term, t ∈ ts → (Term.substAnyAllIt v t).typeOf = t.typeOf :=
    fun t ht => substAnyAllIt_typeOf t (hta t ht)
  cases hwt <;>
    (try simp only [List.map_cons, List.map_nil]) <;>
    first
      | exact ExtOp.WellTyped.decimal.val_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.ipaddr.isV4_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.ipaddr.addrV4_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.ipaddr.prefixV4_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.ipaddr.addrV6_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.ipaddr.prefixV6_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.datetime.val_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.datetime.ofBitVec_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.duration.val_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact ExtOp.WellTyped.duration.ofBitVec_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)

/-- `substAnyAllIt v` preserves `NoSetAll` when `v` itself has no `set.all`. -/
theorem substAnyAllIt_noSetAll {v : Term} (hvn : v.NoSetAll = true) :
  ∀ t : Term, Term.NoSetAll t = true → Term.NoSetAll (Term.substAnyAllIt v t) = true
  | .prim _, _ => by simp only [Term.substAnyAllIt, Term.NoSetAll]
  | .var w, _ => by
    simp only [Term.substAnyAllIt]
    by_cases h : w.id = "!anyall!it"
    · simp only [h, reduceIte]; exact hvn
    · simp only [h, reduceIte, Term.NoSetAll]
  | .none _, _ => by simp only [Term.substAnyAllIt, Term.NoSetAll]
  | .some t, hn => by
    have : Term.NoSetAll t = true := by simp only [Term.NoSetAll] at hn; exact hn
    simp only [Term.substAnyAllIt, Term.NoSetAll, substAnyAllIt_noSetAll hvn t this]
  | .set ts ty, hn => by
    have hmem := noSetAll_set hn
    simp only [Term.substAnyAllIt, Term.NoSetAll, Set.map₁_eq_map]
    rw [Set.all₁_eq_all, Set.all_eq_true]
    intro t ht
    rw [Set.mem_map] at ht
    rcases ht with ⟨t', ht', rfl⟩
    exact substAnyAllIt_noSetAll hvn t' (hmem t' ht')
  | .record ats, hn => by
    have hmem := noSetAll_record hn
    simp only [Term.substAnyAllIt, Term.NoSetAll, Map.mapOnValues₂_eq_mapOnValues,
      List.all_attach₂_snd, List.all_eq_true, Prod.forall]
    intro a t' ht'
    rcases Map.in_mapOnValues_in_toList' ht' with ⟨t'', rfl, hmem'⟩
    exact substAnyAllIt_noSetAll hvn t'' (hmem (a, t'') hmem')
  | .app op ts ty, hn => by
    have ⟨hop, hmem⟩ := noSetAll_app hn
    simp only [Term.substAnyAllIt]
    cases op <;> first
      | exact absurd rfl hop
      | (simp only [Term.NoSetAll, List.map₁_eq_map, List.map_map, List.all_eq_true, List.mem_map,
           Function.comp_apply]
         intro x _
         rcases List.mem_map.mp x.property with ⟨t', ht', heq⟩
         rw [← heq]
         exact substAnyAllIt_noSetAll hvn t' (hmem t' ht'))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)
      | omega

/-- `substAnyAllIt v` preserves `anyAllItTyped ety` when `v` does. -/
theorem substAnyAllIt_anyAllItTyped {v : Term} {ety : TermType}
  (hvt : Term.anyAllItTyped ety v = true) :
  ∀ t : Term, Term.anyAllItTyped ety t = true → Term.anyAllItTyped ety (Term.substAnyAllIt v t) = true
  | .prim _, _ => by simp only [Term.substAnyAllIt, Term.anyAllItTyped]
  | .var w, _ => by
    simp only [Term.substAnyAllIt]
    by_cases h : w.id = "!anyall!it"
    · simp only [h, reduceIte]; exact hvt
    · simp only [h, reduceIte, Term.anyAllItTyped]
  | .none _, _ => by simp only [Term.substAnyAllIt, Term.anyAllItTyped]
  | .some t, hn => by
    have : Term.anyAllItTyped ety t = true := by simp only [Term.anyAllItTyped] at hn; exact hn
    simp only [Term.substAnyAllIt, Term.anyAllItTyped, substAnyAllIt_anyAllItTyped hvt t this]
  | .set ts ty, hn => by
    have hmem : ∀ t ∈ ts.elts, Term.anyAllItTyped ety t = true := by
      simp only [Term.anyAllItTyped, Set.all₁_eq_all, Set.all_eq_true] at hn; exact hn
    simp only [Term.substAnyAllIt, Term.anyAllItTyped, Set.map₁_eq_map]
    rw [Set.all₁_eq_all, Set.all_eq_true]
    intro t ht
    rw [Set.mem_map] at ht
    rcases ht with ⟨t', ht', rfl⟩
    exact substAnyAllIt_anyAllItTyped hvt t' (hmem t' ht')
  | .record ats, hn => by
    have hmem : ∀ p ∈ ats.toList, Term.anyAllItTyped ety p.2 = true := by
      simp only [Term.anyAllItTyped, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at hn
      intro p hp; exact hn p.1 p.2 hp
    simp only [Term.substAnyAllIt, Term.anyAllItTyped, Map.mapOnValues₂_eq_mapOnValues,
      List.all_attach₂_snd, List.all_eq_true, Prod.forall]
    intro a t' ht'
    rcases Map.in_mapOnValues_in_toList' ht' with ⟨t'', rfl, hmem'⟩
    exact substAnyAllIt_anyAllItTyped hvt t'' (hmem (a, t'') hmem')
  | .app op ts ty, hn => by
    have hmem : ∀ t ∈ ts, Term.anyAllItTyped ety t = true := by
      have h' : (ts.attach.all (fun x => Term.anyAllItTyped ety x.val)) = true := by
        simp only [Term.anyAllItTyped] at hn; exact hn
      rw [List.all_eq_true] at h'
      intro t ht; exact h' ⟨t, ht⟩ (List.mem_attach ts ⟨t, ht⟩)
    simp only [Term.substAnyAllIt, Term.anyAllItTyped, List.map₁_eq_map, List.map_map,
      List.all_eq_true, List.mem_map, Function.comp_apply]
    intro x _
    rcases List.mem_map.mp x.property with ⟨t', ht', heq⟩
    rw [← heq]
    exact substAnyAllIt_anyAllItTyped hvt t' (hmem t' ht')
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)
      | omega

/-- A literal has no `set.all` node. -/
theorem isLiteral_noSetAll : ∀ t : Term, t.isLiteral = true → Term.NoSetAll t = true
  | .prim _, _ => by simp only [Term.NoSetAll]
  | .none _, _ => by simp only [Term.NoSetAll]
  | .some t, h => by
    have : t.isLiteral = true := by simp only [Term.isLiteral] at h; exact h
    simp only [Term.NoSetAll, isLiteral_noSetAll t this]
  | .set ts _, h => by
    simp only [Term.isLiteral, Set.all₁_eq_all, Set.all_eq_true] at h
    simp only [Term.NoSetAll, Set.all₁_eq_all, Set.all_eq_true]
    intro t ht; exact isLiteral_noSetAll t (h t ht)
  | .record ats, h => by
    simp only [Term.isLiteral, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at h
    simp only [Term.NoSetAll, List.all_attach₂_snd, List.all_eq_true, Prod.forall]
    intro a t ht; exact isLiteral_noSetAll t (h a t ht)
  | .var _, h => by simp only [Term.isLiteral, Bool.false_eq_true] at h
  | .app _ _ _, h => by simp only [Term.isLiteral, Bool.false_eq_true] at h
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)

theorem isLiteral_anyAllItTyped {ety : TermType} : ∀ t : Term, t.isLiteral = true → Term.anyAllItTyped ety t = true
  | .prim _, _ => by simp only [Term.anyAllItTyped]
  | .none _, _ => by simp only [Term.anyAllItTyped]
  | .some t, h => by
    have : t.isLiteral = true := by simp only [Term.isLiteral] at h; exact h
    simp only [Term.anyAllItTyped, isLiteral_anyAllItTyped t this]
  | .set ts _, h => by
    simp only [Term.isLiteral, Set.all₁_eq_all, Set.all_eq_true] at h
    simp only [Term.anyAllItTyped, Set.all₁_eq_all, Set.all_eq_true]
    intro t ht; exact isLiteral_anyAllItTyped t (h t ht)
  | .record ats, h => by
    simp only [Term.isLiteral, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at h
    simp only [Term.anyAllItTyped, List.all_attach₂_snd, List.all_eq_true, Prod.forall]
    intro a t ht; exact isLiteral_anyAllItTyped t (h a t ht)
  | .var _, h => by simp only [Term.isLiteral, Bool.false_eq_true] at h
  | .app _ _ _, h => by simp only [Term.isLiteral, Bool.false_eq_true] at h
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)

/-- A literal term mentions no reserved `!anyall!it` variable (D-62). -/
theorem isLiteral_noAnyAllItVar : ∀ t : Term, t.isLiteral = true → Term.NoAnyAllItVar t = true
  | .prim _, _ => by simp only [Term.NoAnyAllItVar]
  | .none _, _ => by simp only [Term.NoAnyAllItVar]
  | .some t, h => by
    have : t.isLiteral = true := by simp only [Term.isLiteral] at h; exact h
    simp only [Term.NoAnyAllItVar, isLiteral_noAnyAllItVar t this]
  | .set ts _, h => by
    simp only [Term.isLiteral, Set.all₁_eq_all, Set.all_eq_true] at h
    simp only [Term.NoAnyAllItVar, Set.all₁_eq_all, Set.all_eq_true]
    intro t ht; exact isLiteral_noAnyAllItVar t (h t ht)
  | .record ats, h => by
    simp only [Term.isLiteral, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at h
    simp only [Term.NoAnyAllItVar, List.all_attach₂_snd, List.all_eq_true, Prod.forall]
    intro a t ht; exact isLiteral_noAnyAllItVar t (h a t ht)
  | .var _, h => by simp only [Term.isLiteral, Bool.false_eq_true] at h
  | .app _ _ _, h => by simp only [Term.isLiteral, Bool.false_eq_true] at h
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)

/-- A term with no reserved `!anyall!it` variable is `anyAllItTyped` for every `ety`
(there is no reserved occurrence to constrain). D-62 bridge. -/
theorem noAnyAllItVar_anyAllItTyped {ety : TermType} :
    ∀ t : Term, t.NoAnyAllItVar = true → Term.anyAllItTyped ety t = true
  | .prim _, _ => by simp only [Term.anyAllItTyped]
  | .none _, _ => by simp only [Term.anyAllItTyped]
  | .var w, h => by
    simp only [Term.NoAnyAllItVar, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at h
    simp only [Term.anyAllItTyped]
    split
    · rename_i heq; exact absurd heq h
    · rfl
  | .some t, h => by
    simp only [Term.NoAnyAllItVar] at h
    simp only [Term.anyAllItTyped, noAnyAllItVar_anyAllItTyped t h]
  | .set ts _, h => by
    simp only [Term.NoAnyAllItVar, Set.all₁_eq_all, Set.all_eq_true] at h
    simp only [Term.anyAllItTyped, Set.all₁_eq_all, Set.all_eq_true]
    intro t ht; exact noAnyAllItVar_anyAllItTyped t (h t ht)
  | .record ats, h => by
    simp only [Term.NoAnyAllItVar, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at h
    simp only [Term.anyAllItTyped, List.all_attach₂_snd, List.all_eq_true, Prod.forall]
    intro a t ht; exact noAnyAllItVar_anyAllItTyped t (h a t ht)
  | .app op ts ty, h => by
    simp only [Term.NoAnyAllItVar] at h
    rw [List.all_eq_true] at h
    simp only [Term.anyAllItTyped]
    rw [List.all_eq_true]
    rintro ⟨t, ht⟩ _
    have hmem : t ∈ ts := ht
    exact noAnyAllItVar_anyAllItTyped t (h ⟨t, ht⟩ (List.mem_attach ts ⟨t, ht⟩))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts.elts›; omega)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)

/-- `Term.interpret` fixes well-formed literals. Self-contained (no Lit import). -/
theorem interpret_lit_id {εs : SymEntities} {I : Interpretation} :
  ∀ t : Term, t.WellFormed εs → t.isLiteral = true → Term.interpret I t = t
  | .prim _, _, _ => by simp only [interpret_term_prim]
  | .none _, _, _ => by simp only [interpret_term_none]
  | .some t, hw, h => by
    cases hw with | some_wf hw' =>
    have : t.isLiteral = true := by simp only [Term.isLiteral] at h; exact h
    simp only [interpret_term_some, interpret_lit_id t hw' this]
  | .set s ty, hw, h => by
    cases hw with | set_wf hw' _ _ hswf =>
    simp only [Term.isLiteral, Set.all₁_eq_all, Set.all_eq_true] at h
    rw [interpret_term_set]
    have hmc : s.map (Term.interpret I) = s.map id := by
      apply Set.map_congr
      intro t ht; simp only [id_eq]; exact interpret_lit_id t (hw' t ht) (h t ht)
    rw [hmc, Set.map_id s hswf]
  | .record ats, hw, h => by
    cases hw with | record_wf hw' hawf =>
    simp only [Term.isLiteral, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at h
    rw [interpret_term_record]
    apply congrArg Term.record
    apply Map.mapOnValues_restricted_id
    intro w hw2
    rcases Map.in_values_exists_key hw2 with ⟨a, ha⟩
    exact interpret_lit_id w (hw' a w ha) (h a w ha)
  | .var _, _, h => by simp only [Term.isLiteral, Bool.false_eq_true] at h
  | .app _ _ _, _, h => by simp only [Term.isLiteral, Bool.false_eq_true] at h
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := Set.sizeOf_lt_of_elts s; have := List.sizeOf_lt_of_mem ‹_ ∈ s.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)

/--
**WellTyped transport.** `Op.WellTyped` depends only on argument types, which
`substAnyAllIt v` preserves (`substAnyAllIt_typeOf`), so it transports across the
substitution. The `set.all` constructor also carries `NoSetAll` premises, which
transport via `substAnyAllIt_noSetAll` (needing `v.NoSetAll`). -/
theorem op_wellTyped_substAnyAllIt {εs : SymEntities} {v : Term} {op : Op} {ts : List Term} {ty : TermType}
  (hvn : v.NoSetAll = true)
  (hvty : ∀ ety : TermType, Term.anyAllItTyped ety v = true)
  (hta : ∀ t : Term, t ∈ ts → Term.anyAllItTyped v.typeOf t = true) :
  Op.WellTyped εs op ts ty →
  Op.WellTyped εs op (ts.map (Term.substAnyAllIt v)) ty := by
  intro hwt
  have hT : ∀ t : Term, t ∈ ts → (Term.substAnyAllIt v t).typeOf = t.typeOf :=
    fun t ht => substAnyAllIt_typeOf t (hta t ht)
  have hN : ∀ t : Term, Term.NoSetAll t = true → Term.NoSetAll (Term.substAnyAllIt v t) = true :=
    substAnyAllIt_noSetAll hvn
  have hA : ∀ (ety : TermType) t, Term.anyAllItTyped ety t = true →
      Term.anyAllItTyped ety (Term.substAnyAllIt v t) = true :=
    fun ety => substAnyAllIt_anyAllItTyped (hvty ety)
  cases hwt <;>
    (try simp only [List.map_cons, List.map_nil]) <;>
    first
      | exact Op.WellTyped.not_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.and_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.or_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.eq_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | (rename_i t₁ t₂ t₃ hb he
         rw [← hT t₂ (by simp)]
         exact Op.WellTyped.ite_wt (by rw [hT _ (by simp)]; exact hb) (by rw [hT _ (by simp), hT _ (by simp)]; exact he))
      | exact Op.WellTyped.uuf_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by assumption)
      | exact Op.WellTyped.bvneg_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvnego_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvadd_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvsub_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvmul_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvsdiv_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvudiv_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvsrem_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvsmod_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvurem_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvshl_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvlshr_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvsaddo_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvssubo_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvsmulo_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvslt_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvsle_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvult_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.bvule_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.zero_extend_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.set.member_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.set.subset_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.set.inter_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.set.all_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by apply hN; assumption) (by apply hN; assumption) (by apply hA; assumption) (by apply hA; assumption)
      | exact Op.WellTyped.option.get_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | exact Op.WellTyped.record.get_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption) (by assumption)
      | exact Op.WellTyped.string.like_wt (by (try rw [hT _ (by simp)]) <;> (try rw [hT _ (by simp)]) <;> assumption)
      | (rename_i h; exact Op.WellTyped.ext_wt (extOp_wellTyped_substAnyAllIt hta h))

/-- `ExtOp.WellTyped` transports across a typeOf-preserving arg map. -/
theorem extOp_wellTyped_congr_typeOf {f : Term → Term}
  {xop : ExtOp} {ts : List Term} {ty : TermType}
  (hf : ∀ t ∈ ts, (f t).typeOf = t.typeOf) :
  ExtOp.WellTyped xop ts ty → ExtOp.WellTyped xop (ts.map (fun t => f t)) ty := by
  intro hwt
  cases hwt <;>
    (try simp only [List.map_cons, List.map_nil]) <;>
    first
      | exact ExtOp.WellTyped.decimal.val_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.ipaddr.isV4_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.ipaddr.addrV4_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.ipaddr.prefixV4_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.ipaddr.addrV6_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.ipaddr.prefixV6_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.datetime.val_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.datetime.ofBitVec_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.duration.val_wt (by rw [hf _ (by simp)]; assumption)
      | exact ExtOp.WellTyped.duration.ofBitVec_wt (by rw [hf _ (by simp)]; assumption)

/-- `Op.WellTyped` (non-`set.all`) transports across a typeOf-preserving arg map `f`.
`set.all` is excluded (its extra `NoSetAll`/`anyAllItTyped` premises are not generic). -/
theorem op_wellTyped_congr_typeOf {εs : SymEntities} {f : Term → Term}
  {op : Op} {ts : List Term} {ty : TermType}
  (hf : ∀ t ∈ ts, (f t).typeOf = t.typeOf) (hop : op ≠ Op.set.all) :
  Op.WellTyped εs op ts ty → Op.WellTyped εs op (ts.map (fun t => f t)) ty := by
  intro hwt
  cases hwt <;>
    (try simp only [List.map_cons, List.map_nil]) <;>
    first
      | exact absurd rfl hop
      | exact Op.WellTyped.not_wt (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.and_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.or_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.eq_wt (by rw [hf _ (by simp), hf _ (by simp)]; assumption)
      | (rename_i t₁ t₂ t₃ hb he
         rw [← hf t₂ (by simp)]
         exact Op.WellTyped.ite_wt (by rw [hf _ (by simp)]; exact hb) (by rw [hf _ (by simp), hf _ (by simp)]; exact he))
      | exact Op.WellTyped.uuf_wt (by rw [hf _ (by simp)]; assumption) (by assumption)
      | exact Op.WellTyped.bvneg_wt (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvnego_wt (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvadd_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvsub_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvmul_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvsdiv_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvudiv_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvsrem_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvsmod_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvurem_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvshl_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvlshr_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvsaddo_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvssubo_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvsmulo_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvslt_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvsle_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvult_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.bvule_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.zero_extend_wt (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.set.member_wt (by rw [hf _ (by simp), hf _ (by simp)]; assumption)
      | exact Op.WellTyped.set.subset_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.set.inter_wt (by rw [hf _ (by simp)]; assumption) (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.option.get_wt (by rw [hf _ (by simp)]; assumption)
      | exact Op.WellTyped.record.get_wt (by rw [hf _ (by simp)]; assumption) (by assumption)
      | exact Op.WellTyped.string.like_wt (by rw [hf _ (by simp)]; assumption)
      | (rename_i h; exact Op.WellTyped.ext_wt (extOp_wellTyped_congr_typeOf hf h))


/--
**Lemma B (WellFormed).** `substAnyAllIt v` preserves well-formedness when `v` is
well-formed and shares its type with every bound-variable occurrence. -/
theorem substAnyAllIt_wf {εs : SymEntities} {v : Term}
  (hvwf : v.WellFormed εs)
  (hvn : v.NoSetAll = true)
  (hvty : ∀ ety : TermType, Term.anyAllItTyped ety v = true) :
  ∀ t : Term, Term.WellFormed εs t → Term.anyAllItTyped v.typeOf t = true →
    (Term.substAnyAllIt v t).WellFormed εs
  | .prim p, h, _ => by simp only [Term.substAnyAllIt]; exact h
  | .var w, h, _ => by
    simp only [Term.substAnyAllIt]
    by_cases hw : w.id = "!anyall!it"
    · simp only [hw, reduceIte]; exact hvwf
    · simp only [hw, reduceIte]; exact h
  | .none ty, h, _ => by simp only [Term.substAnyAllIt]; exact h
  | .some t, h, hat => by
    simp only [Term.substAnyAllIt]
    cases h with | some_wf h₁ =>
    have hat' : Term.anyAllItTyped v.typeOf t = true := by simp only [Term.anyAllItTyped] at hat; exact hat
    exact Term.WellFormed.some_wf (substAnyAllIt_wf hvwf hvn hvty t h₁ hat')
  | .set s ty, h, hat => by
    simp only [Term.substAnyAllIt]
    cases h with | set_wf h₁ h₂ h₃ h₄ =>
    have hmem : ∀ t ∈ s.elts, Term.anyAllItTyped v.typeOf t = true := by
      simp only [Term.anyAllItTyped, Set.all₁_eq_all, Set.all_eq_true] at hat; exact hat
    apply Term.WellFormed.set_wf
    · intro t ht
      simp only [Set.map₁_eq_map, Set.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩
      exact substAnyAllIt_wf hvwf hvn hvty t' (h₁ t' ht') (hmem t' ht')
    · intro t ht
      simp only [Set.map₁_eq_map, Set.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩
      rw [substAnyAllIt_typeOf t' (hmem t' ht')]; exact h₂ t' ht'
    · exact h₃
    · rw [Set.map₁_eq_map]; exact Set.map_wf _ _
  | .record ats, h, hat => by
    simp only [Term.substAnyAllIt]
    cases h with | record_wf h₁ h₂ =>
    have hmem : ∀ p ∈ ats.toList, Term.anyAllItTyped v.typeOf p.2 = true := by
      simp only [Term.anyAllItTyped, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at hat
      intro p hp; exact hat p.1 p.2 hp
    apply Term.WellFormed.record_wf
    · intro a t ht
      rw [Map.mapOnValues₂_eq_mapOnValues] at ht
      rcases Map.in_mapOnValues_in_toList' ht with ⟨t', rfl, ht'⟩
      exact substAnyAllIt_wf hvwf hvn hvty t' (h₁ a t' ht') (hmem (a, t') ht')
    · rw [Map.mapOnValues₂_eq_mapOnValues]; exact Map.mapOnValues_wf.mp h₂
  | .app op ts ty, h, hat => by
    simp only [Term.substAnyAllIt]
    cases h with | app_wf h₁ h₂ =>
    have hmem : ∀ t ∈ ts, Term.anyAllItTyped v.typeOf t = true := by
      have h' : (ts.attach.all (fun x => Term.anyAllItTyped v.typeOf x.val)) = true := by
        simp only [Term.anyAllItTyped] at hat; exact hat
      rw [List.all_eq_true] at h'
      intro t ht; exact h' ⟨t, ht⟩ (List.mem_attach ts ⟨t, ht⟩)
    apply Term.WellFormed.app_wf
    · intro t ht
      simp only [List.map₁_eq_map, List.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩
      exact substAnyAllIt_wf hvwf hvn hvty t' (h₁ t' ht') (hmem t' ht')
    · rw [List.map₁_eq_map]
      exact op_wellTyped_substAnyAllIt hvn hvty hmem h₂
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := Set.sizeOf_lt_of_elts s; have := List.sizeOf_lt_of_mem ‹_ ∈ s.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1
         omega)

/-- WF of a right fold of `Factory.and` over bool-WF terms. -/
theorem foldr_and_wf {εs : SymEntities} {α} {g : α → Term} :
  ∀ (vs : List α), (∀ x ∈ vs, (g x).WellFormed εs ∧ (g x).typeOf = .bool) →
    (vs.foldr (fun x acc => Factory.and (g x) acc) (true : Term)).WellFormed εs ∧
    (vs.foldr (fun x acc => Factory.and (g x) acc) (true : Term)).typeOf = .bool
  | [], _ => by
    refine ⟨Term.WellFormed.prim_wf TermPrim.WellFormed.bool_wf, ?_⟩
    simp only [List.foldr_nil, Term.typeOf, TermPrim.typeOf]
  | x :: xs, hx => by
    have hhd := hx x (by simp)
    have htl := foldr_and_wf xs (fun y hy => hx y (by simp [hy]))
    simp only [List.foldr_cons]
    exact wf_and hhd.left htl.left hhd.right htl.right

/-- WF of a right fold of `Factory.or` over bool-WF terms. -/
theorem foldr_or_wf {εs : SymEntities} {α} {g : α → Term} :
  ∀ (vs : List α), (∀ x ∈ vs, (g x).WellFormed εs ∧ (g x).typeOf = .bool) →
    (vs.foldr (fun x acc => Factory.or (g x) acc) (false : Term)).WellFormed εs ∧
    (vs.foldr (fun x acc => Factory.or (g x) acc) (false : Term)).typeOf = .bool
  | [], _ => by
    refine ⟨Term.WellFormed.prim_wf TermPrim.WellFormed.bool_wf, ?_⟩
    simp only [List.foldr_nil, Term.typeOf, TermPrim.typeOf]
  | x :: xs, hx => by
    have hhd := hx x (by simp)
    have htl := foldr_or_wf xs (fun y hy => hx y (by simp [hy]))
    simp only [List.foldr_cons]
    exact wf_or hhd.left htl.left hhd.right htl.right

/-- A right fold of `Factory.and` over WF-literal bool terms is a literal. -/
theorem foldr_and_isLit {εs : SymEntities} {α} {g : α → Term} :
  ∀ (vs : List α), (∀ x ∈ vs, (g x).WellFormedLiteral εs ∧ (g x).typeOf = .bool) →
    (vs.foldr (fun x acc => Factory.and (g x) acc) (true : Term)).isLiteral = true
  | [], _ => by simp only [List.foldr_nil, Term.isLiteral]
  | x :: xs, hx => by
    have hhd := hx x (by simp)
    have htlL := foldr_and_isLit xs (fun y hy => hx y (by simp [hy]))
    have htlW := foldr_and_wf (g := g) xs (fun y hy => ⟨(hx y (by simp [hy])).left.left, (hx y (by simp [hy])).right⟩)
    simp only [List.foldr_cons]
    exact pe_and_wfl hhd.left hhd.right ⟨htlW.left, htlL⟩ htlW.right

/-- A right fold of `Factory.or` over WF-literal bool terms is a literal. -/
theorem foldr_or_isLit {εs : SymEntities} {α} {g : α → Term} :
  ∀ (vs : List α), (∀ x ∈ vs, (g x).WellFormedLiteral εs ∧ (g x).typeOf = .bool) →
    (vs.foldr (fun x acc => Factory.or (g x) acc) (false : Term)).isLiteral = true
  | [], _ => by simp only [List.foldr_nil, Term.isLiteral]
  | x :: xs, hx => by
    have hhd := hx x (by simp)
    have htlL := foldr_or_isLit xs (fun y hy => hx y (by simp [hy]))
    have htlW := foldr_or_wf (g := g) xs (fun y hy => ⟨(hx y (by simp [hy])).left.left, (hx y (by simp [hy])).right⟩)
    simp only [List.foldr_cons]
    exact pe_or_wfl hhd.left hhd.right ⟨htlW.left, htlL⟩ htlW.right

/-- A `set.all` node built from WF, `.bool`-typed, `NoSetAll`, `anyAllItTyped ety`
bodies over a WF receiver of type `.set ety` is WF with type `.option .bool`. -/
theorem mkApp_set_all_wf {εs : SymEntities} {S P E : Term} {ety : TermType}
  (hSwf : S.WellFormed εs) (hSty : S.typeOf = .set ety)
  (hPwf : P.WellFormed εs) (hPty : P.typeOf = .bool)
  (hEwf : E.WellFormed εs) (hEty : E.typeOf = .bool)
  (hPn : P.NoSetAll = true) (hEn : E.NoSetAll = true)
  (hPa : P.anyAllItTyped ety = true) (hEa : E.anyAllItTyped ety = true) :
  (Term.app Op.set.all [S, P, E] (.option .bool)).WellFormed εs ∧
  (Term.app Op.set.all [S, P, E] (.option .bool)).typeOf = (.option .bool) := by
  refine ⟨Term.WellFormed.app_wf ?_ ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h <;> subst h
    · exact hSwf
    · exact hPwf
    · exact hEwf
  · exact Op.WellTyped.set.all_wt hSty hPty hEty hPn hEn hPa hEa
  · simp only [Term.typeOf]

/-- `op.interpret` (non-`set.all`) of well-formed, well-typed arguments is well-formed. -/
theorem op_interpret_wf {εs : SymEntities} {I : Interpretation} {op : Op} {ts : List Term} {ty : TermType}
  (h₀ : I.WellFormed εs) (hwt : Op.WellTyped εs op ts ty) (hargs : ∀ t ∈ ts, t.WellFormed εs) :
  (Op.interpret I op ts ty).WellFormed εs ∧ (Op.interpret I op ts ty).typeOf = ty := by
  simp only [Op.interpret]
  cases hwt with
  | not_wt h1 => exact wf_not (hargs _ (by simp)) h1
  | and_wt h1 h2 => exact wf_and (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | or_wt h1 h2 => exact wf_or (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | eq_wt h1 => exact wf_eq (hargs _ (by simp)) (hargs _ (by simp)) h1
  | ite_wt h1 h2 => exact wf_ite (hargs _ (by simp)) (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | @uuf_wt f t h1 h2 =>
    have h₅ := wf_interpretation_implies_wf_udf h₀ h2
    have hwf := hargs t (by simp)
    have happ := wf_app (f := .udf (I.funs f)) hwf
      (by simp only [UnaryFunction.argType]; rw [h₅.right.left]; exact h1)
      (by simp only [UnaryFunction.WellFormed, h₅.left])
    refine ⟨happ.left, ?_⟩
    rw [happ.right]
    simp only [UnaryFunction.outType, h₅.right.right]
  | bvneg_wt h1 => exact wf_bvneg (hargs _ (by simp)) h1
  | bvnego_wt h1 => exact wf_bvnego (hargs _ (by simp)) h1
  | bvadd_wt h1 h2 => exact wf_bvadd (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvsub_wt h1 h2 => exact wf_bvsub (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvmul_wt h1 h2 => exact wf_bvmul (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvsdiv_wt h1 h2 => exact wf_bvsdiv (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvudiv_wt h1 h2 => exact wf_bvudiv (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvsrem_wt h1 h2 => exact wf_bvsrem (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvsmod_wt h1 h2 => exact wf_bvsmod (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvurem_wt h1 h2 => exact wf_bvurem (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvshl_wt h1 h2 => exact wf_bvshl (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvlshr_wt h1 h2 => exact wf_bvlshr (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvsaddo_wt h1 h2 => exact wf_bvsaddo (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvssubo_wt h1 h2 => exact wf_bvssubo (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvsmulo_wt h1 h2 => exact wf_bvsmulo (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvslt_wt h1 h2 => exact wf_bvslt (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvsle_wt h1 h2 => exact wf_bvsle (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvult_wt h1 h2 => exact wf_bvult (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | bvule_wt h1 h2 => exact wf_bvule (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | zero_extend_wt h1 => exact wf_zero_extend (hargs _ (by simp)) h1
  | set.member_wt h1 => exact wf_set_member (hargs _ (by simp)) (hargs _ (by simp)) h1
  | set.subset_wt h1 h2 => exact wf_set_subset (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | set.inter_wt h1 h2 => exact wf_set_inter (hargs _ (by simp)) (hargs _ (by simp)) h1 h2
  | set.all_wt h1 h2 h3 h4 h5 h6 h7 =>
    exact mkApp_set_all_wf (hargs _ (by simp)) h1 (hargs _ (by simp)) h2 (hargs _ (by simp)) h3 h4 h5 h6 h7
  | option.get_wt h1 => exact wf_option_get' h₀ (hargs _ (by simp)) h1
  | record.get_wt h1 h2 => exact wf_record_get (hargs _ (by simp)) h1 h2
  | string.like_wt h1 => exact wf_string_like (hargs _ (by simp)) h1
  | @ext_wt xop ets ety h1 =>
    cases h1 with
    | decimal.val_wt he => exact wf_ext_decimal_val (hargs _ (by simp)) he
    | ipaddr.isV4_wt he => exact wf_ext_ipaddr_isV4 (hargs _ (by simp)) he
    | ipaddr.addrV4_wt he => exact wf_ext_ipaddr_addrV4' h₀ (hargs _ (by simp)) he
    | ipaddr.prefixV4_wt he => exact wf_ext_ipaddr_prefixV4' h₀ (hargs _ (by simp)) he
    | ipaddr.addrV6_wt he => exact wf_ext_ipaddr_addrV6' h₀ (hargs _ (by simp)) he
    | ipaddr.prefixV6_wt he => exact wf_ext_ipaddr_prefixV6' h₀ (hargs _ (by simp)) he
    | datetime.val_wt he => exact wf_ext_datetime_val (hargs _ (by simp)) he
    | datetime.ofBitVec_wt he => exact wf_ext_datetime_ofBitVec (hargs _ (by simp)) he
    | duration.val_wt he => exact wf_ext_duration_val (hargs _ (by simp)) he
    | duration.ofBitVec_wt he => exact wf_ext_duration_ofBitVec (hargs _ (by simp)) he


/-- `op.interpret` (non-`set.all`) of well-formed-literal arguments is a literal. -/
theorem op_interpret_lit {εs : SymEntities} {I : Interpretation} {op : Op} {ts : List Term} {ty : TermType}
  (h₀ : I.WellFormed εs) (hop : op ≠ Op.set.all) (hwt : Op.WellTyped εs op ts ty)
  (hargs : ∀ t ∈ ts, t.WellFormedLiteral εs) :
  (Op.interpret I op ts ty).isLiteral = true := by
  simp only [Op.interpret]
  cases hwt with
  | not_wt h1 => exact pe_not_wfl (hargs _ (by simp)) h1
  | and_wt h1 h2 => exact pe_and_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | or_wt h1 h2 => exact pe_or_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | eq_wt h1 => exact (pe_eq_lit (hargs _ (by simp)).right (hargs _ (by simp)).right).left
  | ite_wt h1 h2 => exact pe_ite_wfl (hargs _ (by simp)) (hargs _ (by simp)) (hargs _ (by simp)) h1
  | @uuf_wt f t h1 h2 =>
    exact pe_app_wfl (hargs t (by simp)) (wf_interpretation_implies_wf_udf h₀ h2).left
  | bvneg_wt h1 => exact pe_bvneg_wfl (hargs _ (by simp)) h1
  | bvnego_wt h1 => exact pe_bvnego_wfl (hargs _ (by simp)) h1
  | bvadd_wt h1 h2 => exact pe_bvadd_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvsub_wt h1 h2 => exact pe_bvsub_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvmul_wt h1 h2 => exact pe_bvmul_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvsdiv_wt h1 h2 => exact pe_bvsdiv_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvudiv_wt h1 h2 => exact pe_bvudiv_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvsrem_wt h1 h2 => exact pe_bvsrem_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvsmod_wt h1 h2 => exact pe_bvsmod_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvurem_wt h1 h2 => exact pe_bvurem_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvshl_wt h1 h2 => exact pe_bvshl_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvlshr_wt h1 h2 => exact pe_bvlshr_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvsaddo_wt h1 h2 => exact pe_bvsaddo_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvssubo_wt h1 h2 => exact pe_bvssubo_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvsmulo_wt h1 h2 => exact pe_bvsmulo_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvslt_wt h1 h2 => exact pe_bvslt_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvsle_wt h1 h2 => exact pe_bvsle_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvult_wt h1 h2 => exact pe_bvult_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | bvule_wt h1 h2 => exact pe_bvule_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | zero_extend_wt h1 => exact pe_zero_extend_wfl (hargs _ (by simp)) h1
  | set.member_wt h1 => exact pe_set_member_wfl (hargs _ (by simp)) (hargs _ (by simp)) h1
  | set.subset_wt h1 h2 => exact pe_set_subset_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | set.inter_wt h1 h2 => exact pe_set_inter_wfl (hargs _ (by simp)) h1 (hargs _ (by simp)) h2
  | option.get_wt h1 => exact pe_option_get'_wfl h₀ (hargs _ (by simp)) h1
  | record.get_wt h1 h2 => exact pe_record_get_wfl (hargs _ (by simp)) h1 h2
  | string.like_wt h1 => exact pe_string_like_wfl (hargs _ (by simp)) h1
  | ext_wt h1 =>
    cases h1 with
    | decimal.val_wt he => exact pe_ext_decimal_val_wfl (hargs _ (by simp)) he
    | ipaddr.isV4_wt he => exact pe_ext_ipaddr_isV4_wfl (hargs _ (by simp)) he
    | ipaddr.addrV4_wt he => exact pe_ext_ipaddr_addrV4'_wfl h₀ (hargs _ (by simp)) he
    | ipaddr.prefixV4_wt he => exact pe_ext_ipaddr_prefixV4'_wfl h₀ (hargs _ (by simp)) he
    | ipaddr.addrV6_wt he => exact pe_ext_ipaddr_addrV6'_wfl h₀ (hargs _ (by simp)) he
    | ipaddr.prefixV6_wt he => exact pe_ext_ipaddr_prefixV6'_wfl h₀ (hargs _ (by simp)) he
    | datetime.val_wt he => exact pe_ext_datetime_val_wfl (hargs _ (by simp)) he
    | datetime.ofBitVec_wt he => exact pe_ext_datetime_ofBitVec_wfl (hargs _ (by simp)) he
    | duration.val_wt he => exact pe_ext_duration_val_wfl (hargs _ (by simp)) he
    | duration.ofBitVec_wt he => exact pe_ext_duration_ofBitVec_wfl (hargs _ (by simp)) he
  | set.all_wt _ _ _ _ _ _ _ => exact absurd rfl hop

/--
**σ-generalized interpret WF.** Interpreting a well-formed, non-nested term `t`
whose reserved-var occurrences are all at type `v.typeOf`, with the bound var
mapped to a well-formed `v`, preserves well-formedness and type. The `.app` arm
reuses `op_interpret_wf` (its args are WF with preserved types by the IH, and the
op is well-typed on them by `op_wellTyped_congr_typeOf`); the nested `set.all`
case is impossible under `t.NoSetAll`. -/
theorem interpretWith_wf {εs : SymEntities} {I : Interpretation} {v : Term}
  (h₀ : I.WellFormed εs) (hvwf : v.WellFormed εs) :
  ∀ t : Term, t.WellFormed εs → t.NoSetAll = true → t.anyAllItTyped v.typeOf = true →
    (Term.interpretWith (some v) I t).WellFormed εs ∧
    (Term.interpretWith (some v) I t).typeOf = t.typeOf
  | .prim p, h, _, _ => by
    refine ⟨?_, ?_⟩ <;> simp only [Term.interpretWith]
    exact h
  | .var w, _, _, hat => by
    simp only [Term.interpretWith]
    by_cases hw : w.id = "!anyall!it"
    · simp only [hw, reduceIte]
      refine ⟨hvwf, ?_⟩
      simp only [Term.anyAllItTyped, hw, reduceIte, decide_eq_true_eq] at hat
      simp only [Term.typeOf]; exact hat.symm
    · simp only [hw, reduceIte]
      have := (h₀.left w (by cases ‹Term.WellFormed εs (Term.var w)› with | var_wf hvw => exact hvw))
      exact ⟨this.left.left, by simp only [Term.typeOf, this.right]⟩
  | .none ty, _, _, _ => by
    simp only [Term.interpretWith]
    exact ⟨Term.WellFormed.none_wf (by cases ‹Term.WellFormed εs (Term.none ty)› with | none_wf h => exact h),
      by simp only [Term.typeOf, Factory.noneOf]⟩
  | .some t, h, hn, hat => by
    cases h with | some_wf h₁ =>
    have hn' : t.NoSetAll = true := by simp only [Term.NoSetAll] at hn; exact hn
    have hat' : t.anyAllItTyped v.typeOf = true := by simp only [Term.anyAllItTyped] at hat; exact hat
    have ih := interpretWith_wf h₀ hvwf t h₁ hn' hat'
    refine ⟨?_, ?_⟩ <;> simp only [Term.interpretWith, Factory.someOf, Term.typeOf]
    · exact Term.WellFormed.some_wf ih.left
    · rw [ih.right]
  | .set s ty, h, hn, hat => by
    cases h with | set_wf h₁ h₂ h₃ h₄ =>
    have hnm : ∀ t ∈ s.elts, t.NoSetAll = true := noSetAll_set hn
    have ham : ∀ t ∈ s.elts, t.anyAllItTyped v.typeOf = true := by
      simp only [Term.anyAllItTyped, Set.all₁_eq_all, Set.all_eq_true] at hat; exact hat
    have ihelt : ∀ t ∈ s.elts, (Term.interpretWith (some v) I t).WellFormed εs ∧
        (Term.interpretWith (some v) I t).typeOf = t.typeOf :=
      fun t ht => interpretWith_wf h₀ hvwf t (h₁ t ht) (hnm t ht) (ham t ht)
    simp only [Term.interpretWith, Term.typeOf]
    refine ⟨Term.WellFormed.set_wf ?_ ?_ h₃ (by rw [Set.map₁_eq_map]; exact Set.map_wf _ _), ?_⟩
    · intro t ht
      simp only [Set.map₁_eq_map, Set.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩
      exact (ihelt t' ht').left
    · intro t ht
      simp only [Set.map₁_eq_map, Set.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩
      rw [(ihelt t' ht').right]; exact h₂ t' ht'
    · simp only [Set.map₁_eq_map]
  | .record ats, h, hn, hat => by
    cases h with | record_wf h₁ h₂ =>
    have hnm : ∀ p ∈ ats.toList, p.2.NoSetAll = true := noSetAll_record hn
    have ham : ∀ p ∈ ats.toList, p.2.anyAllItTyped v.typeOf = true := by
      simp only [Term.anyAllItTyped, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at hat
      intro p hp; exact hat p.1 p.2 hp
    simp only [Term.interpretWith, Term.typeOf]
    refine ⟨Term.WellFormed.record_wf ?_ ?_, ?_⟩
    · intro a t ht
      rw [Map.mapOnValues₂_eq_mapOnValues] at ht
      rcases Map.in_mapOnValues_in_toList' ht with ⟨t', rfl, ht'⟩
      exact (interpretWith_wf h₀ hvwf t' (h₁ a t' ht') (hnm (a, t') ht') (ham (a, t') ht')).left
    · rw [Map.mapOnValues₂_eq_mapOnValues]; exact Map.mapOnValues_wf.mp h₂
    · simp only [Map.mapOnValues₂_eq_mapOnValues]
      apply congrArg (TermType.record ·)
      rw [Map.mapOnValues_mapOnValues]
      apply Map.mapOnValues_congr
      intro w hw
      rcases Map.in_values_exists_key hw with ⟨a, ha⟩
      simp only [Function.comp_apply]
      exact (interpretWith_wf h₀ hvwf w (h₁ a w ha) (hnm (a, w) ha) (ham (a, w) ha)).right
  | .app op ts ty, h, hn, hat => by
    have ⟨hop, hargsNoSetAll⟩ := noSetAll_app hn
    have hargsTyped : ∀ t ∈ ts, t.anyAllItTyped v.typeOf = true := by
      have h' : (ts.attach.all (fun x => Term.anyAllItTyped v.typeOf x.val)) = true := by
        cases op <;> first | exact absurd rfl hop | (simp only [Term.anyAllItTyped] at hat ⊢; exact hat)
      rw [List.all_eq_true] at h'
      intro t ht; exact h' ⟨t, ht⟩ (List.mem_attach ts ⟨t, ht⟩)
    cases h with | app_wf hwfargs hwt =>
    have ihargs : ∀ t ∈ ts, (Term.interpretWith (some v) I t).WellFormed εs ∧
        (Term.interpretWith (some v) I t).typeOf = t.typeOf :=
      fun t ht => interpretWith_wf h₀ hvwf t (hwfargs t ht) (hargsNoSetAll t ht) (hargsTyped t ht)
    rw [interpretWith_app_ne_setAll hop]
    have hwt' : Op.WellTyped εs op (ts.map₁ (fun x => Term.interpretWith (some v) I x.val)) ty := by
      rw [List.map₁_eq_map]
      exact op_wellTyped_congr_typeOf (fun t ht => (ihargs t ht).right) hop hwt
    have hwfargs' : ∀ t ∈ ts.map₁ (fun x => Term.interpretWith (some v) I x.val), t.WellFormed εs := by
      intro t ht
      simp only [List.map₁_eq_map, List.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩
      exact (ihargs t' ht').left
    have := op_interpret_wf h₀ hwt' hwfargs'
    simp only [Term.typeOf]
    exact this
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := Set.sizeOf_lt_of_elts s; have := List.sizeOf_lt_of_mem ‹_ ∈ s.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)


/-- **σ-generalized interpret literalness.** For a well-formed-literal substituend
`v` and a well-formed, non-nested term whose reserved-var occurrences are at type
`v.typeOf`, interpreting with the bound var mapped to `v` yields a literal. -/
theorem interpretWith_lit {εs : SymEntities} {I : Interpretation} {v : Term}
  (h₀ : I.WellFormed εs) (hvl : v.WellFormedLiteral εs) :
  ∀ t : Term, t.WellFormed εs → t.NoSetAll = true → t.anyAllItTyped v.typeOf = true →
    (Term.interpretWith (Option.some v) I t).isLiteral = true
  | .prim p, _, _, _ => by simp only [Term.interpretWith, Term.isLiteral]
  | .var w, _, _, hat => by
    simp only [Term.interpretWith]
    by_cases hw : w.id = "!anyall!it"
    · simp only [hw, reduceIte]; exact hvl.right
    · simp only [hw, reduceIte]
      exact (h₀.left w (by cases ‹Term.WellFormed εs (Term.var w)› with | var_wf hvw => exact hvw)).left.right
  | .none ty, _, _, _ => by simp only [Term.interpretWith, Factory.noneOf, Term.isLiteral]
  | .some t, h, hn, hat => by
    cases h with | some_wf h₁ =>
    have hn' : t.NoSetAll = true := by simp only [Term.NoSetAll] at hn; exact hn
    have hat' : t.anyAllItTyped v.typeOf = true := by simp only [Term.anyAllItTyped] at hat; exact hat
    simp only [Term.interpretWith, Factory.someOf, Term.isLiteral]
    exact interpretWith_lit h₀ hvl t h₁ hn' hat'
  | .set s ty, h, hn, hat => by
    cases h with | set_wf h₁ h₂ h₃ h₄ =>
    have hnm : ∀ t ∈ s.elts, t.NoSetAll = true := noSetAll_set hn
    have ham : ∀ t ∈ s.elts, t.anyAllItTyped v.typeOf = true := by
      simp only [Term.anyAllItTyped, Set.all₁_eq_all, Set.all_eq_true] at hat; exact hat
    simp only [Term.interpretWith, Term.isLiteral, Set.map₁_eq_map, Set.all₁_eq_all, Set.all_eq_true]
    intro t ht
    rw [Set.mem_map] at ht
    rcases ht with ⟨t', ht', rfl⟩
    exact interpretWith_lit h₀ hvl t' (h₁ t' ht') (hnm t' ht') (ham t' ht')
  | .record ats, h, hn, hat => by
    cases h with | record_wf h₁ h₂ =>
    have hnm : ∀ p ∈ ats.toList, p.2.NoSetAll = true := noSetAll_record hn
    have ham : ∀ p ∈ ats.toList, p.2.anyAllItTyped v.typeOf = true := by
      simp only [Term.anyAllItTyped, List.all_attach₂_snd, List.all_eq_true, Prod.forall] at hat
      intro p hp; exact hat p.1 p.2 hp
    simp only [Term.interpretWith, Term.isLiteral, Map.mapOnValues₂_eq_mapOnValues,
      List.all_attach₂_snd, List.all_eq_true, Prod.forall]
    intro a t ht
    rcases Map.in_mapOnValues_in_toList' ht with ⟨t', rfl, ht'⟩
    exact interpretWith_lit h₀ hvl t' (h₁ a t' ht') (hnm (a, t') ht') (ham (a, t') ht')
  | .app op ts ty, h, hn, hat => by
    have ⟨hop, hargsNoSetAll⟩ := noSetAll_app hn
    have hargsTyped : ∀ t ∈ ts, t.anyAllItTyped v.typeOf = true := by
      have h' : (ts.attach.all (fun x => Term.anyAllItTyped v.typeOf x.val)) = true := by
        cases op <;> first | exact absurd rfl hop | (simp only [Term.anyAllItTyped] at hat ⊢; exact hat)
      rw [List.all_eq_true] at h'
      intro t ht; exact h' ⟨t, ht⟩ (List.mem_attach ts ⟨t, ht⟩)
    cases h with | app_wf hwfargs hwt =>
    have ihW : ∀ t ∈ ts, (Term.interpretWith (Option.some v) I t).WellFormed εs ∧
        (Term.interpretWith (Option.some v) I t).typeOf = t.typeOf :=
      fun t ht => interpretWith_wf h₀ hvl.left t (hwfargs t ht) (hargsNoSetAll t ht) (hargsTyped t ht)
    have ihL : ∀ t ∈ ts, (Term.interpretWith (Option.some v) I t).isLiteral = true :=
      fun t ht => interpretWith_lit h₀ hvl t (hwfargs t ht) (hargsNoSetAll t ht) (hargsTyped t ht)
    rw [interpretWith_app_ne_setAll hop]
    have hwt' : Op.WellTyped εs op (ts.map₁ (fun x => Term.interpretWith (Option.some v) I x.val)) ty := by
      rw [List.map₁_eq_map]
      exact op_wellTyped_congr_typeOf (fun t ht => (ihW t ht).right) hop hwt
    have hargs' : ∀ t ∈ ts.map₁ (fun x => Term.interpretWith (Option.some v) I x.val), t.WellFormedLiteral εs := by
      intro t ht
      simp only [List.map₁_eq_map, List.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩
      exact ⟨(ihW t' ht').left, ihL t' ht'⟩
    exact op_interpret_lit h₀ hop hwt' hargs'
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := Set.sizeOf_lt_of_elts s; have := List.sizeOf_lt_of_mem ‹_ ∈ s.elts›; omega)
      | (have h1 := List.sizeOf_lt_of_mem ‹(_, _) ∈ Map.toList ats›
         have h2 := Map.sizeOf_lt_of_toList ats
         simp only [Prod.mk.sizeOf_spec] at h1; omega)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)


end Cedar.Thm
