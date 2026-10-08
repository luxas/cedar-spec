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

end Cedar.Thm
