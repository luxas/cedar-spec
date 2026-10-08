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

end Cedar.Thm
