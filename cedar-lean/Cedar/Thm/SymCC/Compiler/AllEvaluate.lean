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

import Cedar.SymCC
import Cedar.Thm.SymCC.Compiler.CompilePredEvaluate
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Term.Same
import Cedar.Thm.Data.Set

/-!
Step D: `compile_evaluate_all`, the `.all` arm of `compile_evaluate`.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC Cedar.SymCC.Factory

/-- A term whose `value?` succeeds is a literal. -/
theorem value?_some_implies_isLiteral {t : Term} {v : Value} :
    t.value? = some v → t.isLiteral = true := by
  intro hv
  induction t using Term.value?.induct generalizing v
  case motive1 _ tᵢ =>
    exact (∀ vᵢ, tᵢ.value? = .some vᵢ → tᵢ.isLiteral = true)
  case case1 | case2 =>
    simp only [Term.value?, false_implies, implies_true, reduceCtorEq]
  case case3 ih =>
    intro v hv
    exact ih hv
  case case4 =>
    simp only [Term.isLiteral]
  case case5 ih =>
    simp only [Term.isLiteral, Cedar.Data.Set.all₁_eq_all, Cedar.Data.Set.all_eq_true]
    intro ti hti
    rename_i s _
    rw [Term.value?] at hv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    replace ⟨vs', hv, _⟩ := hv
    simp only [List.mapM₁_eq_mapM Term.value?, ← List.mapM'_eq_mapM] at hv
    rw [← Cedar.Data.Set.mem_elts_iff_mem_set] at hti
    replace ⟨vi, hvi⟩ := List.mapM'_some_implies_all_some hv ti hti
    exact ih ti hti hvi.2
  case case6 ih =>
    rename_i ats
    rw [Term.isLiteral, List.all_attach₂_snd, List.all_eq_true]
    intro x hx
    obtain ⟨xa, xt⟩ := x
    simp only at *
    have hsz : sizeOf xt < 1 + sizeOf ats.toList := by
      have := List.sizeOf_snd_lt_sizeOf_list hx
      simp only at this; omega
    -- extract attrValue? xa xt = some _ for this attr from hv
    rw [Term.value?] at hv
    simp only [List.mapM₂_eq_mapM λ x : Attr × Term => Term.value?.attrValue? x.fst x.snd,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    replace ⟨avs, hm, _⟩ := hv
    replace ⟨pv, _, hav⟩ := List.mapM_some_implies_all_some hm (xa, xt) hx
    -- hav : attrValue? xa xt = some pv
    cases hxs : xt with
    | «some» t' =>
      rw [hxs] at hav
      simp only [Term.value?.attrValue?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hav
      obtain ⟨vv, hvv, _⟩ := hav
      rw [Term.isLiteral]
      exact ih xa t' (by rw [hxs] at hsz; simp only [Term.some.sizeOf_spec] at hsz; omega) vv hvv
    | «none» tty =>
      exact isLiteral_none
    | _ =>
      rw [hxs] at hav
      simp only [Term.value?.attrValue?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hav
      obtain ⟨vv, hvv, _⟩ := hav
      exact ih xa _ (by rw [hxs] at hsz; exact hsz) vv hvv
  case case7 =>
    simp only [Term.value?, reduceCtorEq] at hv


