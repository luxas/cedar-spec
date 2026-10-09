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

/-- The compiler's `anyErr` fold over a list of WF `.option .bool` literal predicate terms
is itself a `.bool` literal. -/
theorem foldr_anyErr_lit {εs : SymEntities} {pairs : List (Term × Spec.Result Bool)}
    (hwf : ∀ pr ∈ pairs, (pr.1).WellFormedLiteral εs ∧ (pr.1).typeOf = .option .bool) :
    ∃ ge, pairs.foldr (fun pr acc => Factory.or (Factory.not (Factory.isSome pr.1)) acc) (false : Term)
        = Term.prim (.bool ge) := by
  induction pairs with
  | nil => exact ⟨false, rfl⟩
  | cons pr rest ih =>
    have hwfhd := hwf pr (by simp only [List.mem_cons, true_or])
    obtain ⟨ge, hge⟩ := ih (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
    simp only [List.foldr_cons, hge]
    rcases wfl_of_type_option_is_option ⟨hwfhd.1.1, hwfhd.1.2⟩ hwfhd.2 with hnone | ⟨t', hsome, _⟩
    · exact ⟨true, by simp only [hnone, pe_isSome_none, pe_not_false, pe_or_true_left]⟩
    · exact ⟨ge, by simp only [hsome, pe_isSome_some, pe_not_true, pe_or_false_left]⟩

/-- Fold reconciliation: the compiler's per-element `conj`/`anyErr` fold reconciles
with `evalAll`'s `mapM (·.as Bool)` collapse, element-wise. -/
theorem all_fold_reconcile {εs : SymEntities} {pairs : List (Term × Spec.Result Bool)}
    (hwf : ∀ pr ∈ pairs, (pr.1).WellFormedLiteral εs ∧ (pr.1).typeOf = .option .bool)
    (hsame : ∀ pr ∈ pairs, SameResults (pr.2.map (Value.prim ∘ Prim.bool)) pr.1) :
    SameResults
      (match pairs.mapM Prod.snd with
        | .error _ => .error .quantifierError
        | .ok bs => .ok (Value.prim (.bool (bs.all id))))
      (Factory.ite
        (pairs.foldr (fun pr acc => Factory.or (Factory.not (Factory.isSome pr.1)) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (pairs.foldr (fun pr acc => Factory.and (Factory.option.get pr.1) acc) (true : Term)))) := by
  induction pairs with
  | nil =>
    simp only [List.mapM_nil, List.foldr_nil, pe_ite_false, Factory.someOf]
    exact same_ok_bool
  | cons pr rest ih =>
    have hwfhd := hwf pr (by simp only [List.mem_cons, true_or])
    have hshd := hsame pr (by simp only [List.mem_cons, true_or])
    have ihrest := ih (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
                      (fun p hp => hsame p (List.mem_cons_of_mem _ hp))
    obtain ⟨ger, hger⟩ := foldr_anyErr_lit (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
    simp only [List.foldr_cons]
    cases hrb : pr.2 with
    | error e =>
      rw [hrb] at hshd
      simp only [Except.map, SameResults] at hshd
      obtain ⟨ty, hnoneq⟩ : ∃ ty, pr.1 = Term.none ty := by
        cases hpt : pr.1 <;> simp only [hpt, SameResults] at hshd
        exact ⟨_, rfl⟩
      rw [List.mapM_cons, hrb]
      simp only [Except.bind_err, hnoneq, pe_isSome_none, pe_not_false,
        pe_or_true_left, pe_ite_true, Factory.noneOf]
      exact same_error_implied_by (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    | ok b =>
      rw [hrb] at hshd
      have hbt : (Except.ok (Value.prim (.bool b)) : Spec.Result Value) ∼ pr.1 := by
        simp only [Except.map, Function.comp] at hshd; exact hshd
      have ht : pr.1 = Term.some (.prim (.bool b)) := same_ok_bool_implies hbt
      rw [List.mapM_cons, hrb]
      simp only [Except.bind_ok, ht, pe_isSome_some, pe_not_true, pe_or_false_left,
        pe_option_get_some, hger]
      -- guard is literal `ger`; case on it
      cases ger with
      | «true» =>
        -- anyErr_rest = true ⇒ ihrest's ite = noneOf ⇒ its LHS is an error ⇒ mapM rest errors
        simp only [hger, pe_ite_true] at ihrest
        rw [pe_ite_true]
        cases hmr : List.mapM Prod.snd rest with
        | error e =>
          simp only [hmr, Except.bind_err, Factory.noneOf]
          exact same_error_implied_by (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
        | ok bs =>
          rw [hmr] at ihrest
          simp only [hmr, Factory.noneOf, SameResults, reduceCtorEq] at ihrest
      | «false» =>
        simp only [hger, pe_ite_false] at ihrest ⊢
        -- anyErr_rest = false ⇒ ihrest : (mapM rest result) ∼ someOf conj_rest
        cases hmr : List.mapM Prod.snd rest with
        | error e =>
          rw [hmr] at ihrest
          simp only [hmr, Factory.someOf, SameResults] at ihrest
        | ok bs =>
          rw [hmr] at ihrest
          simp only [hmr, Factory.someOf, List.all_cons] at ihrest ⊢
          replace ihrest := same_ok_some_implies ihrest
          cases b with
          | «true» =>
            simp only [pe_and_true_left, Bool.true_and]
            exact same_ok_some_iff.mpr ihrest
          | «false» =>
            simp only [pe_and_false_left, Bool.false_and]
            exact same_ok_bool


