module

/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.SymCC
import Cedar.Thm.SymCC.Compiler.SetAllWF
import all Cedar.Thm.SymCC.Term.Interpret.WF
import all Cedar.Thm.SymCC.Term.Interpret.SubstAnyAllIt
import Cedar.Thm.SymCC.Term.Interpret.Factory
import Cedar.Thm.Tactics

/-! Interpretation of the compiled `set.all` node over a literal-set receiver (D-67 → M3).
`Factory.set.all` folds the predicate/error bodies with `substAnyAllIt` per element; `interpret`
pushes through the fold and `interpretWith_some_eq_interpret_substAnyAllIt` (Lemma A) turns each
`interpret I (substAnyAllIt vi _)` into `interpretWith (some vi) I _`. -/

namespace Cedar.Thm

open Spec SymCC Factory Cedar.Data
theorem interpret_foldr_and_substAnyAllIt {εs : SymEntities} {I : Interpretation} {P : Term} {ety : TermType} {vs : List Term}
    (hwI : I.WellFormed εs)
    (hlit : ∀ vi ∈ vs, vi.isLiteral = true)
    (hvw : ∀ vi ∈ vs, vi.WellFormed εs) (hvty : ∀ vi ∈ vs, vi.typeOf = ety)
    (hPw : P.WellFormed εs) (hPty : P.typeOf = .bool) (hPn : P.NoSetAll = true) (hPa : P.anyAllItTyped ety = true) :
    Term.interpret I (vs.foldr (fun vi acc => and (Term.substAnyAllIt vi P) acc) (true : Term))
      = vs.foldr (fun vi acc => and (Term.interpretWith (Option.some vi) I P) acc) (true : Term) := by
  induction vs with
  | nil => simp only [List.foldr_nil, interpret_term_prim]
  | cons vhd vtl ih =>
    simp only [List.foldr_cons]
    have hhdlit := hlit vhd (by simp)
    have hhdw := hvw vhd (by simp)
    have hhdty := hvty vhd (by simp)
    have hava : ∀ e, vhd.anyAllItTyped e = true := fun e => isLiteral_anyAllItTyped _ hhdlit
    -- WF of the substituted head + typeOf bool
    have hsubw := substAnyAllIt_wf hhdw (isLiteral_noSetAll vhd hhdlit) hava P hPw (hhdty ▸ hPa)
    have hsubty : (Term.substAnyAllIt vhd P).typeOf = .bool := by rw [substAnyAllIt_typeOf P (hhdty ▸ hPa), hPty]
    -- WF + typeOf bool of the accumulator (foldr) : via foldr_and_wf
    have hacc := foldr_and_wf (εs := εs) (g := fun vi => Term.substAnyAllIt vi P) vtl (by
      intro vi hmem
      have hil := hlit vi (by simp [hmem])
      have hw := hvw vi (by simp [hmem])
      have ht := hvty vi (by simp [hmem])
      have hav : ∀ e, vi.anyAllItTyped e = true := fun e => isLiteral_anyAllItTyped _ hil
      exact ⟨substAnyAllIt_wf hw (isLiteral_noSetAll vi hil) hav P hPw (ht ▸ hPa), by rw [substAnyAllIt_typeOf P (ht ▸ hPa), hPty]⟩)
    rw [interpret_and hwI hsubw hacc.left hsubty hacc.right]
    have hvid := interpret_lit_id (I := I) vhd hhdw hhdlit
    have hA := interpretWith_some_eq_interpret_substAnyAllIt hvid P hPn
    rw [← hA]
    congr 1
    exact ih (fun vi h => hlit vi (by simp [h])) (fun vi h => hvw vi (by simp [h])) (fun vi h => hvty vi (by simp [h]))

theorem interpret_foldr_or_substAnyAllIt {εs : SymEntities} {I : Interpretation} {E : Term} {ety : TermType} {vs : List Term}
    (hwI : I.WellFormed εs)
    (hlit : ∀ vi ∈ vs, vi.isLiteral = true)
    (hvw : ∀ vi ∈ vs, vi.WellFormed εs) (hvty : ∀ vi ∈ vs, vi.typeOf = ety)
    (hEw : E.WellFormed εs) (hEty : E.typeOf = .bool) (hEn : E.NoSetAll = true) (hEa : E.anyAllItTyped ety = true) :
    Term.interpret I (vs.foldr (fun vi acc => or (Term.substAnyAllIt vi E) acc) (false : Term))
      = vs.foldr (fun vi acc => or (Term.interpretWith (Option.some vi) I E) acc) (false : Term) := by
  induction vs with
  | nil => simp only [List.foldr_nil, interpret_term_prim]
  | cons vhd vtl ih =>
    simp only [List.foldr_cons]
    have hhdlit := hlit vhd (by simp)
    have hhdw := hvw vhd (by simp)
    have hhdty := hvty vhd (by simp)
    have hava : ∀ e, vhd.anyAllItTyped e = true := fun e => isLiteral_anyAllItTyped _ hhdlit
    have hsubw := substAnyAllIt_wf hhdw (isLiteral_noSetAll vhd hhdlit) hava E hEw (hhdty ▸ hEa)
    have hsubty : (Term.substAnyAllIt vhd E).typeOf = .bool := by rw [substAnyAllIt_typeOf E (hhdty ▸ hEa), hEty]
    have hacc := foldr_or_wf (εs := εs) (g := fun vi => Term.substAnyAllIt vi E) vtl (by
      intro vi hmem
      have hil := hlit vi (by simp [hmem])
      have hw := hvw vi (by simp [hmem])
      have ht := hvty vi (by simp [hmem])
      have hav : ∀ e, vi.anyAllItTyped e = true := fun e => isLiteral_anyAllItTyped _ hil
      exact ⟨substAnyAllIt_wf hw (isLiteral_noSetAll vi hil) hav E hEw (ht ▸ hEa), by rw [substAnyAllIt_typeOf E (ht ▸ hEa), hEty]⟩)
    rw [interpret_or hwI hsubw hacc.left hsubty hacc.right]
    have hvid := interpret_lit_id (I := I) vhd hhdw hhdlit
    have hA := interpretWith_some_eq_interpret_substAnyAllIt hvid E hEn
    rw [← hA]
    congr 1
    exact ih (fun vi h => hlit vi (by simp [h])) (fun vi h => hvw vi (by simp [h])) (fun vi h => hvty vi (by simp [h]))

/-- Interpreting the compiled `set.all` node over a literal-set receiver folds element-by-element,
with each per-element predicate/error body given by `interpretWith (some vi) I`. -/
theorem interpret_set_all_lit {εs : SymEntities} {I : Interpretation} {P E : Term} {ety : TermType} {vs : List Term}
    (hwI : I.WellFormed εs)
    (hlit : ∀ vi ∈ vs, vi.isLiteral = true)
    (hvw : ∀ vi ∈ vs, vi.WellFormed εs) (hvty : ∀ vi ∈ vs, vi.typeOf = ety)
    (hPw : P.WellFormed εs) (hPty : P.typeOf = .bool) (hPn : P.NoSetAll = true) (hPa : P.anyAllItTyped ety = true)
    (hEw : E.WellFormed εs) (hEty : E.typeOf = .bool) (hEn : E.NoSetAll = true) (hEa : E.anyAllItTyped ety = true) :
    Term.interpret I (Factory.set.all (.set (Set.mk vs) ety) P E) =
      Factory.ite
        (vs.foldr (fun vi acc => or (Term.interpretWith (Option.some vi) I E) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (vs.foldr (fun vi acc => and (Term.interpretWith (Option.some vi) I P) acc) (true : Term))) := by
  have hmemiff : ∀ vi, vi ∈ vs → vi ∈ (Set.mk vs).elts := by intro vi h; simpa [Set.elts] using h
  unfold Factory.set.all
  have hallit : (List.all vs (·.isLiteral)) = true := by
    simp only [List.all_eq_true]; intro vi hmem; exact hlit vi hmem
  simp only [hallit, if_true]
  have hconj := foldr_and_wf (εs := εs) (g := fun vi => Term.substAnyAllIt vi P) vs (by
    intro vi hmem
    have hil := hlit vi hmem
    have hw := hvw vi hmem
    have ht := hvty vi hmem
    have hav : ∀ e, vi.anyAllItTyped e = true := fun e => isLiteral_anyAllItTyped _ hil
    exact ⟨substAnyAllIt_wf hw (isLiteral_noSetAll vi hil) hav P hPw (ht ▸ hPa), by rw [substAnyAllIt_typeOf P (ht ▸ hPa), hPty]⟩)
  have hanyErr := foldr_or_wf (εs := εs) (g := fun vi => Term.substAnyAllIt vi E) vs (by
    intro vi hmem
    have hil := hlit vi hmem
    have hw := hvw vi hmem
    have ht := hvty vi hmem
    have hav : ∀ e, vi.anyAllItTyped e = true := fun e => isLiteral_anyAllItTyped _ hil
    exact ⟨substAnyAllIt_wf hw (isLiteral_noSetAll vi hil) hav E hEw (ht ▸ hEa), by rw [substAnyAllIt_typeOf E (ht ▸ hEa), hEty]⟩)
  simp only [Factory.noneOf, Factory.someOf]
  rw [interpret_ite hwI hanyErr.left (Term.WellFormed.none_wf TermType.WellFormed.bool_wf) (Term.WellFormed.some_wf hconj.left) hanyErr.right (by simp only [Term.typeOf, hconj.right])]
  simp only [interpret_term_none, interpret_term_some]
  rw [interpret_foldr_and_substAnyAllIt hwI hlit hvw hvty hPw hPty hPn hPa]
  rw [interpret_foldr_or_substAnyAllIt hwI hlit hvw hvty hEw hEty hEn hEa]

end Cedar.Thm
