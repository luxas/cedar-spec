/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

-- NOTE (D-68, crux): this file is deliberately NOT a `module`. It must import the
-- non-module `CompilePredInterpret`; a `module` file may not import a non-module
-- one. A non-module file CAN import the module files below and see their `public`
-- lemmas (`interpret_set_all_lit`, `interpret_extInterp_eq_of_noAnyAllItVar`,
-- `interpretWith_some_eq_interpret_ext`, …).

import Cedar.SymCC
import Cedar.Thm.SymCC.Compiler.WF

import Cedar.Thm.SymCC.Compiler.CompilePredInterpret
import Cedar.Thm.SymCC.Compiler.SetAllInterpret
import Cedar.Thm.SymCC.Term.Interpret.WF
import Cedar.Thm.SymCC.Term.Interpret.Lit
import Cedar.Thm.SymCC.Term.Interpret.SubstAnyAllIt
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Env.Interpret
import Cedar.Thm.Tactics

namespace Cedar.Thm

open Spec SymCC Factory Cedar.Data

/-- General-receiver variant of `interpret_set_all_lit`: `S` is any well-formed
term of set type (not already a literal-set node). It interprets to a well-formed
literal set `.set (Set.mk vs') elemTy`; the compiled `set.all S P E` node then
folds element-by-element over `vs'` with each body given by `interpretWith (some vi') I`. -/
theorem interpret_set_all_wf {εs : SymEntities} {I : Interpretation} {S P E : Term} {elemTy : TermType}
    (hwI : I.WellFormed εs)
    (hSw : S.WellFormed εs) (hSty : S.typeOf = .set elemTy)
    (hPw : P.WellFormed εs) (hPty : P.typeOf = .bool) (hPn : P.NoSetAll = true) (hPa : P.anyAllItTyped elemTy = true)
    (hEw : E.WellFormed εs) (hEty : E.typeOf = .bool) (hEn : E.NoSetAll = true) (hEa : E.anyAllItTyped elemTy = true) :
    ∃ (vs' : List Term),
      (Term.interpret I S = .set (Set.mk vs') elemTy) ∧
      (∀ vi ∈ vs', vi.isLiteral = true) ∧
      (∀ vi ∈ vs', vi.WellFormed εs) ∧
      (∀ vi ∈ vs', vi.typeOf = elemTy) ∧
      Term.interpret I (Factory.set.all S P E) =
        Factory.ite
          (vs'.foldr (fun vi acc => or (Term.interpretWith (Option.some vi) I E) acc) (false : Term))
          (Factory.noneOf .bool)
          (Factory.someOf (vs'.foldr (fun vi acc => and (Term.interpretWith (Option.some vi) I P) acc) (true : Term))) := by
  have hwfl := interpret_term_wfl hwI hSw
  have hSinty : (Term.interpret I S).typeOf = .set elemTy := by rw [hwfl.right, hSty]
  have ⟨s', hSeq⟩ := wfl_of_type_set_is_set hwfl.left hSinty
  cases s' with
  | mk vs' =>
  have hSinw : (Term.interpret I S).WellFormed εs := hwfl.left.left
  have hSinl : (Term.interpret I S).isLiteral = true := hwfl.left.right
  rw [hSeq] at hSinw hSinl
  have hlit : ∀ vi ∈ vs', vi.isLiteral = true := by
    intro vi hmem
    simp only [Term.isLiteral, Set.all₁_eq_all, Set.all_eq_true] at hSinl
    exact hSinl vi (by rw [← Set.mem_elts_iff_mem_set]; simpa [Set.elts] using hmem)
  have hvw : ∀ vi ∈ vs', vi.WellFormed εs := by
    intro vi hmem
    exact wf_term_set_implies_wf_elt hSinw (by rw [← Set.mem_elts_iff_mem_set]; simpa [Set.elts] using hmem)
  have hvty : ∀ vi ∈ vs', vi.typeOf = elemTy := by
    intro vi hmem
    exact wf_term_set_implies_typeOf_elt hSinw (by rw [← Set.mem_elts_iff_mem_set]; simpa [Set.elts] using hmem)
  refine ⟨vs', hSeq, hlit, hvw, hvty, ?_⟩
  unfold Factory.set.all
  show Term.interpretWith Option.none I (.app Op.set.all [S, P, E] (.option .bool)) = _
  have hII : Term.interpretWith Option.none I S = Term.set (Set.mk vs') elemTy := hSeq
  have hallit : (List.all vs' (·.isLiteral)) = true := by
    simp only [List.all_eq_true]; intro vi hmem; exact hlit vi hmem
  rw [Term.interpretWith]
  simp only [hII, hallit, if_true]

/-- D-68 step 4: interpreting a symbolic environment under `extInterp I v ety`
gives the same environment as interpreting under `I`. The entities read only
`I.funs`/`I.partials` (which `extInterp` leaves untouched), and a well-formed
request's four terms are `NoAnyAllItVar`/`NoSetAll` (D-62), so they never read the
reserved `I.vars` entry that `extInterp` redefines. -/
theorem symEnv_interpret_extInterp {εnv : SymEnv} {I : Interpretation} {v : Term} {ety : TermType}
    (hwε : εnv.WellFormed) :
    εnv.interpret (extInterp I v ety) = εnv.interpret I := by
  have hreq := hwε.left
  simp only [SymRequest.WellFormed] at hreq
  obtain ⟨_, _, hpn, hps, _, _, han, has, _, _, hrn, hrs, _, _, hcn, hcs⟩ := hreq
  simp only [SymEnv.interpret, SymRequest.interpret, SymEntities.interpret]
  refine SymEnv.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · -- request: each term interprets identically
    refine SymRequest.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact interpret_extInterp_eq_of_noAnyAllItVar _ hpn hps
    · exact interpret_extInterp_eq_of_noAnyAllItVar _ han has
    · exact interpret_extInterp_eq_of_noAnyAllItVar _ hrn hrs
    · exact interpret_extInterp_eq_of_noAnyAllItVar _ hcn hcs
  · -- entities: `extInterp` only redefines `I.vars`, which entity interpretation never reads
    rfl

-- NEXT: `compile_interpret_all` (closes Compiler.lean:168) is to be added here and
-- wired into Compiler.lean's `.all` arm. The receiver interprets to a WF *literal*
-- set, so the interpreted-side compile always takes the per-element literal-fold
-- path; its reconciliation with the three εnv-side cases consumes, per element:
--   `interpret_ifSome` + `interpret_option_get_aux` (ifSome/option.get commute),
--   `interpret_set_all_lit` (interpret of the symbolic set.all node, D-67),
--   `interpretWith_some_eq_interpret_ext` (D-67) + `compilePred_interpret` at
--   I' := extInterp I vi elemTy + `symEnv_interpret_extInterp` (above) +
--   `extInterp_wf`. See .kiro/.../phase5b/D-68-compiler-fold.md.

/-- The reserved element variable, interpreted under `extInterp I vi elemTy`, is `vi`. -/
theorem interpret_someOf_itVar_extInterp {I : Interpretation} {vi : Term} {elemTy : TermType} :
    (Factory.someOf (.var (Factory.anyAllItVar elemTy))).interpret (extInterp I vi elemTy) = Factory.someOf vi := by
  simp only [Factory.someOf, Term.interpret, Term.interpretWith, extInterp, Factory.anyAllItVar, and_self, if_true]

/-- D-68 per-element bridge: compiling the symbolic predicate `pt` and then
substituting a well-formed literal element `vi` for the bound variable (via
interpretation under `extInterp I vi elemTy`) equals compiling the predicate
directly with `it := someOf vi` under the interpreted environment. This is the
link between the symbolic receiver's `interpret_set_all_lit` fold bodies and the
interpreted-side per-element `compilePred` calls. -/
theorem compilePred_interpret_someOf_lit {p : PredExpr} {εnv : SymEnv} {I : Interpretation} {pt vi : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hvw : vi.WellFormed εnv.entities) (hvlit : vi.isLiteral = true) (hvty : vi.typeOf = elemTy)
    (hpt : compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv = .ok pt) :
    compilePred p (Factory.someOf vi) (εnv.interpret I) = .ok (pt.interpret (extInterp I vi elemTy)) := by
  let I' := extInterp I vi elemTy
  have hitw : (Factory.someOf (.var (Factory.anyAllItVar elemTy))).WellFormed εnv.entities := by
    apply Term.WellFormed.some_wf
    apply Term.WellFormed.var_wf
    -- elemTy is WF: vi is a WF term of type elemTy
    have := typeOf_wf_term_is_wf hvw
    rw [hvty] at this; exact this
  have hitty : (Factory.someOf (.var (Factory.anyAllItVar elemTy))).typeOf = .option elemTy := by
    simp only [Factory.someOf, typeOf_term_some, typeOf_term_var, Factory.anyAllItVar]
  have hI' : I'.WellFormed εnv.entities := extInterp_wf hI ⟨hvw, hvlit⟩ hvty
  -- apply compilePred_interpret at I'
  have hci := compilePred_interpret hI' hwε hitw hitty hpt
  -- rewrite it.interpret I' = someOf vi and εnv.interpret I' = εnv.interpret I
  rw [interpret_someOf_itVar_extInterp (I := I) (vi := vi) (elemTy := elemTy),
      symEnv_interpret_extInterp (I := I) (v := vi) (ety := elemTy) hwε] at hci
  exact hci

/-- `ifSome` only inspects its guard's `isNone` and its value's option element type:
when the guard is a well-formed literal of option type and the two values share a
type, they agree under `ifSome` as long as they agree whenever the guard is `.some`
(the `.none` guard collapses both to `noneOf`). -/
theorem ifSome_guard_congr {εs : SymEntities} {g t₂ t₃ : Term} {ty ety : TermType}
    (hg : g.WellFormedLiteral εs) (hgty : g.typeOf = .option ty)
    (ht₂ : t₂.typeOf = .option ety) (ht₃ : t₃.typeOf = .option ety)
    (hsome : ∀ w, g = .some w → t₂ = t₃) :
    Factory.ifSome g t₂ = Factory.ifSome g t₃ := by
  rcases wfl_of_type_option_is_option hg hgty with hn | ⟨w, hw, _⟩
  · subst hn
    simp only [Factory.ifSome, ht₂, ht₃, pe_isNone_none, pe_ite_true]
  · subst hw
    rw [hsome w rfl]

/-- If some element folds its `or`-head to literal `true`, the whole `foldr or` is literal `true`. -/
theorem foldr_or_true_of_mem {α} {g : α → Term} {ws : List α}
    (h : ∃ w ∈ ws, g w = Term.prim (.bool true)) :
    ws.foldr (fun w acc => Factory.or (g w) acc) (false : Term) = Term.prim (.bool true) := by
  induction ws with
  | nil => obtain ⟨_, hmem, _⟩ := h; simp at hmem
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    obtain ⟨w, hmem, hw⟩ := h
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [hw]; exact pe_or_true_left
    · rw [ih ⟨w, htl, hw⟩]; exact pe_or_true_right

/-- `foldr and` congruence when the per-element terms agree. -/
theorem foldr_and_congr {α} {g₁ g₂ : α → Term} {ws : List α}
    (h : ∀ w ∈ ws, g₁ w = g₂ w) :
    ws.foldr (fun w acc => Factory.and (g₁ w) acc) (true : Term)
      = ws.foldr (fun w acc => Factory.and (g₂ w) acc) (true : Term) := by
  induction ws with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldr_cons, h hd (by simp), ih (fun w hw => h w (by simp [hw]))]

/-- `foldr or` congruence when the per-element terms agree. -/
theorem foldr_or_congr {α} {g₁ g₂ : α → Term} {ws : List α}
    (h : ∀ w ∈ ws, g₁ w = g₂ w) :
    ws.foldr (fun w acc => Factory.or (g₁ w) acc) (false : Term)
      = ws.foldr (fun w acc => Factory.or (g₂ w) acc) (false : Term) := by
  induction ws with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldr_cons, h hd (by simp), ih (fun w hw => h w (by simp [hw]))]

/-- Interpretation commutes with a right fold of `Factory.and` over Bool-WF bodies. -/
theorem interpret_foldr_and {εs : SymEntities} {I : Interpretation} {g : Term → Term} {ws : List Term}
    (hwI : I.WellFormed εs)
    (hg : ∀ w ∈ ws, (g w).WellFormed εs ∧ (g w).typeOf = .bool) :
    Term.interpret I (ws.foldr (fun w acc => Factory.and (g w) acc) (true : Term))
      = ws.foldr (fun w acc => Factory.and (Term.interpret I (g w)) acc) (true : Term) := by
  induction ws with
  | nil => simp only [List.foldr_nil, interpret_term_prim]
  | cons hd tl ih =>
    have hhd := hg hd (by simp)
    have hacc := foldr_and_wf (εs := εs) (g := g) tl (fun w hw => hg w (by simp [hw]))
    simp only [List.foldr_cons]
    rw [interpret_and hwI hhd.left hacc.left hhd.right hacc.right,
      ih (fun w hw => hg w (by simp [hw]))]

/-- Interpretation commutes with a right fold of `Factory.or` over Bool-WF bodies. -/
theorem interpret_foldr_or {εs : SymEntities} {I : Interpretation} {g : Term → Term} {ws : List Term}
    (hwI : I.WellFormed εs)
    (hg : ∀ w ∈ ws, (g w).WellFormed εs ∧ (g w).typeOf = .bool) :
    Term.interpret I (ws.foldr (fun w acc => Factory.or (g w) acc) (false : Term))
      = ws.foldr (fun w acc => Factory.or (Term.interpret I (g w)) acc) (false : Term) := by
  induction ws with
  | nil => simp only [List.foldr_nil, interpret_term_prim]
  | cons hd tl ih =>
    have hhd := hg hd (by simp)
    have hacc := foldr_or_wf (εs := εs) (g := g) tl (fun w hw => hg w (by simp [hw]))
    simp only [List.foldr_cons]
    rw [interpret_or hwI hhd.left hacc.left hhd.right hacc.right,
      ih (fun w hw => hg w (by simp [hw]))]

/-- The compiler's per-element `.all` mapM over a list `vs'` evaluates to `.ok (vs'.map fval)`
when each element compiles to `fval vi'` with a Bool-typed `option.get`. -/
theorem mapM_someOf_eq_map {p : PredExpr} {εnv : SymEnv} {fval : Term → Term} {vs' : List Term}
    (hbridge : ∀ vi' ∈ vs', compilePred p (Factory.someOf vi') εnv = .ok (fval vi'))
    (hget : ∀ vi' ∈ vs', (Factory.option.get (fval vi')).typeOf = .bool) :
    (vs'.mapM (fun vi => do
        let pti ← compilePred p (Factory.someOf vi) εnv
        if (Factory.option.get pti).typeOf = TermType.bool then Except.ok pti else Except.error SymCC.Error.typeError))
      = .ok (vs'.map fval) := by
  induction vs' with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.mapM_cons, hbridge hd (by simp)]
    simp only [hget hd (by simp), if_true, Except.bind_ok,
      ih (fun vi' h => hbridge vi' (by simp [h])) (fun vi' h => hget vi' (by simp [h])),
      List.map_cons]
    rfl

/-- Route A (D-68), fold reconciliation over the element list `vs'`. `fval vi'` is the
per-element interpreted predicate body (a WF literal of type `.option .bool`). The GOAL side
folds with value `option.get (fval vi')` and error `not (isSome (fval vi'))`; the `set.all`
side folds with value `B vi'` and error `BE vi'`. Given the error bodies match and `B` agrees
with `option.get (fval vi')` whenever `fval vi'` is `.some`, the two `ite`s are equal (any
`.none` element makes both error disjunctions `true`, collapsing both to `noneOf .bool`). -/
theorem fold_ite_val_congr {εs : SymEntities} {vs' : List Term} {fval B BE : Term → Term}
    (hw : ∀ vi' ∈ vs', (fval vi').WellFormedLiteral εs ∧ (fval vi').typeOf = .option .bool)
    (hE : ∀ vi' ∈ vs', BE vi' = Factory.not (Factory.isSome (fval vi')))
    (hB : ∀ vi' ∈ vs', ∀ w', fval vi' = Term.some w' → B vi' = w') :
    Factory.ite (vs'.foldr (fun vi' acc => Factory.or (Factory.not (Factory.isSome (fval vi'))) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (vs'.foldr (fun vi' acc => Factory.and (Factory.option.get (fval vi')) acc) (true : Term)))
      = Factory.ite (vs'.foldr (fun vi' acc => Factory.or (BE vi') acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (vs'.foldr (fun vi' acc => Factory.and (B vi') acc) (true : Term))) := by
  -- the error disjunctions agree (hE elementwise)
  have hErr : vs'.foldr (fun vi' acc => Factory.or (BE vi') acc) (false : Term)
      = vs'.foldr (fun vi' acc => Factory.or (Factory.not (Factory.isSome (fval vi'))) acc) (false : Term) :=
    foldr_or_congr hE
  rw [hErr]
  by_cases hcong : ∀ vi' ∈ vs', Factory.option.get (fval vi') = B vi'
  · rw [foldr_and_congr hcong]
  · simp only [Classical.not_forall, Classical.not_imp] at hcong
    obtain ⟨vi', hmem, hne⟩ := hcong
    rcases wfl_of_type_option_is_option (hw vi' hmem).left (hw vi' hmem).right with hn | ⟨w', hsome, _⟩
    · have herr : vs'.foldr (fun vi' acc => Factory.or (Factory.not (Factory.isSome (fval vi'))) acc) (false : Term)
          = Term.prim (.bool true) := by
        apply foldr_or_true_of_mem
        exact ⟨vi', hmem, by rw [hn, pe_isSome_none, pe_not_false]⟩
      rw [herr, pe_ite_true, pe_ite_true]
    · exact absurd (by rw [hsome, pe_option_get_some, hB vi' hmem w' hsome]) hne

end Cedar.Thm
