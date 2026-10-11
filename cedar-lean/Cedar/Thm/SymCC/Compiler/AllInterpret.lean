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

/-- D-68 steps 3/5: `compile_interpret` for the `.all` arm (closes Compiler.lean:169). -/
theorem compile_interpret_all {x₁ : Expr} {p : PredExpr} {εnv : SymEnv} {I : Interpretation} {t : Term}
    (hI : I.WellFormed εnv.entities)
    (hwε : εnv.WellFormedFor (.all x₁ p))
    (hok : compile (.all x₁ p) εnv = .ok t)
    (ih₁ : CompileInterpret x₁) :
    compile (.all x₁ p) (εnv.interpret I) = .ok (t.interpret I) := by
  have hwφ₁ : εnv.WellFormedFor x₁ := by
    refine ⟨hwε.left, ?_⟩
    have hv := hwε.right
    cases hv with | all_valid hvx _ => exact hvx
  rw [compile.eq_def] at hok
  simp only [] at hok
  split at hok
  · simp only [reduceCtorEq] at hok
  rename_i hnoit
  rw [Decidable.not_not] at hnoit
  simp_do_let (compile x₁ εnv) at hok
  rename_i t₁ hr₁
  have ⟨ih1w, ty1, hty1⟩ := compile_wf hwφ₁ hr₁
  have hrecv : compile x₁ (εnv.interpret I) = .ok (t₁.interpret I) := ih₁ hI hwφ₁ hr₁
  have hgt := wf_option_get ih1w hty1
  split at hok
  · -- D-69: `.none ty` receiver — short-circuit on both sides to noneOf .bool
    rename_i ty
    split at hok
    · rename_i sty
      simp only [Except.ok.injEq] at hok
      subst hok
      rw [compile.eq_def]; simp only []; rw [if_neg (by simp only [hnoit, not_true, not_false_eq_true])]; rw [hrecv]; simp only [Except.bind_ok]
      rw [interpret_term_none]
      simp only [Factory.noneOf, interpret_term_none]
    · simp only [reduceCtorEq] at hok
  · -- non-`.none` receiver
    split at hok
    · rename_i elemTy helemq
      have htys : ty1 = .set elemTy := by rw [← hgt.right]; exact helemq
      rw [htys] at hgt
      have hel : TermType.WellFormed εnv.entities elemTy := by
        have hw := typeOf_wf_term_is_wf hgt.left
        rw [hgt.right] at hw
        cases hw with | set_wf h => exact h
      have hvarw : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).WellFormed εnv.entities :=
        Term.WellFormed.some_wf (Term.WellFormed.var_wf hel)
      have hvarty : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).typeOf = .option elemTy := by
        simp only [Factory.someOf, typeOf_term_some, typeOf_term_var, Factory.anyAllItVar]
      have hvarn : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).NoSetAll = true := by
        simp only [Factory.someOf, Term.NoSetAll]
      have hvara : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).anyAllItTyped elemTy = true := by
        simp [Factory.someOf, Term.anyAllItTyped, Factory.anyAllItVar]
      have hwfl := interpret_term_wfl hI ih1w
      rw [hty1] at hwfl
      -- SYMBOLIC case, shared by inner-symbolic and typeOf-symbolic εnv branches.
      have symbolic : ∀ {pt : Term},
          compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv = Except.ok pt →
          (option.get pt).typeOf = .bool →
          compile (.all x₁ p) (εnv.interpret I) =
            Except.ok ((Factory.ifSome t₁ (Factory.set.all (option.get t₁) (option.get pt) (Factory.not (Factory.isSome pt)))).interpret I) := by
        intro pt hpt hpbool
        have ⟨hptw, pty, hptty⟩ := compilePred_wf hwε.left hvarw hvarty hpt
        have hptn := compilePred_noSetAll' hwε.left hvarn hpt
        have hpta := compilePred_anyAllItTyped' (elemTy := elemTy) hwε.left hvara hpt
        have hgp := wf_option_get hptw hptty
        rw [hpbool] at hgp
        have hgpn : (option.get pt).NoSetAll = true := noSetAll_option_get hptn
        have hgpa : (option.get pt).anyAllItTyped elemTy = true := anyAllItTyped_option_get hpta
        have hns := wf_isSome hptw
        have hnotw := wf_not hns.left hns.right
        have hnotn : (Factory.not (isSome pt)).NoSetAll = true := noSetAll_not (noSetAll_isSome hptn)
        have hnota : (Factory.not (isSome pt)).anyAllItTyped elemTy = true := anyAllItTyped_not (anyAllItTyped_isSome hpta)
        have hifw : (Factory.set.all (option.get t₁) (option.get pt) (Factory.not (isSome pt))).WellFormed εnv.entities :=
          (wf_set_all' hgt.left hgt.right hgp.left hpbool hnotw.left hnotw.right hgpn hnotn hgpa hnota).left
        rw [interpret_ifSome hI ih1w hifw]
        obtain ⟨vs', hSeq, hlit', hvw', hvty', hfold⟩ :=
          interpret_set_all_wf hI hgt.left hgt.right hgp.left hpbool hgpn hgpa hnotw.left hnotw.right hnotn hnota
        rw [hfold]
        rw [compile.eq_def]; simp only []; rw [if_neg (by simp only [hnoit, not_true, not_false_eq_true])]; rw [hrecv]; simp only [Except.bind_ok]
        -- per-element value function and the two set.all fold bodies
        let fval : Term → Term := fun vi' => pt.interpret (extInterp I vi' elemTy)
        -- bridge: each element's εnv.interpret-I compile equals fval vi'
        have hbridge : ∀ vi' ∈ vs', compilePred p (Factory.someOf vi') (εnv.interpret I) = .ok (fval vi') := by
          intro vi' hmem
          exact compilePred_interpret_someOf_lit hI hwε.left (hvw' vi' hmem) (hlit' vi' hmem) (hvty' vi' hmem) hpt
        -- each fval vi' is a WF literal of type .option .bool
        have hptybool : pty = .bool := by
          have := (wf_option_get hptw hptty).right
          rw [hpbool] at this; exact this.symm
        have hfvalwfl : ∀ vi' ∈ vs', (fval vi').WellFormedLiteral εnv.entities ∧ (fval vi').typeOf = .option .bool := by
          intro vi' hmem
          have hI' := extInterp_wf hI ⟨hvw' vi' hmem, hlit' vi' hmem⟩ (hvty' vi' hmem)
          have hwfl' := interpret_term_wfl hI' hptw
          rw [hptty, hptybool] at hwfl'
          exact ⟨hwfl'.left, hwfl'.right⟩
        -- (option.get (fval vi')).typeOf = .bool
        have hfvalget : ∀ vi' ∈ vs', (option.get (fval vi')).typeOf = .bool := by
          intro vi' hmem
          exact (wf_option_get (hfvalwfl vi' hmem).left.left (hfvalwfl vi' hmem).right).right
        -- the mapM evaluates to .ok (vs'.map fval)
        have hmapM := mapM_someOf_eq_map (p := p) (εnv := εnv.interpret I) (fval := fval) (vs' := vs') hbridge hfvalget
        -- per-element set.all fold bodies and their relation to the GOAL bodies
        let B : Term → Term := fun vi => Term.interpretWith (Option.some vi) I (option.get pt)
        let BE : Term → Term := fun vi => Term.interpretWith (Option.some vi) I (Factory.not (isSome pt))
        have hE : ∀ vi ∈ vs', BE vi = Factory.not (Factory.isSome (fval vi)) := by
          intro vi hmem
          have hI' := extInterp_wf hI ⟨hvw' vi hmem, hlit' vi hmem⟩ (hvty' vi hmem)
          show Term.interpretWith (Option.some vi) I (Factory.not (isSome pt))
            = Factory.not (Factory.isSome (pt.interpret (extInterp I vi elemTy)))
          rw [interpretWith_some_eq_interpret_ext _ hnotn hnota,
            interpret_not hI' (wf_isSome hptw).left, interpret_isSome hI' hptw]
        have hB : ∀ vi ∈ vs', ∀ w', fval vi = Term.some w' → B vi = w' := by
          intro vi hmem w' hsome
          have hI' := extInterp_wf hI ⟨hvw' vi hmem, hlit' vi hmem⟩ (hvty' vi hmem)
          show Term.interpretWith (Option.some vi) I (option.get pt) = w'
          rw [interpretWith_some_eq_interpret_ext _ hgpn hgpa, interpret_option_get (extInterp I vi elemTy) hptw hptty]
          show option.get' (extInterp I vi elemTy) (pt.interpret (extInterp I vi elemTy)) = w'
          have hfe : fval vi = pt.interpret (extInterp I vi elemTy) := rfl
          rw [hfe] at hsome
          rw [hsome, pe_option_get'_some]
        -- the key fold equality (GOAL fold over vs'.map fval, re-indexed, = set.all fold over vs')
        have hfoldeq :
            Factory.ite (vs'.foldr (fun vi acc => Factory.or (Factory.not (Factory.isSome (fval vi))) acc) (false : Term))
                (Factory.noneOf .bool)
                (Factory.someOf (vs'.foldr (fun vi acc => Factory.and (Factory.option.get (fval vi)) acc) (true : Term)))
              = Factory.ite (vs'.foldr (fun vi acc => Factory.or (BE vi) acc) (false : Term))
                (Factory.noneOf .bool)
                (Factory.someOf (vs'.foldr (fun vi acc => Factory.and (B vi) acc) (true : Term))) :=
          fold_ite_val_congr (εs := εnv.entities) (fval := fval) (B := B) (BE := BE) hfvalwfl hE hB
        -- the two inner ite's are option-bool typed (via the set.all node's typeOf through hfold)
        have hsaty : (Factory.set.all (option.get t₁) (option.get pt) (Factory.not (isSome pt))).typeOf = .option .bool :=
          (wf_set_all' hgt.left hgt.right hgp.left hpbool hnotw.left hnotw.right hgpn hnotn hgpa hnota).right
        have hrhsty : (Factory.ite (vs'.foldr (fun vi acc => Factory.or (BE vi) acc) (false : Term)) (Factory.noneOf .bool)
              (Factory.someOf (vs'.foldr (fun vi acc => Factory.and (B vi) acc) (true : Term)))).typeOf = .option .bool := by
          rw [← hfold, (interpret_term_wf hI hifw).right, hsaty]
        have hlhsty : (Factory.ite (vs'.foldr (fun vi acc => Factory.or (Factory.not (Factory.isSome (fval vi))) acc) (false : Term))
              (Factory.noneOf .bool)
              (Factory.someOf (vs'.foldr (fun vi acc => Factory.and (Factory.option.get (fval vi)) acc) (true : Term)))).typeOf = .option .bool := by
          rw [hfoldeq]; exact hrhsty
        -- case on interpret I t₁
        rcases wfl_of_type_option_is_option hwfl.left hwfl.right with hnone | ⟨w, hsome, hwty⟩
        · -- interpret I t₁ = .none ty1 : interpreted-side compiler short-circuits (D-69) to noneOf .bool;
          -- RHS ifSome (.none ty1) <fold> = noneOf .bool
          have hfity : (Factory.ite
              (vs'.foldr (fun vi acc => Factory.or (Term.interpretWith (Option.some vi) I (Factory.not (isSome pt))) acc) (false : Term))
              (Factory.noneOf .bool)
              (Factory.someOf (vs'.foldr (fun vi acc => Factory.and (Term.interpretWith (Option.some vi) I (option.get pt)) acc) (true : Term)))).typeOf = .option .bool := by
            rw [← hfold, (interpret_term_wf hI hifw).right]
            exact (wf_set_all' hgt.left hgt.right hgp.left hpbool hnotw.left hnotw.right hgpn hnotn hgpa hnota).right
          rw [hnone, htys]
          show _ = Except.ok (Factory.ifSome (Term.none (.set elemTy)) _)
          rw [Factory.ifSome, hfity]
          simp only [pe_isNone_none, pe_ite_true, Factory.noneOf]
        · -- interpret I t₁ = .some w : option.get (.some w) = w = .set (Set.mk vs') elemTy
          rw [hsome]
          have hw_eq : w = Term.set (Set.mk vs') elemTy := by
            have hog := interpret_option_get I ih1w hty1
            rw [hsome, pe_option_get'_some] at hog
            -- hog : Term.interpret I (option.get t₁) = w ; hSeq : Term.interpret I (option.get t₁) = .set ...
            exact hog.symm.trans hSeq
          subst hw_eq
          rw [pe_option_get_some]
          have hvs'lit : (vs'.all fun x => x.isLiteral) = true := by
            simp only [List.all_eq_true]; intro vi hmem; exact hlit' vi hmem
          simp only [Term.typeOf, hvs'lit, if_true]
          rw [hmapM]
          simp only [Except.bind_ok]
          rw [List.foldr_map, List.foldr_map]
          apply congrArg Except.ok
          exact congrArg (Factory.ifSome _) hfoldeq
      split at hok
      · rename_i vs eltsTy hvseq
        split at hok
        · -- literal-fold εnv case
          rename_i hvslit
          simp only [List.all_eq_true] at hvslit
          simp_do_let (vs.mapM (fun vi => do
            let pti ← compilePred p (Factory.someOf vi) εnv
            if (option.get pti).typeOf = TermType.bool then Except.ok pti else Except.error SymCC.Error.typeError)) at hok
          rename_i pts hpts
          simp only [Except.ok.injEq] at hok; subst hok
          -- eltsTy = elemTy and element facts
          have hety : eltsTy = elemTy := by
            have := hgt.right; rw [hvseq] at this
            simp only [Term.typeOf, TermType.set.injEq] at this; exact this
          subst hety
          have hsetw := hgt.left; rw [hvseq] at hsetw
          have helts : ∀ vi ∈ vs, vi.WellFormed εnv.entities ∧ vi.typeOf = eltsTy := by
            cases hsetw with | set_wf h₁ h₂ _ _ =>
            intro vi hmem; exact ⟨h₁ vi hmem, by rw [h₂ vi hmem]⟩
          rw [List.mapM_ok_iff_forall₂] at hpts
          -- per-element predicate-value function (default never hit for vi ∈ vs)
          let fval : Term → Term := fun vi => (compilePred p (Factory.someOf vi) εnv).toOption.getD vi
          have hfe : ∀ vi, fval vi = (compilePred p (Factory.someOf vi) εnv).toOption.getD vi := fun _ => rfl
          -- each forall₂-related (vi, pti) satisfies pti = fval vi
          have hrel : ∀ {vi pti}, (do
              let pti' ← compilePred p (Factory.someOf vi) εnv
              if (option.get pti').typeOf = TermType.bool then Except.ok pti' else Except.error SymCC.Error.typeError) = Except.ok pti →
              pti = fval vi := by
            intro vi pti hpti
            cases hcp : compilePred p (Factory.someOf vi) εnv <;>
              simp only [hcp, Except.bind_err, Except.bind_ok, reduceCtorEq] at hpti
            rename_i cpt
            split at hpti <;> simp only [Except.ok.injEq, reduceCtorEq] at hpti
            rw [← hpti, hfe, hcp]; rfl
          -- per-element facts for fval (derived from the forall₂ before it is consumed)
          have hpe : ∀ vi ∈ vs, compilePred p (Factory.someOf vi) εnv = .ok (fval vi)
              ∧ (option.get (fval vi)).typeOf = .bool := by
            intro vi hmem
            obtain ⟨pti, _, hpti⟩ := List.forall₂_implies_all_left hpts vi hmem
            show compilePred p (Factory.someOf vi) εnv = .ok ((compilePred p (Factory.someOf vi) εnv).toOption.getD vi)
              ∧ (option.get ((compilePred p (Factory.someOf vi) εnv).toOption.getD vi)).typeOf = .bool
            cases hcp : compilePred p (Factory.someOf vi) εnv <;>
              simp only [hcp, Except.bind_err, Except.bind_ok, reduceCtorEq] at hpti ⊢
            rename_i cpt
            split at hpti <;> simp only [Except.ok.injEq, reduceCtorEq] at hpti
            rename_i hbool
            exact ⟨rfl, hbool⟩
          -- pts = vs.map fval
          have hptsmap : pts = vs.map fval := by
            clear hvseq hvslit helts hsetw hgt helemq hpe
            induction hpts with
            | nil => rfl
            | cons hr _htl ih =>
              simp only [List.map_cons]
              rw [hrel hr, ih]
          subst hptsmap
          -- εnv per-element predicate `fval vi` is WF of type .option .bool
          have hfvalw : ∀ vi ∈ vs, (fval vi).WellFormed εnv.entities ∧ (fval vi).typeOf = .option .bool := by
            intro vi hmem
            have ⟨hcpok, hbool⟩ := hpe vi hmem
            have ⟨hcpw, cty, hcpty⟩ := compilePred_wf hwε.left
              (Term.WellFormed.some_wf (helts vi hmem).left)
              (by simp only [Factory.someOf, typeOf_term_some]; rw [(helts vi hmem).right]) hcpok
            have hg := wf_option_get hcpw hcpty
            have hctybool : cty = .bool := hg.right.symm.trans hbool
            exact ⟨hcpw, by rw [hcpty, hctybool]⟩
          -- interpreted per-element value
          let fvalI : Term → Term := fun vi => (fval vi).interpret I
          -- fvalI vi is a WF literal of type .option .bool
          have hfvalIwfl : ∀ vi ∈ vs, (fvalI vi).WellFormedLiteral εnv.entities ∧ (fvalI vi).typeOf = .option .bool := by
            intro vi hmem
            have hwfl := interpret_term_wfl hI (hfvalw vi hmem).left
            rw [(hfvalw vi hmem).right] at hwfl
            exact ⟨hwfl.left, hwfl.right⟩
          -- the two set.all-style fold bodies (interpreted εnv value/error) and their relation to GOAL bodies
          have hE : ∀ vi ∈ vs, (fun vi => Term.interpret I (Factory.not (isSome (fval vi)))) vi = Factory.not (Factory.isSome (fvalI vi)) := by
            intro vi hmem
            show Term.interpret I (Factory.not (isSome (fval vi))) = Factory.not (Factory.isSome ((fval vi).interpret I))
            rw [interpret_not hI (wf_isSome (hfvalw vi hmem).left).left, interpret_isSome hI (hfvalw vi hmem).left]
          have hB : ∀ vi ∈ vs, ∀ w', fvalI vi = Term.some w' → (fun vi => Term.interpret I (option.get (fval vi))) vi = w' := by
            intro vi hmem w' hsome
            show Term.interpret I (option.get (fval vi)) = w'
            rw [interpret_option_get I (hfvalw vi hmem).left (hfvalw vi hmem).right]
            have hsome' : (fval vi).interpret I = Term.some w' := hsome
            rw [hsome', pe_option_get'_some]
          -- the fold equality (GOAL fold over vs = εnv-interpreted fold over vs)
          have hfoldeq :
              Factory.ite (vs.foldr (fun vi acc => Factory.or (Factory.not (Factory.isSome (fvalI vi))) acc) (false : Term))
                  (Factory.noneOf .bool)
                  (Factory.someOf (vs.foldr (fun vi acc => Factory.and (Factory.option.get (fvalI vi)) acc) (true : Term)))
                = Factory.ite (vs.foldr (fun vi acc => Factory.or (Term.interpret I (Factory.not (isSome (fval vi)))) acc) (false : Term))
                  (Factory.noneOf .bool)
                  (Factory.someOf (vs.foldr (fun vi acc => Factory.and (Term.interpret I (option.get (fval vi))) acc) (true : Term))) :=
            fold_ite_val_congr (εs := εnv.entities) (fval := fvalI)
              (B := fun vi => Term.interpret I (option.get (fval vi)))
              (BE := fun vi => Term.interpret I (Factory.not (isSome (fval vi)))) hfvalIwfl hE hB
          -- per-element WF of the εnv fold bodies (over vs.map fval, re-indexed to vs)
          have hgetw : ∀ vi ∈ vs, (option.get (fval vi)).WellFormed εnv.entities ∧ (option.get (fval vi)).typeOf = .bool := by
            intro vi hmem
            exact wf_option_get (hfvalw vi hmem).left (hfvalw vi hmem).right
          have hnotw : ∀ vi ∈ vs, (Factory.not (isSome (fval vi))).WellFormed εnv.entities ∧ (Factory.not (isSome (fval vi))).typeOf = .bool := by
            intro vi hmem
            have hns := wf_isSome (hfvalw vi hmem).left
            exact wf_not hns.left hns.right
          -- WF of the two εnv folds (over vs.map fval)
          have hconjw := foldr_and_wf (εs := εnv.entities) (g := fun pti => option.get pti) (vs.map fval)
            (by intro pti hmem; rw [List.mem_map] at hmem; obtain ⟨vi, hvm, rfl⟩ := hmem; exact hgetw vi hvm)
          have hanyErrw := foldr_or_wf (εs := εnv.entities) (g := fun pti => Factory.not (isSome pti)) (vs.map fval)
            (by intro pti hmem; rw [List.mem_map] at hmem; obtain ⟨vi, hvm, rfl⟩ := hmem; exact hnotw vi hvm)
          -- the εnv ite is WF with typeOf .option .bool
          have hitew := wf_ite hanyErrw.left (Term.WellFormed.none_wf TermType.WellFormed.bool_wf)
            (Term.WellFormed.some_wf hconjw.left) hanyErrw.right (by simp only [Factory.noneOf, typeOf_term_none, typeOf_term_some, hconjw.right])
          -- RHS: interpret the εnv ifSome; push interpret through the ite/fold; re-index via foldr_map
          simp only [Factory.noneOf, Factory.someOf]
          rw [interpret_ifSome hI ih1w hitew.left]
          rw [interpret_ite hI hanyErrw.left (Term.WellFormed.none_wf TermType.WellFormed.bool_wf)
            (Term.WellFormed.some_wf hconjw.left) hanyErrw.right
            (by simp only [Factory.noneOf, typeOf_term_none, typeOf_term_some, hconjw.right])]
          simp only [Factory.noneOf, Factory.someOf, interpret_term_none, interpret_term_some]
          rw [interpret_foldr_or hI (by intro pti hmem; rw [List.mem_map] at hmem; obtain ⟨vi, hvm, rfl⟩ := hmem; exact hnotw vi hvm),
            interpret_foldr_and hI (by intro pti hmem; rw [List.mem_map] at hmem; obtain ⟨vi, hvm, rfl⟩ := hmem; exact hgetw vi hvm)]
          rw [List.foldr_map, List.foldr_map]
          -- RHS ite equals the GOAL ite (fold_ite_val_congr), whose typeOf is .option .bool
          simp only [Factory.noneOf, Factory.someOf] at hfoldeq
          rw [← hfoldeq]
          have hgoality : (Factory.ite (vs.foldr (fun vi acc => Factory.or (Factory.not (Factory.isSome (fvalI vi))) acc) (false : Term))
              (Term.none .bool)
              ((vs.foldr (fun vi acc => Factory.and (Factory.option.get (fvalI vi)) acc) (true : Term)).some)).typeOf = .option .bool := by
            have hc := foldr_and_wf (εs := εnv.entities) (g := fun vi => option.get (fvalI vi)) vs
              (by intro vi hmem; exact wf_option_get (hfvalIwfl vi hmem).left.left (hfvalIwfl vi hmem).right)
            have he := foldr_or_wf (εs := εnv.entities) (g := fun vi => Factory.not (Factory.isSome (fvalI vi))) vs
              (by intro vi hmem; have hns := wf_isSome (hfvalIwfl vi hmem).left.left; exact wf_not hns.left hns.right)
            have := wf_ite he.left (Term.WellFormed.none_wf TermType.WellFormed.bool_wf) (Term.WellFormed.some_wf hc.left)
              he.right (by simp only [typeOf_term_none, typeOf_term_some, hc.right])
            rw [this.right]; simp only [typeOf_term_none]
          -- LHS: reduce the interpreted-side compile; case on interpret I t₁
          rw [compile.eq_def]; simp only []; rw [if_neg (by simp only [hnoit, not_true, not_false_eq_true])]; rw [hrecv]; simp only [Except.bind_ok]
          rcases wfl_of_type_option_is_option hwfl.left hwfl.right with hnone | ⟨w, hsome, hwty⟩
          · -- interpret I t₁ = .none ty1 : D-69 short-circuit; RHS ifSome (.none) collapses to noneOf
            have htys : ty1 = .set eltsTy :=
              (wf_option_get ih1w hty1).right.symm.trans (by rw [hvseq, typeOf_term_set])
            rw [hnone, htys]
            show _ = Except.ok (Factory.ifSome (Term.none (.set eltsTy)) _)
            rw [Factory.ifSome, hgoality]
            simp only [pe_isNone_none, pe_ite_true, Factory.noneOf]
          · -- interpret I t₁ = .some w : literal fold over vs
            have hswf : (Set.mk vs).WellFormed := by
              have h := hgt.left; rw [hvseq] at h
              cases h with | set_wf _ _ _ hw => exact hw
            have hw_eq : w = Term.set (Set.mk vs) eltsTy := by
              have hog := interpret_option_get I ih1w hty1
              rw [hsome, pe_option_get'_some] at hog
              rw [hvseq] at hog
              have hlitset : Term.interpret I (Term.set (Set.mk vs) eltsTy) = Term.set (Set.mk vs) eltsTy := by
                rw [interpret_term_set]
                have hmc : (Set.mk vs).map (Term.interpret I) = (Set.mk vs).map id := by
                  apply Set.map_congr
                  intro ti hti
                  simp only [id_eq]
                  have htl : ti ∈ vs := by rw [← Set.mem_elts_iff_mem_set] at hti; exact hti
                  exact interpret_lit_id ti (helts ti htl).left (hvslit ti htl)
                rw [hmc, Set.map_id (Set.mk vs) hswf]
              rw [hlitset] at hog; exact hog.symm
            subst hw_eq
            rw [hsome, pe_option_get_some]
            have hvs'lit : (vs.all fun x => x.isLiteral) = true := by
              simp only [List.all_eq_true]; intro vi hmem; exact hvslit vi hmem
            simp only [Term.typeOf, hvs'lit, if_true]
            -- bridge at plain I: compilePred p (someOf vi) (εnv.interpret I) = .ok (fvalI vi)
            have hbridge : ∀ vi ∈ vs, compilePred p (Factory.someOf vi) (εnv.interpret I) = .ok (fvalI vi) := by
              intro vi hmem
              have hviw : (Factory.someOf vi).WellFormed εnv.entities := Term.WellFormed.some_wf (helts vi hmem).left
              have hvity : (Factory.someOf vi).typeOf = .option eltsTy := by
                simp only [Factory.someOf, typeOf_term_some, (helts vi hmem).right]
              have hci := compilePred_interpret hI hwε.left hviw hvity (hpe vi hmem).left
              have hidv : (Factory.someOf vi).interpret I = Factory.someOf vi := by
                simp only [Factory.someOf, interpret_term_some, interpret_lit_id vi (helts vi hmem).left (hvslit vi hmem)]
              rw [hidv] at hci
              exact hci
            have hgetbool : ∀ vi ∈ vs, (option.get (fvalI vi)).typeOf = .bool := by
              intro vi hmem
              exact (wf_option_get (hfvalIwfl vi hmem).left.left (hfvalIwfl vi hmem).right).right
            rw [mapM_someOf_eq_map (p := p) (εnv := εnv.interpret I) (fval := fvalI) (vs' := vs) hbridge hgetbool]
            simp only [Except.bind_ok]
            rw [List.foldr_map, List.foldr_map]
            apply congrArg Except.ok
            rfl
        · rename_i hnlit
          simp_do_let (compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv) at hok
          rename_i pt hpt
          split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
          rename_i hpbool; subst hok
          exact symbolic hpt hpbool
      · simp_do_let (compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv) at hok
        rename_i pt hpt
        split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
        rename_i hpbool; subst hok
        exact symbolic hpt hpbool
    · simp only [reduceCtorEq] at hok

end Cedar.Thm
