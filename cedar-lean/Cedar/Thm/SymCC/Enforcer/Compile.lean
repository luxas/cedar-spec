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
import Cedar.Thm.SymCC.Concretizer
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.SymCC.Env.SWF
import Cedar.Thm.SymCC.Enforcer.Asserts
import Cedar.Thm.SymCC.Enforcer.Footprint
import Cedar.Thm.SymCC.Enforcer.Util
import Cedar.Thm.SymCC.Compiler

/-!
This file proves that a term produced by compiling an expression `x`
has the same value under interpretations `I₁` and `I₂` that agree
on the footprint of `x`.  See `compile_interpret_on_footprint`.

This proof relies on the theorem `compile_interpret_in_footprint`, which says
that every entity produced by interpreting a subexpression of `x` is
in the footprint of `x`.
--/


namespace Cedar.Thm

open Data Spec SymCC Factory

-------------------

private theorem compile_isOptionEntityType {x : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term} {uid : EntityUID}
  (hwε : εnv.WellFormedFor x)
  (hI  : I.WellFormed εnv.entities)
  (hok : compile x εnv = .ok t)
  (ht  : t.interpret I = .some (.entity uid)) :
  t.typeOf.isOptionEntityType
:= by
  have hwt := (compile_wf hwε hok).left
  have hty := (interpret_term_wf hI hwt).right
  rw [ht] at hty
  rw [← hty]
  simp only [TermType.isOptionEntityType, Term.typeOf, typeOf_term_prim_entity]

private theorem typeOf_ifSome_ite_option_bool {t₁ t₂ t₃ : Term} {εs : SymEntities} :
  t₁.WellFormed εs → t₂.WellFormed εs → t₃.WellFormed εs →
  t₁.typeOf = .option .bool → t₂.typeOf = .option .bool → t₃.typeOf = .option .bool →
  (ifSome t₁ (Factory.ite (option.get t₁) t₂ t₃)).typeOf = .option .bool
:= by
  intro hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty₃
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hwi := wf_ite hwo₁.left hwt₂ hwt₃ hwo₁.right (by simp only [hty₂, hty₃])
  rw [hty₂] at hwi
  simp only [wf_ifSome_option hwt₁ hwi.left hwi.right]

private theorem typeOf_compile_and_option_bool {x₁ x₂ : Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.and x₁ x₂))
  (hok : compile (.and x₁ x₂) εnv = .ok t) :
  t.typeOf = .option .bool
:= by
  replace ⟨t₁, hok₁, hok⟩ := compile_and_ok_implies hok
  split at hok
  · subst hok
    simp only [typeOf_term_some, typeOf_bool]
  · replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
    subst hok
    try have hwε := wf_εnv_for_and_implies hwε
    try have hwε := wf_εnv_for_or_implies hwε
    have hwt₁ := (compile_wf hwε.left hok₁).left
    have hwt₂ := (compile_wf hwε.right hok₂).left
    exact typeOf_ifSome_ite_option_bool hwt₁ hwt₂ (Term.WellFormed.some_wf wf_bool) hty₁ hty₂ (by simp only [typeOf_term_some, typeOf_bool])

private theorem typeOf_compile_or_option_bool {x₁ x₂ : Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.or x₁ x₂))
  (hok : compile (.or x₁ x₂) εnv = .ok t) :
  t.typeOf = .option .bool
:= by
  replace ⟨t₁, hok₁, hok⟩ := compile_or_ok_implies hok
  split at hok
  · subst hok
    simp only [typeOf_term_some, typeOf_bool]
  · replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
    subst hok
    try have hwε := wf_εnv_for_and_implies hwε
    try have hwε := wf_εnv_for_or_implies hwε
    have hwt₁ := (compile_wf hwε.left hok₁).left
    have hwt₂ := (compile_wf hwε.right hok₂).left
    exact typeOf_ifSome_ite_option_bool hwt₁ (Term.WellFormed.some_wf wf_bool) hwt₂ hty₁ (by simp only [typeOf_term_some, typeOf_bool]) hty₂

private theorem typeOf_compile_unaryApp_option_types {op₁ : UnaryOp} {x₁ : Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.unaryApp op₁ x₁))
  (hok : compile (.unaryApp op₁ x₁) εnv = .ok t) :
  t.typeOf = .option .bool ∨ t.typeOf = .option (.bitvec 64)
:= by
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compile_unaryApp_ok_implies hok
  subst heq
  have ⟨ty₁, ⟨hwt₁, _⟩, hwo₁⟩ := compile_option_get_wf (wf_εnv_for_unaryApp_implies hwε) hok₁
  have ⟨hwt₂, hty₂⟩ := compileApp₁_wf_types hwo₁.left hok
  split at hty₂ <;>
  simp only [wf_ifSome_option hwt₁ hwt₂ hty₂, TermType.option.injEq, TermType.prim.injEq, or_true, or_false, reduceCtorEq]

private theorem typeOf_compile_hasAttr_option_bool {x : Expr} {a : Attr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.hasAttr x a))
  (hok : compile (.hasAttr x a) εnv = .ok t) :
  t.typeOf = .option .bool
:= by
  replace ⟨_, _, hok₁, hok, heq⟩ := compile_hasAttr_ok_implies hok
  subst heq
  have ⟨_, ⟨hwt₁, _⟩, hwo₁⟩ := compile_option_get_wf (wf_εnv_for_hasAttr_implies hwε) hok₁
  have ⟨hwt₂, hty₂⟩ := compileHasAttr_wf hwε.left.right hwo₁.left hok
  simp only [wf_ifSome_option hwt₁ hwt₂ hty₂]

private theorem typeOf_compile_extHasAttr_option_bool {x : Expr} {a : Attr} {attrs : List Attr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.extHasAttr x a attrs))
  (hok : compile (.extHasAttr x a attrs) εnv = .ok t) :
  t.typeOf = .option .bool
:= compile_extHasAttr_typeOf hwε hok

private theorem typeOf_compile_set_option_set {xs : List Expr} {t : Term} {εnv : SymEnv}
  (hok : compile (.set xs) εnv = .ok t) :
  ∃ ty, t.typeOf = .option (.set ty)
:= by
  replace ⟨ts, _, hok⟩ := compile_set_ok_implies hok
  replace ⟨ty, _, _, _, _, hok⟩ := compileSet_ok_implies hok
  subst hok
  exists ty
  apply typeOf_ifAllSome_option_type
  simp only [setOf, Term.typeOf]

private theorem typeOf_compile_record_option_record {axs : List (Attr × Expr)} {t : Term} {εnv : SymEnv}
  (hok : compile (.record axs) εnv = .ok t) :
  ∃ rty, t.typeOf = .option (.record rty)
:= by
  replace ⟨ts, _, hok⟩ := compile_record_ok_implies hok
  subst hok
  simp only [compileRecord, someOf, recordOf]
  have ⟨rty, hty⟩ := @typeOf_term_record_is_record_type (Map.make (List.map (Prod.map id option.get) ts))
  exists rty
  apply typeOf_ifAllSome_option_type
  simp only [typeOf_term_some, hty]

private theorem typeOf_compile_call_option_types {xfn : ExtFun} {xs : List Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.call xfn xs))
  (hok : compile (.call xfn xs) εnv = .ok t) :
  t.typeOf = .option .bool ∨ (∃ xty, t.typeOf = .option (.ext xty)) ∨ t.typeOf = .option (.bitvec 64)
:= by
  replace ⟨ts, ha, hok⟩ := compile_call_ok_implies hok
  replace ha := List.forall₂_implies_all_right ha
  replace hwε := wf_εnv_for_call_implies hwε
  have hwf : ∀ t ∈ ts, t.WellFormed εnv.entities := by
    intro t ht
    replace ⟨x, ha, hr⟩ := ha t ht
    simp only [compile_wf (hwε x ha) hr]
  have ⟨_, hty⟩ := compileCall_wf_types hwf hok
  split at hty <;>
  simp only [hty, TermType.option.injEq, TermType.prim.injEq,
    TermPrimType.ext.injEq, exists_eq', or_true, exists_const, or_false, reduceCtorEq]

private theorem compile_interpret_lit_in_footprint {p : Prim} {εnv : SymEnv} {I : Interpretation} {t : Term} {uid : EntityUID}
  (hwε : εnv.WellFormedFor (Expr.lit p))
  (hI  : I.WellFormed εnv.entities)
  (hok : compile (Expr.lit p) εnv = .ok t)
  (ht  : t.interpret I = .some (.entity uid)) :
  ∃ tₑ ∈ footprint (Expr.lit p) εnv, tₑ.interpret I = .some (.entity uid)
:= by
  have hok' := hok
  have hty := compile_isOptionEntityType hwε hI hok ht
  simp only [compile, compilePrim] at hok
  cases p <;> simp only [someOf, Except.ok.injEq] at hok
  case bool | int | string =>
    subst hok
    simp only [TermType.isOptionEntityType, Term.typeOf, typeOf_bool, typeOf_bv, typeOf_term_prim_string, Bool.false_eq_true] at hty
  case entityUID uid' =>
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    simp only [interpret_term_some, interpret_term_prim, Term.some.injEq, Term.prim.injEq,
      TermPrim.entity.injEq] at ht
    subst ht
    exists (Term.some (Term.entity uid'))
    simp only [footprint, footprint.ofEntity, hok', TermType.isOptionEntityType, Term.typeOf,
      typeOf_term_prim_entity, ↓reduceIte, Set.mem_singleton, interpret_term_some,
      interpret_term_prim, and_self]

private theorem compile_interpret_var_in_footprint {v : Var} {εnv : SymEnv} {I : Interpretation} {t : Term} {uid : EntityUID}
  (hwε : εnv.WellFormedFor (Expr.var v))
  (hI  : I.WellFormed εnv.entities)
  (hok : compile (Expr.var v) εnv = .ok t)
  (ht  : t.interpret I = .some (.entity uid)) :
  ∃ tₑ ∈ footprint (Expr.var v) εnv, tₑ.interpret I = .some (.entity uid)
:= by
  have hok' := hok
  have hty := compile_isOptionEntityType hwε hI hok ht
  simp only [compile, compileVar] at hok
  cases v <;>
  simp only [someOf] at hok <;>
  split at hok <;>
  simp only [Except.ok.injEq, reduceCtorEq] at hok <;>
  subst hok
  case principal | action | resource =>
    simp only [interpret_term_some, Term.some.injEq] at ht
    simp only [footprint, footprint.ofEntity, hok', hty, ↓reduceIte, Set.mem_singleton,
      exists_eq_left, interpret_term_some, ht]
  case context hty' =>
    cases h : εnv.request.context.typeOf <;>
    simp only [TermType.isRecordType, h, Bool.false_eq_true] at hty'
    simp only [TermType.isOptionEntityType, typeOf_term_some, h, Bool.false_eq_true] at hty

private theorem interpret_ifSome_ite_eq_implies {t₁ t₂ t₃ t₄ : Term} {ty : TermType} {I : Interpretation} {εs : SymEntities} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs → t₃.WellFormed εs →
  t₁.typeOf = .option .bool → t₂.typeOf = .option ty → t₂.typeOf = t₃.typeOf →
  (ifSome t₁ (Factory.ite (option.get t₁) t₂ t₃)).interpret I = t₄.some →
  t₂.interpret I = t₄.some ∨ t₃.interpret I = t₄.some
:= by
  intro hI hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty heq
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hwi := wf_ite hwo₁.left hwt₂ hwt₃ hwo₁.right hty
  rw [hty₂] at hwi
  have hlit := interpret_term_wfl hI hwt₁
  rw [hty₁] at hlit
  simp only [interpret_ifSome hI hwt₁ hwi.left] at heq
  have hwi' := interpret_term_wf hI hwi.left
  rw [hwi.right] at hwi'
  have hopt := wfl_of_type_option_is_option hlit.left hlit.right
  rcases hopt with hopt | ⟨t', hopt, _⟩ <;>
  simp only [hopt, pe_ifSome_none hwi'.right, pe_ifSome_some hwi'.right, reduceCtorEq] at heq
  rename_i hty'
  simp only [interpret_ite hI hwo₁.left hwt₂ hwt₃ hwo₁.right hty,
    interpret_option_get I hwt₁ hty₁, hopt, pe_option_get'_some] at heq
  replace hlit := interpret_term_wfl hI hwt₁
  simp only [hopt] at hlit
  have hwt' := wf_term_some_implies hlit.left.left
  replace hlit := isLiteral_some.mp hlit.left.right
  have hb := wfl_of_type_bool_is_true_or_false (And.intro hwt' hlit) hty'
  rcases hb with hb | hb <;>
  subst hb <;>
  simp only [pe_ite_false, pe_ite_true] at heq <;>
  simp only [heq, true_or, or_true]

theorem compile_interpret_in_footprint {x : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term} {uid : EntityUID}
  (hwε : εnv.WellFormedFor x)
  (hI  : I.WellFormed εnv.entities)
  (hok : compile x εnv = .ok t)
  (ht  : t.interpret I = .some (.entity uid)) :
  ∃ tₑ ∈ footprint x εnv, tₑ.interpret I = .some (.entity uid)
:= by
  induction x using compile.induct generalizing t
  case case1 =>
    exact compile_interpret_lit_in_footprint hwε hI hok ht
  case case2 =>
    exact compile_interpret_var_in_footprint hwε hI hok ht
  case case3 x₁ x₂ x₃ _ ih₂ ih₃ =>
    replace hwε := wf_εnv_for_ite_implies hwε
    replace ⟨t₁, hok₁, hok⟩ := compile_ite_ok_implies hok
    simp only [footprint, footprint.ofBranch, hok₁]
    split at hok <;> simp only
    · rw [eq_comm] at hok
      exact ih₂ hwε.right.left hok ht
    · rw [eq_comm] at hok
      exact ih₃ hwε.right.right hok ht
    · replace ⟨hty₁, t₂, t₃, hok₂, hok₃, hty, hok⟩ := hok
      subst hok
      simp only [Set.mem_union]
      have hwt₁ := (compile_wf hwε.left hok₁).left
      have ⟨hwt₂, _, hty₂⟩ := compile_wf hwε.right.left hok₂
      have hwt₃ := (compile_wf hwε.right.right hok₃).left
      have heq := interpret_ifSome_ite_eq_implies hI hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty ht
      rcases heq with heq | heq
      · have ⟨tₑ, ih₂⟩ := ih₂ hwε.right.left hok₂ heq
        exists tₑ
        simp only [ih₂, or_true, true_or, and_self]
      · have ⟨tₑ, ih₃⟩ := ih₃ hwε.right.right hok₃ heq
        exists tₑ
        simp only [ih₃, or_true, and_self]
  case case10 =>
    simp only [footprint, footprint.ofEntity, hok, compile_isOptionEntityType hwε hI hok ht,
      ↓reduceIte, Set.mem_union, Set.mem_singleton, exists_eq_or_imp, ht, true_or]
  case' case4 =>
    have hty := typeOf_compile_and_option_bool hwε hok
  case' case5 =>
    have hty := typeOf_compile_or_option_bool hwε hok
  case' case6 =>
    have hty := typeOf_compile_unaryApp_option_types hwε hok
    rcases hty with hty | hty
  case case7 =>
    exists t
    simp [footprint, footprint.ofEntity, hok, compile_isOptionEntityType hwε hI hok ht,
      ↓reduceIte, Set.mem_union, Set.mem_singleton, ht]
  case' case8 =>
    have hty := typeOf_compile_hasAttr_option_bool hwε hok
  case' case9 =>
    have hty := typeOf_compile_extHasAttr_option_bool hwε hok
  case' case11 =>
    have ⟨_, hty⟩ := typeOf_compile_set_option_set hok
  case' case12 =>
    have ⟨_, hty⟩ := typeOf_compile_record_option_record hok
  case' case13 =>
    have hty := typeOf_compile_call_option_types hwε hok
    rcases hty with hty | ⟨_, hty⟩ | hty
  case' case14 =>
    have hty := typeOf_compile_all_option_bool hwε hok
  case' case15 =>
    have hty := typeOf_compile_all_option_bool hwε hok
  all_goals {
    have hty' := compile_isOptionEntityType hwε hI hok ht
    simp only [TermType.isOptionEntityType, hty, Bool.false_eq_true] at hty'
  }

-------------------

private def CompileInterpretOnFootprint (x : Expr) (ft : Set Term) (εnv : SymEnv) (I₁ I₂ : Interpretation) : Prop :=
  ∀ {t : Term},
    εnv.WellFormedFor x →
    I₁.WellFormed εnv.entities →
    I₂.WellFormed εnv.entities →
    εnv.SameOn ft I₁ I₂ →
    footprint x εnv ⊆ ft →
    compile x εnv = .ok t →
    t.interpret I₁ = t.interpret I₂

theorem compile_interpret_lit_on_footprint {p : Prim} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hok : compile (.lit p) εnv = .ok t) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [compile, compilePrim] at hok
  split at hok <;>
  (try split at hok) <;>
  simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok <;>
  subst hok <;>
  simp only [interpret_term_some, interpret_term_prim]

theorem compile_interpret_var_on_footprint {v : Var} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.var v))
  (hsm : εnv.SameOn ft I₁ I₂)
  (hok : compile (.var v) εnv = .ok t) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [compile, compileVar] at hok
  replace hsm := hsm.left
  simp only [SymRequest.interpret, SymRequest.mk.injEq] at hsm
  cases v
  all_goals {
    simp only at hok
    split at hok <;>
    simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    simp only [someOf, interpret_term_some, hsm]
  }

local macro "simp_ifSome_eq" hI₁:ident hI₂:ident hwt₁:ident hty₁:ident hwt₂:ident hty₂:ident ih:ident : tactic => do
  `(tactic | (
    simp only [interpret_ifSome $hI₁ $hwt₁ $hwt₂, interpret_ifSome $hI₂ $hwt₁ $hwt₂, $ih:ident]
    have hwt₁₂ := interpret_term_wf $hI₁ $hwt₂
    have hwt₂₂ := interpret_term_wf $hI₂ $hwt₂
    rw [$hty₂:term] at hwt₁₂ hwt₂₂
    have hwl₂ := interpret_term_wfl $hI₂ $hwt₁
    rw [$hty₁:term] at hwl₂
    have hlit₂ := wfl_of_type_option_is_option hwl₂.left hwl₂.right
    rcases hlit₂ with hlit₂ | ⟨t₂', hlit₂, hty₂'⟩ <;>
    simp only [hlit₂, pe_ifSome_none hwt₁₂.right, pe_ifSome_none hwt₂₂.right]
    simp only [pe_ifSome_some hwt₁₂.right, pe_ifSome_some hwt₂₂.right]
    clear hwt₁₂ hwt₂₂ hwl₂))

private theorem interpret_option_get_eq {t t' : Term} {I₁ I₂ : Interpretation} {εs : SymEntities} :
  t.WellFormed εs → t.typeOf = .option ty →
  t.interpret I₁ = t.interpret I₂ →
  t.interpret I₂ = .some t' →
  (Factory.option.get t).interpret I₁ = (Factory.option.get t).interpret I₂
:= by
  intro hwt hty heq₁ heq₂
  simp only [interpret_option_get I₁ hwt hty, heq₁, heq₂, pe_option_get'_some,
    interpret_option_get I₂ hwt hty]

private theorem interpret_ifSome_ifSome_ite_eq {t₁ t₂ t₃ : Term} {I₁ I₂ : Interpretation} {εs : SymEntities} :
  I₁.WellFormed εs → I₂.WellFormed εs →
  t₁.WellFormed εs → t₂.WellFormed εs → t₃.WellFormed εs →
  t₁.typeOf = .option .bool →
  t₂.typeOf = .option ty →
  t₃.typeOf = .option ty →
  t₁.interpret I₁ = t₁.interpret I₂ →
  t₂.interpret I₁ = t₂.interpret I₂ →
  t₃.interpret I₁ = t₃.interpret I₂ →
  (ifSome t₁ (Factory.ite (option.get t₁) t₂ t₃)).interpret I₁ =
  (ifSome t₁ (Factory.ite (option.get t₁) t₂ t₃)).interpret I₂
:= by
  intro hI₁ hI₂ hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty₃ ht₁ ht₂ ht₃
  have ⟨hwo₁, hoty₁⟩ := wf_option_get hwt₁ hty₁
  rw [← hty₂, eq_comm] at hty₃
  have hwi := wf_ite hwo₁ hwt₂ hwt₃ hoty₁ hty₃
  rw [hty₂] at hwi
  have hwi₁ := interpret_term_wf hI₁ hwi.left
  have hwi₂ := interpret_term_wf hI₂ hwi.left
  rw [hwi.right] at hwi₁ hwi₂
  simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hwi.left hwi.right ht₁
  rename_i ht₁' _
  simp only [interpret_ite hI₁ hwo₁ hwt₂ hwt₃ hoty₁ hty₃,
    interpret_ite hI₂ hwo₁ hwt₂ hwt₃ hoty₁ hty₃,
    ht₂, ht₃, interpret_option_get_eq hwt₁ hty₁ ht₁ ht₁']

private theorem compile_interpret_ite_on_footprint {x₁ x₂ x₃ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.ite x₁ x₂ x₃))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.ite x₁ x₂ x₃) εnv ⊆ ft)
  (hok : compile (.ite x₁ x₂ x₃) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂)
  (ih₂ : CompileInterpretOnFootprint x₂ ft εnv I₁ I₂)
  (ih₃ : CompileInterpretOnFootprint x₃ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace hwε := wf_εnv_for_ite_implies hwε
  replace ⟨t₁, hok₁, hok⟩ := compile_ite_ok_implies hok
  split at hok <;>
  simp only [footprint, footprint.ofBranch, hok₁] at hft
  · rw [eq_comm] at hok
    exact ih₂ hwε.right.left hI₁ hI₂ hsm hft hok
  · rw [eq_comm] at hok
    exact ih₃ hwε.right.right hI₁ hI₂ hsm hft hok
  · rename_i hnt hnf
    replace ⟨hty₁, t₂, t₃, hok₂, hok₃, hty, hok⟩ := hok
    subst hok
    simp only [Set.union_subset] at hft
    have hwt₁ := (compile_wf hwε.left hok₁).left
    have ⟨hwt₂, _, hty₂⟩ := compile_wf hwε.right.left hok₂
    have hwt₃ := (compile_wf hwε.right.right hok₃).left
    have hty₃ := hty₂ ; rw [hty] at hty₃
    exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂ hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty₃
      (ih₁ hwε.left hI₁ hI₂ hsm hft.left.left hok₁)
      (ih₂ hwε.right.left hI₁ hI₂ hsm hft.left.right hok₂)
      (ih₃ hwε.right.right hI₁ hI₂ hsm hft.right hok₃)

private theorem compile_interpret_and_on_footprint {x₁ x₂ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.and x₁ x₂))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.and x₁ x₂) εnv ⊆ ft)
  (hok : compile (.and x₁ x₂) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂)
  (ih₂ : CompileInterpretOnFootprint x₂ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace ⟨t₁, hok₁, hok⟩ := compile_and_ok_implies hok
  split at hok
  · subst hok
    simp only [interpret_term_some, interpret_term_prim]
  · rename_i hf
    replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
    subst hok
    replace hwε := wf_εnv_for_and_implies hwε
    cases ht : decide (t₁ = .some (.bool true)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ht <;>
    simp only [footprint, footprint.ofBranch, hok₁] at hft
    · simp only [Set.union_subset] at hft
      specialize @ih₁ t₁ hwε.left hI₁ hI₂ hsm hft.left.left hok₁
      specialize @ih₂ t₂ hwε.right hI₁ hI₂ hsm hft.left.right hok₂
      have hwt₁ := (compile_wf hwε.left hok₁).left
      have hwt₂ := (compile_wf hwε.right hok₂).left
      exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂
        hwt₁ hwt₂ (Term.WellFormed.some_wf wf_bool)
        hty₁ hty₂ (by simp only [typeOf_term_some, typeOf_bool])
        ih₁ ih₂ (by simp only [interpret_term_some, interpret_term_prim])
    · subst ht
      specialize @ih₂ t₂ hwε.right hI₁ hI₂ hsm hft hok₂
      simp only [pe_option_get_some, pe_ite_true, pe_ifSome_some hty₂, ih₂]

private theorem compile_interpret_or_on_footprint {x₁ x₂ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.or x₁ x₂))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.or x₁ x₂) εnv ⊆ ft)
  (hok : compile (.or x₁ x₂) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂)
  (ih₂ : CompileInterpretOnFootprint x₂ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace ⟨t₁, hok₁, hok⟩ := compile_or_ok_implies hok
  split at hok
  · subst hok
    simp only [interpret_term_some, interpret_term_prim]
  · rename_i hf
    replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
    subst hok
    replace hwε := wf_εnv_for_or_implies hwε
    cases ht : decide (t₁ = .some (.bool false)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ht <;>
    simp only [footprint, footprint.ofBranch, hok₁] at hft
    · simp only [Set.union_subset] at hft
      specialize @ih₁ t₁ hwε.left hI₁ hI₂ hsm hft.left.left hok₁
      specialize @ih₂ t₂ hwε.right hI₁ hI₂ hsm hft.right hok₂
      have hwt₁ := (compile_wf hwε.left hok₁).left
      have hwt₂ := (compile_wf hwε.right hok₂).left
      exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂
        hwt₁ (Term.WellFormed.some_wf wf_bool) hwt₂
        hty₁ (by simp only [typeOf_term_some, typeOf_bool]) hty₂
        ih₁ (by simp only [interpret_term_some, interpret_term_prim]) ih₂
    · subst ht
      specialize @ih₂ t₂ hwε.right hI₁ hI₂ hsm hft hok₂
      simp only [pe_option_get_some, pe_ite_false, pe_ifSome_some hty₂, ih₂]

private theorem same_footprint_ancestors {x : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t t' : Term} {ety₁ : EntityType}
  (hwε  : εnv.WellFormedFor x)
  (hI₁  : I₁.WellFormed εnv.entities)
  (hsm  : εnv.SameOn ft I₁ I₂)
  (hft  : footprint x εnv ⊆ ft)
  (hok  : compile x εnv = Except.ok t)
  (heq₁ : Term.interpret I₁ t = Term.interpret I₂ t)
  (heq₂ : Term.interpret I₂ t = t'.some)
  (hty  : t'.typeOf = .entity ety₁) :
  ∃ uid₁ : EntityUID,
    t' = .entity uid₁ ∧
    uid₁.ty = ety₁ ∧
    ∀ ety₂ f,
      εnv.entities.ancestorsOfType uid₁.ty ety₂ = some f →
      app (UnaryFunction.interpret I₁ f) (Term.entity uid₁) =
      app (UnaryFunction.interpret I₂ f) (Term.entity uid₁)
:= by
  rw [heq₂] at heq₁
  have hwt := (compile_wf hwε hok).left
  have hlit := (interpret_term_wfl hI₁ hwt).left
  simp only [heq₁] at hlit
  replace ⟨hwt, hlit⟩ := hlit
  rw [isLiteral_some] at hlit
  replace hwt := wf_term_some_implies hwt
  have ⟨uid₁, ht', hty'⟩ := wfl_of_type_entity_is_entity (And.intro hwt hlit) hty
  subst ht' hty'
  simp only [Term.prim.injEq, TermPrim.entity.injEq, exists_eq_left', true_and]
  intro ety₂ f hancs
  simp only [SymEntities.ancestorsOfType, SymEntities.ancestors, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at hancs
  replace ⟨_, ⟨δ, hδ, hancs⟩, hf⟩ := hancs
  subst hancs
  have ⟨tₑ, hin, heq₃⟩ := compile_interpret_in_footprint hwε hI₁ hok heq₁
  replace hin := Set.mem_subset_mem hin hft
  exact (hsm.right uid₁.ty δ hδ).right.left ety₂ f hf tₑ hin uid₁ heq₃ rfl

private theorem compile_interpret_unaryApp_on_footprint {op₁ : UnaryOp} {x₁ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.unaryApp op₁ x₁))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.unaryApp op₁ x₁) εnv ⊆ ft)
  (hok : compile (.unaryApp op₁ x₁) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint] at hft
  replace hwε := wf_εnv_for_unaryApp_implies hwε
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compile_unaryApp_ok_implies hok
  subst heq
  specialize ih₁ hwε hI₁ hI₂ hsm hft hok₁
  replace ⟨ty₁, hwt₁, hwo₁⟩ := compile_option_get_wf hwε hok₁
  have hwt₂ := compileApp₁_wf_types hwo₁.left hok
  have ⟨_, hty₂⟩ : ∃ ty, t₂.typeOf = .option ty := by
    split at hwt₂ <;> simp only [hwt₂, TermType.option.injEq, exists_eq']
  replace hwt₂ := hwt₂.left
  simp_ifSome_eq hI₁ hI₂ hwt₁.left hwt₁.right hwt₂ hty₂ ih₁
  rename_i ht₁ _
  replace ih₁ := interpret_option_get_eq hwt₁.left hwt₁.right ih₁ ht₁
  have hr₁ := interpret_compileApp₁ hI₁ hwo₁.left hok
  have hr₂ := interpret_compileApp₁ hI₂ hwo₁.left hok
  simp only [ih₁, hr₂, Except.ok.injEq] at hr₁
  simp only [hr₁]

private theorem compile_interpret_binaryApp_on_footprint {op₂ : BinaryOp} {x₁ x₂ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.binaryApp op₂ x₁ x₂))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.binaryApp op₂ x₁ x₂) εnv ⊆ ft)
  (hok : compile (.binaryApp op₂ x₁ x₂) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂)
  (ih₂ : CompileInterpretOnFootprint x₂ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace ⟨t₁, t₂, t₃, hok₁, hok₂, hok, ht⟩ := compile_binaryApp_ok_implies hok
  subst ht
  replace ⟨hwε, hwt₂⟩ := wf_εnv_for_binaryApp_implies hwε
  simp only [footprint, Set.union_subset] at hft
  specialize @ih₁ t₁ hwε hI₁ hI₂ hsm hft.left.right hok₁
  specialize @ih₂ t₂ hwt₂ hI₁ hI₂ hsm hft.right hok₂
  replace ⟨ty₁, hwt₁, hwo₁⟩ := compile_option_get_wf hwε hok₁
  replace ⟨ty₂, hwt₂, hwo₂⟩ := compile_option_get_wf hwt₂ hok₂
  have ⟨hwt₃, ty₃, hty₃⟩ := compileApp₂_wf hwε.left.right hwo₁.left hwo₂.left hok
  have hwt₂₃ := wf_ifSome_option hwt₂.left hwt₃ hty₃
  simp_ifSome_eq hI₁ hI₂ hwt₁.left hwt₁.right hwt₂₃.left hwt₂₃.right ih₁
  rename_i t₁' hlit₁ hty₁'
  simp_ifSome_eq hI₁ hI₂ hwt₂.left hwt₂.right hwt₃ hty₃ ih₂
  rename_i hlit₂ _
  clear hwt₃ hty₃ hwt₂₃
  have ih₁' := interpret_option_get_eq hwt₁.left hwt₁.right ih₁ hlit₁
  have ih₂' := interpret_option_get_eq hwt₂.left hwt₂.right ih₂ hlit₂
  cases op₂
  case eq =>
    rcases compileApp₂_eq_ok_implies hok with ⟨_, hok⟩ | ⟨_, hok⟩ <;> subst hok
    · simp only [interpret_term_some, interpret_eq hI₁ hwo₁.left hwo₂.left,
        interpret_eq hI₂ hwo₁.left hwo₂.left, ih₁', ih₂']
    · simp only [interpret_term_some, interpret_term_prim]
  case mem =>
    replace ⟨ety₁, ety₂, hety₁, hok⟩ := compileApp₂_mem_ok_implies hok
    have hwl₁₁ := interpret_term_wf hI₁ hwo₁.left
    have hwl₁₂ := interpret_term_wf hI₁ hwo₂.left
    have hwl₂₁ := interpret_term_wf hI₂ hwo₁.left
    have hwl₂₂ := interpret_term_wf hI₂ hwo₂.left
    rcases hok with ⟨hety₂, hok⟩ | ⟨hety₂, hok⟩
    all_goals {
      subst hok
      simp only [hwo₁.right] at hety₁
      simp only [hwo₂.right] at hety₂
      subst hety₁ hety₂
      have ⟨uid₁, heqt, heqty, heqf⟩ := same_footprint_ancestors hwε hI₁ hsm hft.left.right hok₁ ih₁ hlit₁ hty₁'
      subst heqt heqty
      simp only [interpret_term_some]
      try simp only [
        interpret_compileInₑ hwε.left.right hI₁ hwo₁.left hwo₂.left hwl₁₁ hwl₁₂ hwo₁.right hwo₂.right,
        interpret_compileInₑ hwε.left.right hI₂ hwo₁.left hwo₂.left hwl₂₁ hwl₂₂ hwo₁.right hwo₂.right]
      try simp only [
        interpret_compileInₛ hwε.left.right hI₁ hwo₁.left hwo₂.left hwl₁₁ hwl₁₂ hwo₁.right hwo₂.right,
        interpret_compileInₛ hwε.left.right hI₂ hwo₁.left hwo₂.left hwl₂₁ hwl₂₂ hwo₁.right hwo₂.right]
      simp only [ih₁', ih₂',
        interpret_option_get I₂ hwt₁.left hwt₁.right,
        interpret_option_get I₂ hwt₂.left hwt₂.right,
        hlit₁, hlit₂, pe_option_get'_some, compileInₑ, compileInₛ, Term.some.injEq]
      cases hancs : εnv.entities.ancestorsOfType uid₁.ty ety₂
      case none =>
        simp only [interpret_entities_ancestorsOfType_none hancs]
      case some f =>
        simp only [interpret_entities_ancestorsOfType_some hancs]
        specialize heqf ety₂ f hancs
        simp only [SymCC.compileInₑ.isIn, SymCC.compileInₛ.isIn₁, SymCC.compileInₛ.isIn₂]
        congr 2
    }
  case less =>
    rcases compileApp₂_less_ok_implies hok with ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩
    all_goals(
      subst hok
      simp only [interpret_term_some, interpret_bvslt, interpret_ext_duration_val,
        interpret_ext_datetime_val, ih₁', ih₂']
    )
  case lessEq =>
    rcases compileApp₂_lessEq_ok_implies hok with ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩
    all_goals(
      subst hok
      simp only [interpret_term_some, interpret_bvsle, interpret_ext_duration_val,
        interpret_ext_datetime_val, ih₁', ih₂']
    )
  case contains =>
    replace ⟨_, hok⟩ := compileApp₂_contains_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_member hwo₂.left hwo₁.left, ih₁', ih₂']
  case containsAll =>
    replace ⟨_, _, _, hok⟩ := compileApp₂_containsAll_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_subset hwo₂.left hwo₁.left, ih₁', ih₂']
  case containsAny =>
    replace ⟨_, hty₁, hty₂, hok⟩ := compileApp₂_containsAny_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_intersects hI₁ hwo₁.left hwo₂.left hty₁ hty₂,
      ih₁', ih₂', interpret_set_intersects hI₂ hwo₁.left hwo₂.left hty₁ hty₂]
  case add =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_add_ok_implies hok
    subst hok
    have hwa := wf_bvadd hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvsaddo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvsaddo, interpret_bvadd, ih₁', ih₂']
  case sub =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_sub_ok_implies hok
    subst hok
    have hwa := wf_bvsub hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvssubo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvssubo, interpret_bvsub, ih₁', ih₂']
  case mul =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_mul_ok_implies hok
    subst hok
    have hwa := wf_bvmul hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvsmulo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvsmulo, interpret_bvmul, ih₁', ih₂']
  case hasTag =>
    replace ⟨ety, hty₁, _, hok⟩ := compileApp₂_hasTag_ok_implies hok
    replace hok := compileHasTag_ok_implies hok
    rcases hok with ⟨_, hok⟩ | ⟨τs, hτs, hok⟩ <;> subst hok
    · simp only [interpret_term_some, interpret_term_prim]
    · simp only [interpret_term_some,
        ← interpret_hasTag (wf_εs_implies_wf_tags hwε.left.right hτs) hI₁ hwo₁.left hwo₂.left hty₁,
        ← interpret_hasTag (wf_εs_implies_wf_tags hwε.left.right hτs) hI₂ hwo₁.left hwo₂.left hty₁,
        ih₁', ih₂', Term.some.injEq]
      simp only [SymEntities.tags, Option.map_eq_some_iff] at hτs
      replace ⟨δ, hδ, hτs⟩ := hτs
      simp only [(hsm.right ety δ hδ).right.right τs hτs]
  case getTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_getTag_ok_implies hok
    replace ⟨τs, hτs, hok⟩ := compileGetTag_ok_implies hok
    subst hok
    simp only [
      ← interpret_getTag (wf_εs_implies_wf_tags hwε.left.right hτs) hI₁ hwo₁.left hwo₂.left hty₁ hty₂,
      ← interpret_getTag (wf_εs_implies_wf_tags hwε.left.right hτs) hI₂ hwo₁.left hwo₂.left hty₁ hty₂,
      ih₁', ih₂']
    simp only [SymEntities.tags, Option.map_eq_some_iff] at hτs
    replace ⟨δ, hδ, hτs⟩ := hτs
    simp only [(hsm.right ety δ hδ).right.right τs hτs]

private theorem compileAttrsOf_interpret_record_get_eq {t₁ t₃ : Term} {a₁ : Attr} {tyₐ : TermType} {rty : Map Attr TermType} {εs : SymEntities} {I₁ I₂ : Interpretation}
  (hwε  : εs.WellFormed)
  (hI₁  : I₁.WellFormed εs)
  (hI₂  : I₂.WellFormed εs)
  (hsm  : εs.SameOn ft I₁ I₂)
  (hwt₁ : t₁.WellFormed εs)
  (hok  : compileAttrsOf t₁ εs = .ok t₃)
  (hwt₃ : Term.WellFormed εs t₃)
  (hty₃ : t₃.typeOf = TermType.record rty)
  (htyₐ : rty.find? a₁ = some tyₐ)
  (ih₁  : Term.interpret I₁ t₁ = Term.interpret I₂ t₁) :
  (record.get t₃ a₁).interpret I₁ = (record.get t₃ a₁).interpret I₂
:= by
  replace hok := compileAttrsOf_ok_implies hok
  rcases hok with ⟨_, hty₁, hok⟩ | ⟨ety, fₐ, hty₁, hf, hok⟩ <;>
  subst hok <;>
  simp only [interpret_record_get I₁ hwt₃ hty₃ htyₐ, interpret_record_get I₂ hwt₃ hty₃ htyₐ, ih₁]
  have hwf := wf_εs_implies_wf_attrs hwε hf
  rw [eq_comm, ← hty₁] at hwf
  simp only [interpret_app hI₁ hwt₁ hwf.left hwf.right.left, interpret_app hI₂ hwt₁ hwf.left hwf.right.left, ih₁]
  simp only [SymEntities.attrs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hf
  replace ⟨δ, hf⟩ := hf
  replace hsm := (hsm ety δ hf.left).left
  simp only [hf.right] at hsm
  simp only [hsm]

private theorem compile_interpret_hasAttr_on_footprint {x₁ : Expr}  {a₁ : Attr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.hasAttr x₁ a₁))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.hasAttr x₁ a₁) εnv ⊆ ft)
  (hok : compile (.hasAttr x₁ a₁) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace hwε := wf_εnv_for_hasAttr_implies hwε
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compile_hasAttr_ok_implies hok
  subst heq
  simp only [footprint] at hft
  specialize ih₁ hwε hI₁ hI₂ hsm hft hok₁
  have ⟨ty₁, ⟨hwt₁, hty₁⟩, hwo₁⟩ := compile_option_get_wf hwε hok₁
  replace ⟨t₃, rty, hok, hr⟩ := compileHasAttr_ok_implies hok
  replace ⟨hty₃, hr⟩ := hr
  split at hr <;> subst hr
  case h_1 tyₐ htyₐ =>
    have hwt₃ := (compileAttrsOf_wf hwε.left.right hwo₁.left hok).left
    have hwr := wf_record_get hwt₃ hty₃ htyₐ
    have ⟨hws, hwsty⟩ := wf_isSome hwr.left
    replace ⟨hws, hwsty⟩ := wf_term_some hws hwsty
    simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hws hwsty ih₁
    rename_i ht₁ _
    simp only [interpret_term_some, interpret_isSome hI₁ hwr.left,
      interpret_isSome hI₂ hwr.left,
      compileAttrsOf_interpret_record_get_eq
        hwε.left.right hI₁ hI₂ hsm.right hwo₁.left hok hwt₃ hty₃ htyₐ
        (interpret_option_get_eq hwt₁ hty₁ ih₁ ht₁)]
  case h_2 | h_3 =>
    simp only [interpret_ifSome hI₁ hwt₁ (Term.WellFormed.some_wf wf_bool),
      interpret_ifSome hI₂ hwt₁ (Term.WellFormed.some_wf wf_bool),
      ih₁, interpret_term_some, interpret_term_prim]

private theorem compileExtHasAttrRec_interpret_eq
  {t₁ : Term} {attrs : List Attr} {εs : SymEntities} {ft : Set Term}
  {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εs.WellFormed)
  (hI₁ : I₁.WellFormed εs)
  (hI₂ : I₂.WellFormed εs)
  (hsm : εs.SameOn ft I₁ I₂)
  (hw₁ : t₁.WellFormed εs)
  (hty₁ : ∃ ty, t₁.typeOf = .option ty)
  (hih : t₁.interpret I₁ = t₁.interpret I₂)
  (hok : compileExtHasAttrRec t₁ attrs εs = .ok t) :
  t.interpret I₁ = t.interpret I₂ := by
  induction attrs generalizing t₁ t with
  | nil =>
    simp only [compileExtHasAttrRec, pure, Except.pure, Except.ok.injEq] at hok
    subst hok
    simp [interpret_term_some, interpret_term_prim]
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [compileExtHasAttrRec, bind, Except.bind] at hok
      generalize hha : compileHasAttr (option.get t₁) a εs = rha at hok
      cases rha with
      | error => simp only [reduceCtorEq] at hok
      | ok t_ha =>
        simp only [Except.ok.injEq] at hok; subst hok
        -- This is the same as hasAttr: t = ifSome t₁ t_ha
        have hwo := wf_option_get hw₁ hty₁.choose_spec
        have hwt₁ : t₁.WellFormed εs ∧ t₁.typeOf = .option hty₁.choose := ⟨hw₁, hty₁.choose_spec⟩
        have ⟨t₃, rty, hok_attrs, hr⟩ := compileHasAttr_ok_implies hha
        replace ⟨hty₃, hr⟩ := hr
        split at hr <;> subst hr
        case h_1 tyₐ htyₐ =>
          have hwt₃ := (compileAttrsOf_wf hwε hwo.left hok_attrs).left
          have hwr := wf_record_get hwt₃ hty₃ htyₐ
          have ⟨hws, hwsty⟩ := wf_isSome hwr.left
          replace ⟨hws, hwsty⟩ := wf_term_some hws hwsty
          simp_ifSome_eq hI₁ hI₂ hw₁ hty₁.choose_spec hws hwsty hih
          rename_i ht₁ _
          simp only [interpret_term_some, interpret_isSome hI₁ hwr.left,
            interpret_isSome hI₂ hwr.left,
            compileAttrsOf_interpret_record_get_eq
              hwε hI₁ hI₂ hsm hwo.left hok_attrs hwt₃ hty₃ htyₐ
              (interpret_option_get_eq hw₁ hty₁.choose_spec hih ht₁)]
        case h_2 | h_3 =>
          simp only [interpret_ifSome hI₁ hw₁ (Term.WellFormed.some_wf wf_bool),
            interpret_ifSome hI₂ hw₁ (Term.WellFormed.some_wf wf_bool),
            hih, interpret_term_some, interpret_term_prim]
    | cons b rest' =>
      simp [compileExtHasAttrRec, bind, Except.bind] at hok
      split at hok
      . contradiction
      . rename_i _ t_ha hha
        have hwo := wf_option_get hw₁ hty₁.choose_spec
        have hwha := compileHasAttr_wf hwε hwo.left hha
        have hiha :
          (ifSome t₁ t_ha).interpret I₁ = (ifSome t₁ t_ha).interpret I₂ := by
          have ⟨t₃, rty, hok_attrs, hr⟩ := compileHasAttr_ok_implies hha
          replace ⟨hty₃, hr⟩ := hr
          split at hr <;> subst hr
          case h_1 tyₐ htyₐ =>
            have hwt₃ := (compileAttrsOf_wf hwε hwo.left hok_attrs).left
            have hwr := wf_record_get hwt₃ hty₃ htyₐ
            have ⟨hws, hwsty⟩ := wf_isSome hwr.left
            replace ⟨hws, hwsty⟩ := wf_term_some hws hwsty
            simp_ifSome_eq hI₁ hI₂ hw₁ hty₁.choose_spec hws hwsty hih
            rename_i ht₁ _
            simp only [interpret_term_some, interpret_isSome hI₁ hwr.left,
              interpret_isSome hI₂ hwr.left,
              compileAttrsOf_interpret_record_get_eq
                hwε hI₁ hI₂ hsm hwo.left hok_attrs hwt₃ hty₃ htyₐ
                (interpret_option_get_eq hw₁ hty₁.choose_spec hih ht₁)]
          case h_2 | h_3 =>
            simp only [interpret_ifSome hI₁ hw₁ (Term.WellFormed.some_wf wf_bool),
              interpret_ifSome hI₂ hw₁ (Term.WellFormed.some_wf wf_bool),
              hih, interpret_term_some, interpret_term_prim]
        split at hok
        case h_1 =>
          simp only [pure, Except.pure, Except.ok.injEq] at hok
          subst t
          exact hiha
        case h_2 =>
          split at hok
          case h_1 =>
            simp only [pure, Except.pure, Except.ok.injEq] at hok
            subst t
            exact hiha
          case h_2 => simp only [reduceCtorEq] at hok
          case h_3 =>
            rename_i _ _ _ _ t_ga hga
            have ⟨hwga, tyga, htyga⟩ := compileGetAttr_wf hwε hwo.left hga
            have hwnext := wf_ifSome_option hw₁ hwga htyga
            have hinext :
              (ifSome t₁ t_ga).interpret I₁ = (ifSome t₁ t_ga).interpret I₂ := by
              have ⟨t₃, rty, hok_attrs, hr⟩ := compileGetAttr_ok_implies hga
              replace ⟨hty₃, tyₐ, htyₐ, hr⟩ := hr
              have hwt₃ := (compileAttrsOf_wf hwε hwo.left hok_attrs).left
              have ⟨hwr, hwrty⟩ := wf_record_get hwt₃ hty₃ htyₐ
              split at hr <;> subst hr
              case' h_2 => replace ⟨hwr, hwrty⟩ := wf_term_some hwr hwrty
              all_goals simp_ifSome_eq hI₁ hI₂ hw₁ hty₁.choose_spec hwr hwrty hih
              all_goals rename_i ht₁ _
              all_goals simp only [interpret_term_some,
                compileAttrsOf_interpret_record_get_eq
                  hwε hI₁ hI₂ hsm hwo.left hok_attrs hwt₃ hty₃ htyₐ
                  (interpret_option_get_eq hw₁ hty₁.choose_spec hih ht₁)]
            split at hok
            case h_1 => simp only [reduceCtorEq] at hok
            case h_2 =>
              rename_i _ t_rest hrest
              have hirest := ih hwnext.left ⟨tyga, hwnext.right⟩ hinext hrest
              have hwhas := wf_ifSome_option hw₁ hwha.left hwha.right
              have hwrest := compileExtHasAttrRec_wf hwε hwnext.left ⟨tyga, hwnext.right⟩ hrest
              simp only [compileAnd] at hok
              split at hok
              case h_1 => contradiction
              case h_2 =>
                simp only [Except.bind_ok, hwrest.right, ↓reduceIte, Except.ok.injEq] at hok
                subst t
                exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂
                  hwhas.left hwrest.left (Term.WellFormed.some_wf wf_bool)
                  hwhas.right hwrest.right (by simp only [someOf, typeOf_term_some, typeOf_bool])
                  hiha hirest (by simp only [interpret_someOf, interpret_term_prim])
              case h_3 => simp only [reduceCtorEq] at hok


private theorem compile_interpret_extHasAttr_on_footprint {x₁ : Expr} {a₁ : Attr} {attrs : List Attr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.extHasAttr x₁ a₁ attrs))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.extHasAttr x₁ a₁ attrs) εnv ⊆ ft)
  (hok : compile (.extHasAttr x₁ a₁ attrs) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint] at hft
  replace hwε' := wf_εnv_for_extHasAttr_implies hwε
  rw [compile.eq_def] at hok
  simp only at hok
  simp_do_let (compile x₁ εnv) at hok
  rename_i t₁ hok₁
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  specialize ih₁ hwε' hI₁ hI₂ hsm hft hok₁
  have ⟨hwt₁, ty₁, hty₁⟩ := compile_wf hwε' hok₁
  exact compileExtHasAttrRec_interpret_eq hwε'.left.right hI₁ hI₂ hsm.right hwt₁ ⟨ty₁, hty₁⟩ ih₁ hok

private theorem compile_interpret_getAttr_on_footprint {x₁ : Expr}  {a₁ : Attr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.getAttr x₁ a₁))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.getAttr x₁ a₁) εnv ⊆ ft)
  (hok : compile (.getAttr x₁ a₁) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint, footprint.ofEntity, hok, Set.union_subset] at hft
  replace hwε := wf_εnv_for_getAttr_implies hwε
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compile_getAttr_ok_implies hok
  subst heq
  specialize ih₁ hwε hI₁ hI₂ hsm hft.right hok₁
  clear hft
  have ⟨ty₁, ⟨hwt₁, hty₁⟩, hwo₁⟩ := compile_option_get_wf hwε hok₁
  replace ⟨t₃, rty, hok, hr⟩ := compileGetAttr_ok_implies hok
  replace ⟨hty₃, tyₐ, htyₐ, hr⟩ := hr
  have hwt₃ := (compileAttrsOf_wf hwε.left.right hwo₁.left hok).left
  have ⟨hwr, hwrty⟩ := wf_record_get hwt₃ hty₃ htyₐ
  split at hr <;> subst hr
  case' h_2 => replace ⟨hwr, hwrty⟩ := wf_term_some hwr hwrty
  all_goals {
    simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hwr hwrty ih₁
    rename_i ht₁ _
    simp only [interpret_term_some,
      compileAttrsOf_interpret_record_get_eq
        hwε.left.right hI₁ hI₂ hsm.right hwo₁.left hok hwt₃ hty₃ htyₐ
        (interpret_option_get_eq hwt₁ hty₁ ih₁ ht₁)]
  }

private theorem map_interpret_option_get_eq {ts ts' : List Term} {ty : TermType} {I₁ I₂ : Interpretation} {εs : SymEntities}
  (hwt : ∀ t ∈ ts, t.WellFormed εs)
  (hty : ∀ t ∈ ts, t.typeOf = .option ty)
  (h₁  : ∀ t ∈ ts, Term.interpret I₁ t = Term.interpret I₂ t)
  (h₂  : ts.map (Term.interpret I₂) = ts'.map Term.some) :
  ts.map (Term.interpret I₁ ∘ option.get) = ts.map (Term.interpret I₂ ∘ option.get)
:= by
  apply List.map_congr
  intro t ht
  specialize h₁ t ht
  have h₃ : t.interpret I₂ ∈ ts.map (Term.interpret I₂) := by
    simp only [List.mem_map]
    exists t
  simp only [h₂, List.mem_map] at h₃
  replace ⟨t', _, h₃⟩ := h₃
  rw [eq_comm] at h₃
  exact interpret_option_get_eq (hwt t ht) (hty t ht) h₁ h₃

private theorem compile_interpret_on_footprint_ihs {xs : List Expr} {ts : List Term} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation}
  (hwε : ∀ (x : Expr), x ∈ xs → εnv.WellFormedFor x)
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : xs.mapUnion (footprint · εnv) ⊆ ft)
  (hok : ∀ t ∈ ts, ∃ x ∈ xs, compile x εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileInterpretOnFootprint x ft εnv I₁ I₂) :
  ∀ t ∈ ts, t.interpret I₁ = t.interpret I₂
:= by
  intro t ht
  replace ⟨x, hx, hok⟩ := hok t ht
  apply ih x hx (hwε x hx) hI₁ hI₂ hsm _ hok
  exact Set.subset_trans (List.mem_implies_subset_mapUnion (footprint · εnv) hx) hft

/--
D-70 option A, step (1): `SameOn` is preserved by `extInterp`. `extInterp` only
redefines `I.vars` at the reserved `!anyall!it` entry, and every term `SameOn`
inspects — entity `attrs`/`ancestors`/`tags` (unary functions reading only
`I.funs`), the request terms (`NoAnyAllItVar`), and the footprint terms `t ∈ ft`
(also `NoAnyAllItVar`) — never reads that entry. So two interpretations that agree
on `ft` still agree after extending both with the same element binding.
-/
private theorem symEnv_sameOn_extInterp {εnv : SymEnv} {ft : Set Term} {I₁ I₂ : Interpretation} {vi : Term} {ety : TermType}
  (hwε : εnv.WellFormed)
  (hftv : ∀ t ∈ ft, t.NoAnyAllItVar = true ∧ t.NoSetAll = true)
  (hsm : εnv.SameOn ft I₁ I₂) :
  εnv.SameOn ft (extInterp I₁ vi ety) (extInterp I₂ vi ety)
:= by
  have ⟨hreq, hent⟩ := hsm
  refine ⟨?_, ?_⟩
  · -- request terms: NoAnyAllItVar ⇒ extInterp invariant on both sides
    have h₁ := symEnv_interpret_extInterp (εnv := εnv) (I := I₁) (v := vi) (ety := ety) hwε
    have h₂ := symEnv_interpret_extInterp (εnv := εnv) (I := I₂) (v := vi) (ety := ety) hwε
    have e₁ : (εnv.interpret (extInterp I₁ vi ety)).request = (εnv.interpret I₁).request := by rw [h₁]
    have e₂ : (εnv.interpret (extInterp I₂ vi ety)).request = (εnv.interpret I₂).request := by rw [h₂]
    simp only [SymEnv.interpret] at e₁ e₂
    rw [e₁, e₂]; exact hreq
  · -- entities: attrs/ancestors/tags functions and ft terms don't read I.vars
    intro ety' δ hfind
    have ⟨ha, hanc, ht⟩ := hent ety' δ hfind
    refine ⟨ha, ?_, ht⟩
    intro ancTy ancF hancfind t htft uid hintp hety
    -- t ∈ ft is NoAnyAllItVar: its interpretation is unchanged by extInterp
    have htconv : t.interpret I₁ = .some (.entity uid) := by
      have ⟨hnv, hns⟩ := hftv t htft
      rwa [interpret_extInterp_eq_of_noAnyAllItVar t hnv hns] at hintp
    -- app of the (unchanged) ancestor function
    exact hanc ancTy ancF hancfind t htft uid htconv hety

/-- `SameOn` is antitone in the footprint: shrinking `ft` keeps agreement (the only
`ft`-dependent clause, ancestor agreement, is a `∀ t ∈ ft`). -/
private theorem sameOn_subset {εnv : SymEnv} {ft ft' : Set Term} {I₁ I₂ : Interpretation}
  (hsub : ft' ⊆ ft) (hsm : εnv.SameOn ft I₁ I₂) :
  εnv.SameOn ft' I₁ I₂
:= by
  have ⟨hreq, hent⟩ := hsm
  refine ⟨hreq, ?_⟩
  intro ety δ hfind
  have ⟨ha, hanc, ht⟩ := hent ety δ hfind
  exact ⟨ha, (fun ancTy ancF hf t htft uid => hanc ancTy ancF hf t (Set.mem_subset_mem htft hsub) uid), ht⟩
private theorem compile_interpret_set_on_footprint {xs : List Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.set xs))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.set xs) εnv ⊆ ft)
  (hok : compile (.set xs) εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileInterpretOnFootprint x ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace hwε := wf_εnv_for_set_implies hwε
  simp only [footprint, List.mapUnion₁_eq_mapUnion (footprint · εnv)] at hft
  replace ⟨ts, ha, hok⟩ := compile_set_ok_implies hok
  replace ⟨ty, hd, tl, heq, hty, hok⟩ := compileSet_ok_implies hok
  subst hok
  have hwts := compile_wfs hwε ha
  replace ha := List.forall₂_implies_all_right ha
  have hwty := typeOf_option_wf_terms_is_wf heq hwts hty
  have hwo := wf_option_get_mem_of_type hwts hty
  have hws := @wf_setOf_map _ option.get _ _ hwo hwty
  replace hws := wf_term_some hws.left hws.right
  simp only [interpret_ifAllSome hI₁ hwts hws.left hws.right,
    interpret_ifAllSome hI₂ hwts hws.left hws.right]
  replace ih := compile_interpret_on_footprint_ihs hwε hI₁ hI₂ hsm hft ha ih
  simp only [List.map_congr ih]
  have hws₁ := interpret_term_wf hI₁ hws.left
  have hws₂ := interpret_term_wf hI₂ hws.left
  rw [hws.right] at hws₁ hws₂
  have hn := pe_interpret_terms_of_type_option (interpret_terms_wfls hI₂ hwts hty)
  rcases hn with ⟨_, hn⟩ | ⟨_, hs⟩
  · simp only [pe_ifAllSome_none hn hws₁.right, pe_ifAllSome_none hn hws₂.right]
  · simp only [hs, interpret_term_some, interpret_setOf, List.map_map,
      map_interpret_option_get_eq hwts hty ih hs]

private theorem map_interpret_snd_option_get_eq {ats : List (Attr × Term)} {ts : List Term} {I₁ I₂ : Interpretation} {εs : SymEntities}
  (hwt : ∀ a t, (a, t) ∈ ats → t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty)
  (h₁  : ∀ p ∈ ats, p.snd.interpret I₁ = p.snd.interpret I₂)
  (h₂  : List.map (Term.interpret I₂ ∘ Prod.snd) ats = List.map Term.some ts) :
  ats.map (Prod.map id (Term.interpret I₁ ∘ option.get)) =
  ats.map (Prod.map id (Term.interpret I₂ ∘ option.get))
:= by
  apply List.map_congr
  intro (a, t) ht
  specialize h₁ (a, t) ht
  simp only at h₁
  simp only [Prod.map, id_eq, Function.comp_apply, Prod.mk.injEq, true_and]
  have h₃ : (Term.interpret I₂ ∘ Prod.snd) (a, t) ∈ ats.map (Term.interpret I₂ ∘ Prod.snd) := by
    simp only [List.mem_map]
    exists (a, t)
  simp only [h₂, List.mem_map] at h₃
  replace ⟨t', _, h₃⟩ := h₃
  rw [eq_comm] at h₃
  replace ⟨hwt, _, hty⟩ := hwt a t ht
  exact interpret_option_get_eq hwt hty h₁ h₃

private theorem compile_interpret_record_on_footprint {axs : List (Attr × Expr)} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.record axs))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.record axs) εnv ⊆ ft)
  (hok : compile (.record axs) εnv = .ok t)
  (ih  : ∀ (a₁ : Attr) (x₁ : Expr), sizeOf (a₁, x₁).snd < 1 + sizeOf axs →
    CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint, List.mapUnion₂_eq_mapUnion (λ x : Attr × Expr => footprint x.snd εnv)] at hft
  replace hft : ∀ ax ∈ axs, footprint ax.snd εnv ⊆ ft := by
    intro x hx
    have h := List.mem_implies_subset_mapUnion (fun x : Attr × Expr => footprint x.snd εnv) hx
    exact Set.subset_trans h hft
  replace hwε := wf_εnv_for_record_implies hwε
  replace ⟨ats, ha, hok⟩ := compile_record_ok_implies hok
  subst hok
  have hwts := compile_attr_expr_wfs hwε ha
  have hwg := wf_prods_implies_wf_map_snd (wf_prods_option_implies_wf_prods hwts)
  have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd hwts)
  replace ha := List.forall₂_implies_all_right ha
  replace ih : ∀ p ∈ ats, (Term.interpret I₁ ∘ Prod.snd) p = (Term.interpret I₂ ∘ Prod.snd) p := by
    intro (a, t) ht
    have ⟨(a', x), hx, heq, hok⟩ := ha (a, t) ht
    simp only at heq hok
    subst heq
    simp only [Function.comp_apply]
    exact ih a' x (List.sizeOf_attach₂ hx) (hwε (a', x) hx) hI₁ hI₂ hsm (hft (a', x) hx) hok
  simp only [compileRecord, someOf, interpret_ifAllSome hI₁ hwg hwo hty,
    interpret_ifAllSome hI₂ hwg hwo hty, List.map_map, List.map_congr ih]
  have hwo₁ := interpret_term_wf hI₁ hwo
  have hwo₂ := interpret_term_wf hI₂ hwo
  rw [hty] at hwo₁ hwo₂
  have hwts' := interpret_attr_terms_wfls hI₂ hwts
  rcases (pe_wfls_of_type_option hwts') with ⟨_, hn⟩ | ⟨ts, hs⟩
  · simp only [pe_ifAllSome_none hn hwo₁.right, pe_ifAllSome_none hn hwo₂.right]
  · simp only [hs, interpret_term_some, interpret_recordOf, List.map_map,
      prod_map_id_comp_eq, map_interpret_snd_option_get_eq hwts ih hs]

private theorem compile_interpret_call_on_footprint {xfn : ExtFun} {xs : List Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.call xfn xs))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.call xfn xs) εnv ⊆ ft)
  (hok : compile (.call xfn xs) εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileInterpretOnFootprint x ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint, List.mapUnion₁_eq_mapUnion (footprint · εnv)] at hft
  replace hwε := wf_εnv_for_call_implies hwε
  replace ⟨ts, ha, hok⟩ := compile_call_ok_implies hok
  have hwts := compile_wfs hwε ha
  replace ha := List.forall₂_implies_all_right ha
  replace ih := compile_interpret_on_footprint_ihs hwε hI₁ hI₂ hsm hft ha ih
  have hr₁ := compileCall_interpret hI₁ hwts hok
  have hr₂ := compileCall_interpret hI₂ hwts hok
  simp only [List.map_congr ih] at hr₁
  simp only [hr₁, Except.ok.injEq] at hr₂
  exact hr₂

/--
D-70 option A, step (3): the predicate analogue of `CompileInterpretOnFootprint`.
Adds the element-term agreement `it.interpret I₁ = it.interpret I₂`, `it`
well-formedness/typing, and `NoItDependentIn p` as hypotheses — the latter guards
the one arm (`.binaryApp .mem`) whose compiled form would otherwise consult the
`it`-dependent ancestor function.
-/
private def CompilePredInterpretOnFootprint (p : PredExpr) (ft : Set Term) (εnv : SymEnv) (it : Term) (elemTy : TermType) (I₁ I₂ : Interpretation) : Prop :=
  ∀ {pt : Term},
    I₁.WellFormed εnv.entities →
    I₂.WellFormed εnv.entities →
    εnv.WellFormed →
    it.WellFormed εnv.entities →
    it.typeOf = .option elemTy →
    it.interpret I₁ = it.interpret I₂ →
    εnv.SameOn ft I₁ I₂ →
    footprintPred p it εnv ⊆ ft →
    p.NoItDependentIn = true →
    p.ValidRefs (εnv.entities.isValidEntityUID ·) →
    compilePred p it εnv = .ok pt →
    pt.interpret I₁ = pt.interpret I₂

private theorem compilePred_interpret_item_on_footprint {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term}
  (hit : it.interpret I₁ = it.interpret I₂)
  (hok : compilePred .item it εnv = .ok pt) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  simp only [compilePred, Except.ok.injEq] at hok; subst hok; exact hit

private theorem compilePred_interpret_lit_on_footprint {l : Prim} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term}
  (hok : compilePred (.lit l) it εnv = .ok pt) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  rw [compilePred_toExpr_eq (q := .lit l) (by simp only [PredExpr.mentionsIt])] at hok
  simp only [PredExpr.toExpr] at hok
  exact compile_interpret_lit_on_footprint hok

private theorem compilePred_interpret_var_on_footprint {v : Var} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term}
  (hwε : εnv.WellFormed)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hok : compilePred (.var v) it εnv = .ok pt) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  rw [compilePred_toExpr_eq (q := .var v) (by simp only [PredExpr.mentionsIt])] at hok
  simp only [PredExpr.toExpr] at hok
  exact compile_interpret_var_on_footprint ⟨hwε, Expr.ValidRefs.var_valid⟩ hsm hok

private theorem compilePred_interpret_unaryApp_on_footprint {op₁ : UnaryOp} {x₁ : PredExpr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.unaryApp op₁ x₁) it εnv ⊆ ft)
  (hok : compilePred (.unaryApp op₁ x₁) it εnv = .ok pt)
  (ih₁ : ∀ {t₁}, footprintPred x₁ it εnv ⊆ ft → compilePred x₁ it εnv = .ok t₁ → t₁.interpret I₁ = t₁.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  simp only [footprintPred] at hft
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compilePred_unaryApp_ok_implies hok
  subst heq
  have ⟨hwt₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hih := ih₁ hft hok₁
  have hwt₂ := compileApp₁_wf_types hwo₁.left hok
  have ⟨_, hty₂⟩ : ∃ ty, t₂.typeOf = .option ty := by
    split at hwt₂ <;> simp only [hwt₂, TermType.option.injEq, exists_eq']
  replace hwt₂ := hwt₂.left
  simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hwt₂ hty₂ hih
  rename_i ht₁ _
  replace hih := interpret_option_get_eq hwt₁ hty₁ hih ht₁
  have hr₁ := interpret_compileApp₁ hI₁ hwo₁.left hok
  have hr₂ := interpret_compileApp₁ hI₂ hwo₁.left hok
  simp only [hih, hr₂, Except.ok.injEq] at hr₁
  simp only [hr₁]

private theorem compilePred_interpret_hasAttr_on_footprint {x₁ : PredExpr} {a₁ : Attr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.hasAttr x₁ a₁) it εnv ⊆ ft)
  (hok : compilePred (.hasAttr x₁ a₁) it εnv = .ok pt)
  (ih₁ : ∀ {t₁}, footprintPred x₁ it εnv ⊆ ft → compilePred x₁ it εnv = .ok t₁ → t₁.interpret I₁ = t₁.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  simp only [footprintPred] at hft
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compilePred_hasAttr_ok_implies hok
  subst heq
  have ⟨hwt₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hih := ih₁ hft hok₁
  replace ⟨t₃, rty, hok, hr⟩ := compileHasAttr_ok_implies hok
  replace ⟨hty₃, hr⟩ := hr
  split at hr <;> subst hr
  case h_1 tyₐ htyₐ =>
    have hwt₃ := (compileAttrsOf_wf hwε.right hwo₁.left hok).left
    have hwr := wf_record_get hwt₃ hty₃ htyₐ
    have ⟨hws, hwsty⟩ := wf_isSome hwr.left
    replace ⟨hws, hwsty⟩ := wf_term_some hws hwsty
    simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hws hwsty hih
    rename_i ht₁ _
    simp only [interpret_term_some, interpret_isSome hI₁ hwr.left,
      interpret_isSome hI₂ hwr.left,
      compileAttrsOf_interpret_record_get_eq
        hwε.right hI₁ hI₂ hsm.right hwo₁.left hok hwt₃ hty₃ htyₐ
        (interpret_option_get_eq hwt₁ hty₁ hih ht₁)]
  case h_2 | h_3 =>
    simp only [interpret_ifSome hI₁ hwt₁ (Term.WellFormed.some_wf wf_bool),
      interpret_ifSome hI₂ hwt₁ (Term.WellFormed.some_wf wf_bool),
      hih, interpret_term_some, interpret_term_prim]

private theorem compilePred_interpret_getAttr_on_footprint {x₁ : PredExpr} {a₁ : Attr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.getAttr x₁ a₁) it εnv ⊆ ft)
  (hok : compilePred (.getAttr x₁ a₁) it εnv = .ok pt)
  (ih₁ : ∀ {t₁}, footprintPred x₁ it εnv ⊆ ft → compilePred x₁ it εnv = .ok t₁ → t₁.interpret I₁ = t₁.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  simp only [footprintPred, Set.union_subset] at hft
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compilePred_getAttr_ok_implies hok
  subst heq
  have hihsub := ih₁ hft.right hok₁
  have ⟨hwt₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hwo₁ := wf_option_get hwt₁ hty₁
  replace ⟨t₃, rty, hok, hr⟩ := compileGetAttr_ok_implies hok
  replace ⟨hty₃, tyₐ, htyₐ, hr⟩ := hr
  have hwt₃ := (compileAttrsOf_wf hwε.right hwo₁.left hok).left
  have ⟨hwr, hwrty⟩ := wf_record_get hwt₃ hty₃ htyₐ
  split at hr <;> subst hr
  case' h_2 => replace ⟨hwr, hwrty⟩ := wf_term_some hwr hwrty
  all_goals {
    simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hwr hwrty hihsub
    rename_i ht₁ _
    simp only [interpret_term_some,
      compileAttrsOf_interpret_record_get_eq
        hwε.right hI₁ hI₂ hsm.right hwo₁.left hok hwt₃ hty₃ htyₐ
        (interpret_option_get_eq hwt₁ hty₁ hihsub ht₁)]
  }

private theorem compilePred_interpret_extHasAttr_on_footprint {x₁ : PredExpr} {a₁ : Attr} {attrs : List Attr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.extHasAttr x₁ a₁ attrs) it εnv ⊆ ft)
  (hok : compilePred (.extHasAttr x₁ a₁ attrs) it εnv = .ok pt)
  (ih₁ : ∀ {t₁}, footprintPred x₁ it εnv ⊆ ft → compilePred x₁ it εnv = .ok t₁ → t₁.interpret I₁ = t₁.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  simp only [footprintPred] at hft
  simp only [compilePred] at hok
  cases hok₁ : compilePred x₁ it εnv <;> simp only [hok₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  rename_i t₁
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  have hihsub := ih₁ hft hok₁
  have ⟨hwt₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  exact compileExtHasAttrRec_interpret_eq hwε.right hI₁ hI₂ hsm.right hwt₁ ⟨ty₁, hty₁⟩ hihsub hok

private theorem compilePred_interpret_and_on_footprint {x₁ x₂ : PredExpr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.and x₁ x₂) it εnv ⊆ ft)
  (hok : compilePred (.and x₁ x₂) it εnv = .ok pt)
  (ih₁ : ∀ {t₁}, footprintPred x₁ it εnv ⊆ ft → compilePred x₁ it εnv = .ok t₁ → t₁.interpret I₁ = t₁.interpret I₂)
  (ih₂ : ∀ {t₂}, footprintPred x₂ it εnv ⊆ ft → compilePred x₂ it εnv = .ok t₂ → t₂.interpret I₁ = t₂.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  replace ⟨t₁, hok₁, h₃⟩ := compilePred_and_ok_implies hok
  split at h₃
  · subst h₃
    simp only [interpret_term_some, interpret_term_prim]
  · rename_i hf
    simp only [CompileAndSym] at h₃
    replace ⟨ht₁, t₂, hok₂, hty₂, h₃⟩ := h₃
    subst h₃
    have hbf₁ := compilePred_wf hwε hitw hitty hok₁
    have hbf₂ := compilePred_wf hwε hitw hitty hok₂
    -- split footprint on whether the condition short-circuits
    cases ht : decide (t₁ = .some (.bool true)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ht <;>
    simp only [footprintPred, footprintPred.ofBranch, hok₁] at hft
    · simp only [Set.union_subset] at hft
      have hih₁ := ih₁ hft.left.left hok₁
      have hih₂ := ih₂ hft.left.right hok₂
      have hopt := wf_option_get hbf₁.left ht₁
      exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂
        hbf₁.left hbf₂.left (Term.WellFormed.some_wf wf_bool)
        ht₁ hty₂ (by simp only [typeOf_term_some, typeOf_bool])
        hih₁ hih₂ (by simp only [interpret_term_some, interpret_term_prim])
    · subst ht
      have hih₂ := ih₂ hft hok₂
      simp only [pe_option_get_some, pe_ite_true, pe_ifSome_some hty₂, hih₂]

private theorem compilePred_interpret_or_on_footprint {x₁ x₂ : PredExpr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.or x₁ x₂) it εnv ⊆ ft)
  (hok : compilePred (.or x₁ x₂) it εnv = .ok pt)
  (ih₁ : ∀ {t₁}, footprintPred x₁ it εnv ⊆ ft → compilePred x₁ it εnv = .ok t₁ → t₁.interpret I₁ = t₁.interpret I₂)
  (ih₂ : ∀ {t₂}, footprintPred x₂ it εnv ⊆ ft → compilePred x₂ it εnv = .ok t₂ → t₂.interpret I₁ = t₂.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  replace ⟨t₁, hok₁, h₃⟩ := compilePred_or_ok_implies hok
  split at h₃
  · subst h₃
    simp only [interpret_term_some, interpret_term_prim]
  · rename_i hf
    simp only [CompileOrSym] at h₃
    replace ⟨ht₁, t₂, hok₂, hty₂, h₃⟩ := h₃
    subst h₃
    have hbf₁ := compilePred_wf hwε hitw hitty hok₁
    have hbf₂ := compilePred_wf hwε hitw hitty hok₂
    cases ht : decide (t₁ = .some (.bool false)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ht <;>
    simp only [footprintPred, footprintPred.ofBranch, hok₁] at hft
    · simp only [Set.union_subset] at hft
      have hih₁ := ih₁ hft.left.left hok₁
      have hih₂ := ih₂ hft.right hok₂
      exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂
        hbf₁.left (Term.WellFormed.some_wf wf_bool) hbf₂.left
        ht₁ (by simp only [typeOf_term_some, typeOf_bool]) hty₂
        hih₁ (by simp only [interpret_term_some, interpret_term_prim]) hih₂
    · subst ht
      have hih₂ := ih₂ hft hok₂
      simp only [pe_option_get_some, pe_ite_false, pe_ifSome_some hty₂, hih₂]

private theorem compilePred_interpret_ite_on_footprint {x₁ x₂ x₃ : PredExpr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.ite x₁ x₂ x₃) it εnv ⊆ ft)
  (hok : compilePred (.ite x₁ x₂ x₃) it εnv = .ok pt)
  (ih₁ : ∀ {t₁}, footprintPred x₁ it εnv ⊆ ft → compilePred x₁ it εnv = .ok t₁ → t₁.interpret I₁ = t₁.interpret I₂)
  (ih₂ : ∀ {t₂}, footprintPred x₂ it εnv ⊆ ft → compilePred x₂ it εnv = .ok t₂ → t₂.interpret I₁ = t₂.interpret I₂)
  (ih₃ : ∀ {t₃}, footprintPred x₃ it εnv ⊆ ft → compilePred x₃ it εnv = .ok t₃ → t₃.interpret I₁ = t₃.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  replace ⟨t₁, hok₁, h₃⟩ := compilePred_ite_ok_implies hok
  split at h₃ <;>
    simp only [footprintPred, footprintPred.ofBranch, hok₁] at hft
  · rw [eq_comm] at h₃
    exact ih₂ hft h₃
  · rw [eq_comm] at h₃
    exact ih₃ hft h₃
  · rename_i hnt hnf
    simp only [CompileIfSym] at h₃
    replace ⟨hty₁, t₂, t₃, hok₂, hok₃, hty, h₃⟩ := h₃
    subst h₃
    simp only [Set.union_subset] at hft
    have hbf₁ := compilePred_wf hwε hitw hitty hok₁
    have hbf₂ := compilePred_wf hwε hitw hitty hok₂
    have hbf₃ := compilePred_wf hwε hitw hitty hok₃
    have ⟨_, hty₂⟩ := hbf₂.2
    have hty₃ := hty₂; rw [hty] at hty₃
    exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂ hbf₁.left hbf₂.left hbf₃.left hty₁ hty₂ hty₃
      (ih₁ hft.left.left hok₁)
      (ih₂ hft.left.right hok₂)
      (ih₃ hft.right hok₃)


private theorem compilePred_interpret_binaryApp_on_footprint {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hitI : it.interpret I₁ = it.interpret I₂)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.binaryApp op₂ x₁ x₂) it εnv ⊆ ft)
  (hnoit : (PredExpr.binaryApp op₂ x₁ x₂).NoItDependentIn = true)
  (hpvr : (PredExpr.binaryApp op₂ x₁ x₂).ValidRefs (εnv.entities.isValidEntityUID ·))
  (hok : compilePred (.binaryApp op₂ x₁ x₂) it εnv = .ok pt)
  (ih₁ : ∀ {t₁}, footprintPred x₁ it εnv ⊆ ft → compilePred x₁ it εnv = .ok t₁ → t₁.interpret I₁ = t₁.interpret I₂)
  (ih₂ : ∀ {t₂}, footprintPred x₂ it εnv ⊆ ft → compilePred x₂ it εnv = .ok t₂ → t₂.interpret I₁ = t₂.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  replace ⟨t₁, t₂, t₃, hok₁, hok₂, hok, ht⟩ := compilePred_binaryApp_ok_implies hok
  subst ht
  simp only [footprintPred, Set.union_subset] at hft
  have hihsub₁ := ih₁ hft.left.right hok₁
  have hihsub₂ := ih₂ hft.right hok₂
  have ⟨hwt₁', ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hwo₁ := wf_option_get hwt₁' hty₁
  have ⟨hwt₂', ty₂, hty₂⟩ := compilePred_wf hwε hitw hitty hok₂
  have hwo₂ := wf_option_get hwt₂' hty₂
  have hwt₁ : t₁.WellFormed εnv.entities ∧ t₁.typeOf = .option ty₁ := ⟨hwt₁', hty₁⟩
  have hwt₂ : t₂.WellFormed εnv.entities ∧ t₂.typeOf = .option ty₂ := ⟨hwt₂', hty₂⟩
  have ⟨hwt₃, ty₃, hty₃⟩ := compileApp₂_wf hwε.right hwo₁.left hwo₂.left hok
  have hwt₂₃ := wf_ifSome_option hwt₂.left hwt₃ hty₃
  simp_ifSome_eq hI₁ hI₂ hwt₁.left hwt₁.right hwt₂₃.left hwt₂₃.right hihsub₁
  rename_i t₁' hlit₁ hty₁'
  simp_ifSome_eq hI₁ hI₂ hwt₂.left hwt₂.right hwt₃ hty₃ hihsub₂
  rename_i hlit₂ _
  clear hwt₃ hty₃ hwt₂₃
  have ih₁' := interpret_option_get_eq hwt₁.left hwt₁.right hihsub₁ hlit₁
  have ih₂' := interpret_option_get_eq hwt₂.left hwt₂.right hihsub₂ hlit₂
  cases op₂
  case eq =>
    rcases compileApp₂_eq_ok_implies hok with ⟨_, hok⟩ | ⟨_, hok⟩ <;> subst hok
    · simp only [interpret_term_some, interpret_eq hI₁ hwo₁.left hwo₂.left,
        interpret_eq hI₂ hwo₁.left hwo₂.left, ih₁', ih₂']
    · simp only [interpret_term_some, interpret_term_prim]
  case mem =>
    -- NoItDependentIn ⇒ left operand x₁ is it-free ⇒ its compiled term is compile x₁.toExpr εnv,
    -- whose footprint is in ft, so same_footprint_ancestors applies to x₁.toExpr.
    simp only [PredExpr.NoItDependentIn, Bool.and_eq_true, Bool.not_eq_true'] at hnoit
    have hfree₁ : x₁.mentionsIt = false := hnoit.1.1
    cases hpvr with | binaryApp_valid hvr₁ hvr₂ =>
    have hwεx₁ : εnv.WellFormedFor x₁.toExpr := ⟨hwε, PredExpr.toExpr_validRefs hvr₁⟩
    have hok₁' : compile x₁.toExpr εnv = .ok t₁ := by rw [← compilePred_toExpr_eq hfree₁]; exact hok₁
    have hftx₁ : footprint x₁.toExpr εnv ⊆ ft := by
      rw [← footprintPred_toExpr_eq hfree₁]; exact hft.left.right
    replace ⟨ety₁, ety₂, hety₁, hok⟩ := compileApp₂_mem_ok_implies hok
    have hwl₁₁ := interpret_term_wf hI₁ hwo₁.left
    have hwl₁₂ := interpret_term_wf hI₁ hwo₂.left
    have hwl₂₁ := interpret_term_wf hI₂ hwo₁.left
    have hwl₂₂ := interpret_term_wf hI₂ hwo₂.left
    rcases hok with ⟨hety₂, hok⟩ | ⟨hety₂, hok⟩
    all_goals {
      subst hok
      simp only [hwo₁.right] at hety₁
      simp only [hwo₂.right] at hety₂
      subst hety₁ hety₂
      have ⟨uid₁, heqt, heqty, heqf⟩ := same_footprint_ancestors hwεx₁ hI₁ hsm hftx₁ hok₁' hihsub₁ hlit₁ hty₁'
      subst heqt heqty
      simp only [interpret_term_some]
      try simp only [
        interpret_compileInₑ hwε.right hI₁ hwo₁.left hwo₂.left hwl₁₁ hwl₁₂ hwo₁.right hwo₂.right,
        interpret_compileInₑ hwε.right hI₂ hwo₁.left hwo₂.left hwl₂₁ hwl₂₂ hwo₁.right hwo₂.right]
      try simp only [
        interpret_compileInₛ hwε.right hI₁ hwo₁.left hwo₂.left hwl₁₁ hwl₁₂ hwo₁.right hwo₂.right,
        interpret_compileInₛ hwε.right hI₂ hwo₁.left hwo₂.left hwl₂₁ hwl₂₂ hwo₁.right hwo₂.right]
      simp only [ih₁', ih₂',
        interpret_option_get I₂ hwt₁.left hwt₁.right,
        interpret_option_get I₂ hwt₂.left hwt₂.right,
        hlit₁, hlit₂, pe_option_get'_some, compileInₑ, compileInₛ, Term.some.injEq]
      cases hancs : εnv.entities.ancestorsOfType uid₁.ty ety₂
      case none =>
        simp only [interpret_entities_ancestorsOfType_none hancs]
      case some f =>
        simp only [interpret_entities_ancestorsOfType_some hancs]
        specialize heqf ety₂ f hancs
        simp only [SymCC.compileInₑ.isIn, SymCC.compileInₛ.isIn₁, SymCC.compileInₛ.isIn₂]
        congr 2
    }
  case less =>
    rcases compileApp₂_less_ok_implies hok with ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩
    all_goals(
      subst hok
      simp only [interpret_term_some, interpret_bvslt, interpret_ext_duration_val,
        interpret_ext_datetime_val, ih₁', ih₂']
    )
  case lessEq =>
    rcases compileApp₂_lessEq_ok_implies hok with ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩
    all_goals(
      subst hok
      simp only [interpret_term_some, interpret_bvsle, interpret_ext_duration_val,
        interpret_ext_datetime_val, ih₁', ih₂']
    )
  case contains =>
    replace ⟨_, hok⟩ := compileApp₂_contains_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_member hwo₂.left hwo₁.left, ih₁', ih₂']
  case containsAll =>
    replace ⟨_, _, _, hok⟩ := compileApp₂_containsAll_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_subset hwo₂.left hwo₁.left, ih₁', ih₂']
  case containsAny =>
    replace ⟨_, hty₁, hty₂, hok⟩ := compileApp₂_containsAny_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_intersects hI₁ hwo₁.left hwo₂.left hty₁ hty₂,
      ih₁', ih₂', interpret_set_intersects hI₂ hwo₁.left hwo₂.left hty₁ hty₂]
  case add =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_add_ok_implies hok
    subst hok
    have hwa := wf_bvadd hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvsaddo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvsaddo, interpret_bvadd, ih₁', ih₂']
  case sub =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_sub_ok_implies hok
    subst hok
    have hwa := wf_bvsub hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvssubo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvssubo, interpret_bvsub, ih₁', ih₂']
  case mul =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_mul_ok_implies hok
    subst hok
    have hwa := wf_bvmul hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvsmulo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvsmulo, interpret_bvmul, ih₁', ih₂']
  case hasTag =>
    replace ⟨ety, hty₁, _, hok⟩ := compileApp₂_hasTag_ok_implies hok
    replace hok := compileHasTag_ok_implies hok
    rcases hok with ⟨_, hok⟩ | ⟨τs, hτs, hok⟩ <;> subst hok
    · simp only [interpret_term_some, interpret_term_prim]
    · simp only [interpret_term_some,
        ← interpret_hasTag (wf_εs_implies_wf_tags hwε.right hτs) hI₁ hwo₁.left hwo₂.left hty₁,
        ← interpret_hasTag (wf_εs_implies_wf_tags hwε.right hτs) hI₂ hwo₁.left hwo₂.left hty₁,
        ih₁', ih₂', Term.some.injEq]
      simp only [SymEntities.tags, Option.map_eq_some_iff] at hτs
      replace ⟨δ, hδ, hτs⟩ := hτs
      simp only [(hsm.right ety δ hδ).right.right τs hτs]
  case getTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_getTag_ok_implies hok
    replace ⟨τs, hτs, hok⟩ := compileGetTag_ok_implies hok
    subst hok
    simp only [
      ← interpret_getTag (wf_εs_implies_wf_tags hwε.right hτs) hI₁ hwo₁.left hwo₂.left hty₁ hty₂,
      ← interpret_getTag (wf_εs_implies_wf_tags hwε.right hτs) hI₂ hwo₁.left hwo₂.left hty₁ hty₂,
      ih₁', ih₂']
    simp only [SymEntities.tags, Option.map_eq_some_iff] at hτs
    replace ⟨δ, hδ, hτs⟩ := hτs
    simp only [(hsm.right ety δ hδ).right.right τs hτs]

private theorem compilePred_interpret_call_on_footprint {xfn : ExtFun} {xs : List PredExpr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.call xfn xs) it εnv ⊆ ft)
  (hok : compilePred (.call xfn xs) it εnv = .ok pt)
  (ih : ∀ x, x ∈ xs → ∀ {t}, footprintPred x it εnv ⊆ ft → compilePred x it εnv = .ok t → t.interpret I₁ = t.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  simp only [footprintPred, List.mapUnion₁_eq_mapUnion (footprintPred · it εnv)] at hft
  replace ⟨ts, ha, hok⟩ := compilePred_call_ok_implies hok
  have hwts := compilePred_wfs hwε hitw hitty ha
  replace ha := List.forall₂_implies_all_right ha
  have hih : ∀ t ∈ ts, t.interpret I₁ = t.interpret I₂ := by
    intro t ht
    replace ⟨x, hx, hxok⟩ := ha t ht
    exact ih x hx (Set.subset_trans (List.mem_implies_subset_mapUnion (footprintPred · it εnv) hx) hft) hxok
  have hr₁ := compileCall_interpret hI₁ hwts hok
  have hr₂ := compileCall_interpret hI₂ hwts hok
  simp only [List.map_congr hih] at hr₁
  simp only [hr₁, Except.ok.injEq] at hr₂
  exact hr₂

private theorem compilePred_interpret_record_on_footprint {axs : List (Attr × PredExpr)} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred (.record axs) it εnv ⊆ ft)
  (hok : compilePred (.record axs) it εnv = .ok pt)
  (ih : ∀ a x, (a, x) ∈ axs → ∀ {t}, footprintPred x it εnv ⊆ ft → compilePred x it εnv = .ok t → t.interpret I₁ = t.interpret I₂) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  simp only [footprintPred, List.mapUnion₂_eq_mapUnion (λ x : Attr × PredExpr => footprintPred x.snd it εnv)] at hft
  replace hft : ∀ ax ∈ axs, footprintPred ax.snd it εnv ⊆ ft := by
    intro x hx
    exact Set.subset_trans (List.mem_implies_subset_mapUnion (fun x : Attr × PredExpr => footprintPred x.snd it εnv) hx) hft
  replace ⟨ats, ha, hok⟩ := compilePred_record_ok_implies hok
  subst hok
  have hwts : ∀ a t, (a, t) ∈ ats → t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty := by
    intro a t hmem
    have ⟨px, hpx, heq, hp⟩ := List.forall₂_implies_all_right ha (a, t) hmem
    simp only at heq hp
    exact compilePred_wf hwε hitw hitty hp
  have hwg := wf_prods_implies_wf_map_snd (wf_prods_option_implies_wf_prods hwts)
  have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd hwts)
  replace ha := List.forall₂_implies_all_right ha
  have ihc : ∀ p ∈ ats, (Term.interpret I₁ ∘ Prod.snd) p = (Term.interpret I₂ ∘ Prod.snd) p := by
    intro (a, t) ht
    have ⟨(a', x), hx, heq, hp⟩ := ha (a, t) ht
    simp only at heq hp
    subst heq
    simp only [Function.comp_apply]
    exact ih a' x hx (hft (a', x) hx) hp
  simp only [compileRecord, someOf, interpret_ifAllSome hI₁ hwg hwo hty,
    interpret_ifAllSome hI₂ hwg hwo hty, List.map_map, List.map_congr ihc]
  have hwo₁ := interpret_term_wf hI₁ hwo
  have hwo₂ := interpret_term_wf hI₂ hwo
  rw [hty] at hwo₁ hwo₂
  have hwts' := interpret_attr_terms_wfls hI₂ hwts
  rcases (pe_wfls_of_type_option hwts') with ⟨_, hn⟩ | ⟨ts, hs⟩
  · simp only [pe_ifAllSome_none hn hwo₁.right, pe_ifAllSome_none hn hwo₂.right]
  · simp only [hs, interpret_term_some, interpret_recordOf, List.map_map,
      prod_map_id_comp_eq, map_interpret_snd_option_get_eq hwts ihc hs]

private theorem compilePred_interpret_on_footprint {p : PredExpr} {ft : Set Term} {it : Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hitI : it.interpret I₁ = it.interpret I₂)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprintPred p it εnv ⊆ ft)
  (hnoit : p.NoItDependentIn = true)
  (hpvr : p.ValidRefs (εnv.entities.isValidEntityUID ·))
  (hok : compilePred p it εnv = .ok pt) :
  pt.interpret I₁ = pt.interpret I₂
:= by
  match p, hnoit, hpvr, hft, hok with
  | .item, _, _, _, hok => exact compilePred_interpret_item_on_footprint hitI hok
  | .lit l, _, _, _, hok => exact compilePred_interpret_lit_on_footprint hok
  | .var v, _, _, _, hok => exact compilePred_interpret_var_on_footprint hwε hsm hok
  | .unaryApp op x₁, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn] at hnoit
    cases hpvr with | unaryApp_valid hv₁ =>
    exact compilePred_interpret_unaryApp_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit hv₁ h)
  | .hasAttr x₁ a, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn] at hnoit
    cases hpvr with | hasAttr_valid hv₁ =>
    exact compilePred_interpret_hasAttr_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit hv₁ h)
  | .getAttr x₁ a, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn] at hnoit
    cases hpvr with | getAttr_valid hv₁ =>
    exact compilePred_interpret_getAttr_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit hv₁ h)
  | .extHasAttr x₁ a ats, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn] at hnoit
    cases hpvr with | extHasAttr_valid hv₁ =>
    exact compilePred_interpret_extHasAttr_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit hv₁ h)
  | .ite x₁ x₂ x₃, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn, Bool.and_eq_true] at hnoit
    cases hpvr with | ite_valid hv₁ hv₂ hv₃ =>
    exact compilePred_interpret_ite_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit.1.1 hv₁ h)
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit.1.2 hv₂ h)
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit.2 hv₃ h)
  | .and x₁ x₂, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn, Bool.and_eq_true] at hnoit
    cases hpvr with | and_valid hv₁ hv₂ =>
    exact compilePred_interpret_and_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit.1 hv₁ h)
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit.2 hv₂ h)
  | .or x₁ x₂, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn, Bool.and_eq_true] at hnoit
    cases hpvr with | or_valid hv₁ hv₂ =>
    exact compilePred_interpret_or_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit.1 hv₁ h)
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs hnoit.2 hv₂ h)
  | .binaryApp op x₁ x₂, hnoit, hpvr, hft, hok =>
    have hnoit' := hnoit
    cases hpvr with | binaryApp_valid hv₁ hv₂ =>
    refine compilePred_interpret_binaryApp_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hft hnoit'
      (PredExpr.ValidRefs.binaryApp_valid hv₁ hv₂) hok
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs ?_ hv₁ h)
      (fun hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs ?_ hv₂ h)
    · cases op <;> simp_all only [PredExpr.NoItDependentIn, Bool.and_eq_true]
    · cases op <;> simp_all only [PredExpr.NoItDependentIn, Bool.and_eq_true]
  | .call f xs, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn, List.all_eq_true] at hnoit
    cases hpvr with | call_valid hv =>
    exact compilePred_interpret_call_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun x hx {t} hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs
        (by have := hnoit ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩); simpa using this)
        (hv x hx) h)
  | .record axs, hnoit, hpvr, hft, hok =>
    simp only [PredExpr.NoItDependentIn] at hnoit
    rw [List.all_attach₂_snd, List.all_eq_true] at hnoit
    cases hpvr with | record_valid hv =>
    exact compilePred_interpret_record_on_footprint hI₁ hI₂ hwε hitw hitty hsm hft hok
      (fun a x hx {t} hs h => compilePred_interpret_on_footprint hI₁ hI₂ hwε hitw hitty hitI hsm hs
        (by have := hnoit (a, x) hx; simpa using this)
        (hv (a, x) hx) h)
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have h := ‹_ ∈ _›; have := List.sizeOf_snd_lt_sizeOf_list h; omega)
      | (have h := ‹_ ∈ _›; have := List.sizeOf_lt_of_mem h; omega)

/-- Every term in `footprintPred p it εnv` is `NoAnyAllItVar` and `NoSetAll`: it is
`compile q.toExpr εnv` for an `it`-free sub-predicate `q` (`mem_footprintPred_exists`),
which (`compilePred_toExpr_eq`) is `compilePred q IT εnv` for ANY element term `IT`;
compiling against two distinct reserved-var types gives `anyAllItTyped` at both, hence
`NoAnyAllItVar` (and `NoSetAll` from the var being `NoSetAll`). -/
private theorem mem_footprintPred_noAnyAllItVar_noSetAll {p : PredExpr} {it tₑ : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormed) (hin : tₑ ∈ footprintPred p it εnv) :
  tₑ.NoAnyAllItVar = true ∧ tₑ.NoSetAll = true
:= by
  have ⟨q, hfree, _, hok⟩ := mem_footprintPred_exists hin
  -- compile q.toExpr = compilePred q IT for any IT (q it-free)
  have hbool : compilePred q (Factory.someOf (.var ⟨"!anyall!it", .bool⟩)) εnv = .ok tₑ := by
    rw [compilePred_toExpr_eq hfree]; exact hok
  have hstr : compilePred q (Factory.someOf (.var ⟨"!anyall!it", .string⟩)) εnv = .ok tₑ := by
    rw [compilePred_toExpr_eq hfree]; exact hok
  have hitb : (Factory.someOf (.var (⟨"!anyall!it", .bool⟩ : TermVar))).anyAllItTyped .bool = true := by
    simp only [Factory.someOf, Term.anyAllItTyped, reduceIte, decide_eq_true_eq]
  have hits : (Factory.someOf (.var (⟨"!anyall!it", .string⟩ : TermVar))).anyAllItTyped .string = true := by
    simp only [Factory.someOf, Term.anyAllItTyped, reduceIte, decide_eq_true_eq]
  have hitn : (Factory.someOf (.var (⟨"!anyall!it", .bool⟩ : TermVar))).NoSetAll = true := by
    simp only [Factory.someOf, Term.NoSetAll]
  have hab := compilePred_anyAllItTyped' (elemTy := .bool) hwε hitb hbool
  have has := compilePred_anyAllItTyped' (elemTy := .string) hwε hits hstr
  have hns := compilePred_noSetAll' hwε hitn hbool
  exact ⟨noAnyAllItVar_of_anyAllItTyped_ne (by decide) tₑ hab has, hns⟩

private theorem compile_interpret_all_none_on_footprint {I₁ I₂ : Interpretation} :
  (Factory.noneOf (.bool)).interpret I₁ = (Factory.noneOf (.bool)).interpret I₂
:= by
  simp only [Factory.noneOf, interpret_term_none]

/--
D-70/D-71 step (4), SYMBOLIC path: the compiled quantifier node
`set.all (option.get t₁) (option.get pt) (not (isSome pt))` interprets equally under
`I₁`/`I₂`, given the receiver `t₁` interprets equally and the predicate `pt` (compiled
against the reserved element variable) is footprint-covered. Both interpretations fold
over the SAME element list (equal receiver); each fold body is `pt` interpreted at an
`extInterp`, which agrees by step (3) + `symEnv_sameOn_extInterp`.
-/
private theorem compile_interpret_all_symbolic_on_footprint
  {p : PredExpr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t₁ pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hnoit : p.NoItDependentIn = true)
  (hpvr : p.ValidRefs (εnv.entities.isValidEntityUID ·))
  (hwt₁ : t₁.WellFormed εnv.entities) (hty₁ : t₁.typeOf = .option (.set elemTy))
  (hpt : compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv = .ok pt)
  (hpbool : (Factory.option.get pt).typeOf = .bool)
  (hih₁ : (Factory.option.get t₁).interpret I₁ = (Factory.option.get t₁).interpret I₂)
  (hpft : footprintPred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv ⊆ ft) :
  (Factory.set.all (Factory.option.get t₁) (Factory.option.get pt) (Factory.not (Factory.isSome pt))).interpret I₁
    = (Factory.set.all (Factory.option.get t₁) (Factory.option.get pt) (Factory.not (Factory.isSome pt))).interpret I₂
:= by
  have hgt := wf_option_get hwt₁ hty₁
  have hel : TermType.WellFormed εnv.entities elemTy := by
    have hw := typeOf_wf_term_is_wf hgt.left
    rw [hgt.right] at hw; cases hw with | set_wf h => exact h
  have hvarw : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).WellFormed εnv.entities :=
    Term.WellFormed.some_wf (Term.WellFormed.var_wf hel)
  have hvarty : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).typeOf = .option elemTy := by
    simp only [Factory.someOf, typeOf_term_some, typeOf_term_var, Factory.anyAllItVar]
  have hvarn : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).NoSetAll = true := by
    simp only [Factory.someOf, Term.NoSetAll]
  have hvara : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).anyAllItTyped elemTy = true := by
    simp [Factory.someOf, Term.anyAllItTyped, Factory.anyAllItVar]
  have ⟨hptw, pty, hptty⟩ := compilePred_wf hwε hvarw hvarty hpt
  have hptn := compilePred_noSetAll' hwε hvarn hpt
  have hpta := compilePred_anyAllItTyped' (elemTy := elemTy) hwε hvara hpt
  have hgp := wf_option_get hptw hptty
  rw [hpbool] at hgp
  have hgpn : (Factory.option.get pt).NoSetAll = true := noSetAll_option_get hptn
  have hgpa : (Factory.option.get pt).anyAllItTyped elemTy = true := anyAllItTyped_option_get hpta
  have hns := wf_isSome hptw
  have hnotw := wf_not hns.left hns.right
  have hnotn : (Factory.not (isSome pt)).NoSetAll = true := noSetAll_not (noSetAll_isSome hptn)
  have hnota : (Factory.not (isSome pt)).anyAllItTyped elemTy = true := anyAllItTyped_not (anyAllItTyped_isSome hpta)
  -- interpret the set.all node under each interpretation
  obtain ⟨vs₁, hSeq₁, hlit₁, hvw₁, hvty₁, hfold₁⟩ :=
    interpret_set_all_wf hI₁ hgt.left hgt.right hgp.left hpbool hgpn hgpa hnotw.left hnotw.right hnotn hnota
  obtain ⟨vs₂, hSeq₂, hlit₂, hvw₂, hvty₂, hfold₂⟩ :=
    interpret_set_all_wf hI₂ hgt.left hgt.right hgp.left hpbool hgpn hgpa hnotw.left hnotw.right hnotn hnota
  rw [hfold₁, hfold₂]
  -- equal receiver ⇒ same element list vs₁ = vs₂
  have hvseq : vs₁ = vs₂ := by
    have : Term.set (Data.Set.mk vs₁) elemTy = Term.set (Data.Set.mk vs₂) elemTy := by
      rw [← hSeq₁, ← hSeq₂, hih₁]
    simp only [Term.set.injEq, Data.Set.mk.injEq] at this; exact this.1
  subst hvseq
  -- per-element body agreement across I₁/I₂ via step (3) at extInterp
  have hsmext : ∀ vi, εnv.SameOn (footprintPred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv) (extInterp I₁ vi elemTy) (extInterp I₂ vi elemTy) :=
    fun vi => symEnv_sameOn_extInterp hwε
      (fun t ht => mem_footprintPred_noAnyAllItVar_noSetAll hwε ht)
      (sameOn_subset hpft hsm)
  have hvar_itI : ∀ vi, vi.WellFormed εnv.entities → vi.typeOf = elemTy →
      (Factory.someOf (.var (Factory.anyAllItVar elemTy))).interpret (extInterp I₁ vi elemTy)
      = (Factory.someOf (.var (Factory.anyAllItVar elemTy))).interpret (extInterp I₂ vi elemTy) := by
    intro vi _ _
    simp only [interpret_someOf_itVar_extInterp]
  -- shared per-element value function (same under both I via step 3)
  have hptI : ∀ vi ∈ vs₁, pt.interpret (extInterp I₁ vi elemTy) = pt.interpret (extInterp I₂ vi elemTy) := by
    intro vi hmem
    exact compilePred_interpret_on_footprint (I₁ := extInterp I₁ vi elemTy) (I₂ := extInterp I₂ vi elemTy)
      (extInterp_wf hI₁ ⟨hvw₁ vi hmem, hlit₁ vi hmem⟩ (hvty₁ vi hmem))
      (extInterp_wf hI₂ ⟨hvw₁ vi hmem, hlit₁ vi hmem⟩ (hvty₁ vi hmem))
      hwε hvarw hvarty (hvar_itI vi (hvw₁ vi hmem) (hvty₁ vi hmem)) (hsmext vi) Set.subset_refl hnoit hpvr hpt
  let fval : Term → Term := fun vi => pt.interpret (extInterp I₁ vi elemTy)
  -- fval vi is a WF literal of type .option .bool
  have hptybool : pty = .bool := by have := hgp.right; exact this.symm
  have hfvalwfl : ∀ vi ∈ vs₁, (fval vi).WellFormedLiteral εnv.entities ∧ (fval vi).typeOf = .option .bool := by
    intro vi hmem
    have hI' := extInterp_wf hI₁ ⟨hvw₁ vi hmem, hlit₁ vi hmem⟩ (hvty₁ vi hmem)
    have hwfl' := interpret_term_wfl hI' hptw
    rw [hptty, hptybool] at hwfl'
    exact ⟨hwfl'.left, hwfl'.right⟩
  -- each interpretation's fold equals the GOAL fold over fval
  have hfoldk : ∀ (Iₖ : Interpretation), (∀ vi ∈ vs₁, pt.interpret (extInterp Iₖ vi elemTy) = fval vi) →
      (∀ vi ∈ vs₁, (extInterp Iₖ vi elemTy).WellFormed εnv.entities) →
      Factory.ite (vs₁.foldr (fun vi acc => Factory.or (Term.interpretWith (Option.some vi) Iₖ (Factory.not (isSome pt))) acc) (false : Term))
          (Factory.noneOf .bool)
          (Factory.someOf (vs₁.foldr (fun vi acc => Factory.and (Term.interpretWith (Option.some vi) Iₖ (Factory.option.get pt)) acc) (true : Term)))
        = Factory.ite (vs₁.foldr (fun vi acc => Factory.or (Factory.not (Factory.isSome (fval vi))) acc) (false : Term))
          (Factory.noneOf .bool)
          (Factory.someOf (vs₁.foldr (fun vi acc => Factory.and (Factory.option.get (fval vi)) acc) (true : Term))) := by
    intro Iₖ hval hwIk
    refine (fold_ite_val_congr (εs := εnv.entities) (fval := fval)
      (B := fun vi => Term.interpretWith (Option.some vi) Iₖ (Factory.option.get pt))
      (BE := fun vi => Term.interpretWith (Option.some vi) Iₖ (Factory.not (isSome pt)))
      hfvalwfl ?_ ?_).symm
    · intro vi hmem
      rw [interpretWith_some_eq_interpret_ext _ hnotn hnota]
      rw [interpret_not (hwIk vi hmem) hns.left, interpret_isSome (hwIk vi hmem) hptw, hval vi hmem]
    · intro vi hmem w' hsome
      rw [interpretWith_some_eq_interpret_ext _ hgpn hgpa,
          interpret_option_get (extInterp Iₖ vi elemTy) hptw hptty, hval vi hmem]
      show Factory.option.get' (extInterp Iₖ vi elemTy) (fval vi) = w'
      rw [hsome, pe_option_get'_some]
  rw [hfoldk I₁ (fun vi _ => rfl) (fun vi hmem => extInterp_wf hI₁ ⟨hvw₁ vi hmem, hlit₁ vi hmem⟩ (hvty₁ vi hmem)),
      hfoldk I₂ (fun vi hmem => (hptI vi hmem).symm) (fun vi hmem => extInterp_wf hI₂ ⟨hvw₁ vi hmem, hlit₁ vi hmem⟩ (hvty₁ vi hmem))]

/--
D-70/D-71 step (4), LITERAL-FOLD path: a literal-set-of-literals receiver compiles
the predicate PER ELEMENT (`it := someOf vi`); the resulting `ite anyErr (noneOf .bool)
(someOf conj)` interprets equally under `I₁`/`I₂`. Each element `vi` is a literal, so
`someOf vi` is a closed term with `(someOf vi).interpret I₁ = (someOf vi).interpret I₂`
trivially, and step (3) at plain `I` (no `extInterp`) gives each per-element compiled
predicate equal interpretations; `fold_ite_val_congr` closes the two folds.
-/
private theorem compile_interpret_all_litfold_on_footprint
  {p : PredExpr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {vs : List Term} {pts : List Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hnoit : p.NoItDependentIn = true)
  (hpvr : p.ValidRefs (εnv.entities.isValidEntityUID ·))
  (hvw : ∀ vi ∈ vs, vi.WellFormed εnv.entities) (hvlit : ∀ vi ∈ vs, vi.isLiteral = true) (hvty : ∀ vi ∈ vs, vi.typeOf = elemTy)
  (hpe : ∀ vi ∈ vs, compilePred p (Factory.someOf vi) εnv = .ok ((compilePred p (Factory.someOf vi) εnv).toOption.getD vi)
          ∧ (Factory.option.get ((compilePred p (Factory.someOf vi) εnv).toOption.getD vi)).typeOf = .bool)
  (hpftv : ∀ vi ∈ vs, footprintPred p (Factory.someOf vi) εnv ⊆ ft)
  (hpts : pts = vs.map (fun vi => (compilePred p (Factory.someOf vi) εnv).toOption.getD vi)) :
  (Factory.ite (pts.foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term))
      (Factory.noneOf .bool)
      (Factory.someOf (pts.foldr (fun pti acc => Factory.and (Factory.option.get pti) acc) (true : Term)))).interpret I₁
    = (Factory.ite (pts.foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term))
      (Factory.noneOf .bool)
      (Factory.someOf (pts.foldr (fun pti acc => Factory.and (Factory.option.get pti) acc) (true : Term)))).interpret I₂
:= by
  subst hpts
  let fval : Term → Term := fun vi => (compilePred p (Factory.someOf vi) εnv).toOption.getD vi
  -- fval vi is WF of type .option .bool (from hpe + compilePred_wf)
  have hfvalw : ∀ vi ∈ vs, (fval vi).WellFormed εnv.entities ∧ (fval vi).typeOf = .option .bool := by
    intro vi hmem
    have ⟨hcpok, hbool⟩ := hpe vi hmem
    have hitw : (Factory.someOf vi).WellFormed εnv.entities := Term.WellFormed.some_wf (hvw vi hmem)
    have hitty : (Factory.someOf vi).typeOf = .option elemTy := by
      simp only [Factory.someOf, typeOf_term_some]; rw [hvty vi hmem]
    have ⟨hcpw, cty, hcpty⟩ := compilePred_wf hwε hitw hitty hcpok
    have hg := wf_option_get hcpw hcpty
    have hctybool : cty = .bool := hg.right.symm.trans hbool
    exact ⟨hcpw, by rw [hcpty, hctybool]⟩
  -- per-element: fval vi interprets equally under I₁/I₂ via step (3) at it := someOf vi (plain I)
  have hitI : ∀ vi ∈ vs, (Factory.someOf vi).interpret I₁ = (Factory.someOf vi).interpret I₂ := by
    intro vi hmem
    have hwl : (Factory.someOf vi).WellFormedLiteral εnv.entities :=
      ⟨Term.WellFormed.some_wf (hvw vi hmem), by simp only [Factory.someOf, isLiteral_some]; exact hvlit vi hmem⟩
    rw [interpret_term_lit_id I₁ hwl, interpret_term_lit_id I₂ hwl]
  have hfvalI : ∀ vi ∈ vs, (fval vi).interpret I₁ = (fval vi).interpret I₂ := by
    intro vi hmem
    have hitw : (Factory.someOf vi).WellFormed εnv.entities := Term.WellFormed.some_wf (hvw vi hmem)
    have hitty : (Factory.someOf vi).typeOf = .option elemTy := by
      simp only [Factory.someOf, typeOf_term_some]; rw [hvty vi hmem]
    have hcpeq := compilePred_interpret_on_footprint (I₁ := I₁) (I₂ := I₂)
      hI₁ hI₂ hwε hitw hitty (hitI vi hmem) hsm (hpftv vi hmem) hnoit hpvr (hpe vi hmem).1
    exact hcpeq
  -- interpreted per-element value function
  let fvalI : Term → Term := fun vi => (fval vi).interpret I₁
  have hfvalIwfl : ∀ vi ∈ vs, (fvalI vi).WellFormedLiteral εnv.entities ∧ (fvalI vi).typeOf = .option .bool := by
    intro vi hmem
    have hwfl := interpret_term_wfl hI₁ (hfvalw vi hmem).left
    rw [(hfvalw vi hmem).right] at hwfl
    exact ⟨hwfl.left, hwfl.right⟩
  -- each interpretation's fold = GOAL fold over fvalI, via interpret_foldr + fold_ite_val_congr
  have hfoldk : ∀ (Iₖ : Interpretation), Iₖ.WellFormed εnv.entities →
      (∀ vi ∈ vs, (fval vi).interpret Iₖ = fvalI vi) →
      (Factory.ite ((vs.map fval).foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term))
          (Factory.noneOf .bool)
          (Factory.someOf ((vs.map fval).foldr (fun pti acc => Factory.and (Factory.option.get pti) acc) (true : Term)))).interpret Iₖ
        = Factory.ite (vs.foldr (fun vi acc => Factory.or (Factory.not (Factory.isSome (fvalI vi))) acc) (false : Term))
          (Factory.noneOf .bool)
          (Factory.someOf (vs.foldr (fun vi acc => Factory.and (Factory.option.get (fvalI vi)) acc) (true : Term))) := by
    intro Iₖ hIk hval
    rw [List.foldr_map, List.foldr_map]
    have hwErr : ∀ vi ∈ vs, (Factory.not (Factory.isSome (fval vi))).WellFormed εnv.entities ∧ (Factory.not (Factory.isSome (fval vi))).typeOf = .bool := by
      intro vi hmem
      have hns := wf_isSome (hfvalw vi hmem).left
      have := wf_not hns.left hns.right
      exact ⟨this.left, this.right⟩
    have hwVal : ∀ vi ∈ vs, (Factory.option.get (fval vi)).WellFormed εnv.entities ∧ (Factory.option.get (fval vi)).typeOf = .bool := by
      intro vi hmem
      have hg := wf_option_get (hfvalw vi hmem).left (hfvalw vi hmem).right
      exact ⟨hg.left, hg.right⟩
    have hErrW := foldr_or_wf (εs := εnv.entities) (g := fun vi => Factory.not (Factory.isSome (fval vi))) vs hwErr
    have hValW := foldr_and_wf (εs := εnv.entities) (g := fun vi => Factory.option.get (fval vi)) vs hwVal
    have hnoneW : (Factory.noneOf (.bool)).WellFormed εnv.entities := Term.WellFormed.none_wf TermType.WellFormed.bool_wf
    have hsomeW : (Factory.someOf (vs.foldr (fun vi acc => Factory.and (Factory.option.get (fval vi)) acc) (true : Term))).WellFormed εnv.entities :=
      Term.WellFormed.some_wf hValW.left
    rw [interpret_ite hIk hErrW.left hnoneW hsomeW hErrW.right
        (by simp only [Factory.noneOf, typeOf_term_none, Factory.someOf, typeOf_term_some, hValW.right])]
    simp only [interpret_foldr_or hIk hwErr, interpret_foldr_and hIk hwVal,
        Factory.noneOf, interpret_term_none, Factory.someOf, interpret_term_some]
    -- bodies: interpret Iₖ (not (isSome (fval vi))) and interpret Iₖ (option.get (fval vi)) in terms of fvalI
    refine (fold_ite_val_congr (εs := εnv.entities) (fval := fvalI)
      (B := fun vi => Term.interpret Iₖ (Factory.option.get (fval vi)))
      (BE := fun vi => Term.interpret Iₖ (Factory.not (Factory.isSome (fval vi))))
      hfvalIwfl ?_ ?_).symm
    · intro vi hmem
      show Term.interpret Iₖ (Factory.not (Factory.isSome (fval vi))) = Factory.not (Factory.isSome (fvalI vi))
      rw [interpret_not hIk (wf_isSome (hfvalw vi hmem).left).left, interpret_isSome hIk (hfvalw vi hmem).left, hval vi hmem]
    · intro vi hmem w' hsome
      show Term.interpret Iₖ (Factory.option.get (fval vi)) = w'
      rw [interpret_option_get Iₖ (hfvalw vi hmem).left (hfvalw vi hmem).right, hval vi hmem]
      show Factory.option.get' Iₖ (fvalI vi) = w'
      rw [hsome, pe_option_get'_some]
  rw [hfoldk I₁ hI₁ (fun vi _ => rfl), hfoldk I₂ hI₂ (fun vi hmem => (hfvalI vi hmem).symm)]


/-- Decomposition of a successful `compile (.all x₁ p)`: the guard passed
(`NoItDependentIn p`), the receiver compiled (`compile x₁ εnv = .ok t₁`), and the
compiled term is one of the three D-71 shapes. Mirrors `compile_all_wf`'s splits so
the wrapper is a pure `rcases` + dispatch. -/
private theorem compile_all_ok_cases {x₁ : Expr} {p : PredExpr} {εnv : SymEnv} {t : Term}
  (hok : compile (.all x₁ p) εnv = .ok t) :
  p.NoItDependentIn = true ∧ ∃ t₁, compile x₁ εnv = .ok t₁ ∧
    ( (∃ ty, t₁ = .none ty ∧ t = Factory.noneOf .bool)
    ∨ (∃ elemTy vs pts, (∀ ty, t₁ ≠ .none ty) ∧ (Factory.option.get t₁).typeOf = .set elemTy
        ∧ Factory.option.get t₁ = .set (Data.Set.mk vs) elemTy ∧ vs.all (·.isLiteral) = true
        ∧ List.Forall₂ (λ vi pti => (do let p' ← compilePred p (Factory.someOf vi) εnv; if (Factory.option.get p').typeOf = TermType.bool then Except.ok p' else Except.error SymCC.Error.typeError) = Except.ok pti) vs pts
        ∧ t = Factory.ifSome t₁ (Factory.ite (pts.foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term))
            (Factory.noneOf .bool) (Factory.someOf (pts.foldr (fun pti acc => Factory.and (Factory.option.get pti) acc) (true : Term)))))
    ∨ (∃ elemTy pt, (∀ ty, t₁ ≠ .none ty) ∧ (Factory.option.get t₁).typeOf = .set elemTy
        ∧ (∀ vs ety, Factory.option.get t₁ = .set (Data.Set.mk vs) ety → vs.all (·.isLiteral) = false)
        ∧ compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv = .ok pt
        ∧ (Factory.option.get pt).typeOf = .bool
        ∧ t = Factory.ifSome t₁ (Factory.set.all (Factory.option.get t₁) (Factory.option.get pt) (Factory.not (Factory.isSome pt)))) )
:= by
  have hnoit : p.NoItDependentIn = true := by
    by_contra hc; rw [Bool.not_eq_true] at hc
    rw [compile.eq_def] at hok
    simp only [hc, not_false_eq_true, if_true, reduceCtorEq] at hok
  refine ⟨hnoit, ?_⟩
  rw [compile.eq_def] at hok
  simp only [hnoit, not_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true, reduceIte] at hok
  simp_do_let (compile x₁ εnv) at hok
  rename_i t₁ hr₁
  refine ⟨t₁, (by first | exact hr₁ | rfl), ?_⟩
  have hnn : (∃ ty, t₁ = Term.none ty) ∨ (∀ ty, t₁ ≠ Term.none ty) := by
    cases t₁ <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (fun _ h => nomatch h)
  rcases hnn with ⟨ty, rfl⟩ | hnotnone'
  · simp only [] at hok
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    -- `split` on `match ty` substituted `ty := .set _`, so the witness must be inferred.
    exact Or.inl ⟨_, rfl, hok.symm⟩
  · -- eliminate the outer `match t₁` using `hnotnone'`
    split at hok
    · first
        | exact absurd rfl (hnotnone' _)
        | exact absurd ‹_ = Term.none _› (hnotnone' _)
        | (rename_i heq; exact absurd heq (hnotnone' _))
    try simp only [] at hok
    split at hok
    · rename_i elemTy helemq
      split at hok
      · rename_i vs ety' hvseq
        have htyeq : ety' = elemTy := by
          rw [hvseq] at helemq; simp only [Term.typeOf, TermType.set.injEq] at helemq
          first | exact helemq | exact helemq.symm
        subst ety'
        split at hok
        · rename_i hlit
          simp_do_let (vs.mapM (fun vi => do
            let pti ← compilePred p (Factory.someOf vi) εnv
            if (Factory.option.get pti).typeOf = TermType.bool then Except.ok pti else Except.error SymCC.Error.typeError)) at hok
          rename_i pts hpts
          simp only [Except.ok.injEq] at hok; subst hok
          exact Or.inr (Or.inl ⟨elemTy, vs, pts, hnotnone', helemq, hvseq, hlit, (List.mapM_ok_iff_forall₂).mp hpts, rfl⟩)
        · rename_i hlit
          simp_do_let (compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv) at hok
          rename_i pt hpt
          split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
          rename_i hpbool; subst hok
          exact Or.inr (Or.inr ⟨elemTy, pt, hnotnone', helemq, (by
            intro vs' ety' heq; rw [hvseq] at heq
            simp only [Term.set.injEq, Data.Set.mk.injEq] at heq
            obtain ⟨rfl, _⟩ := heq; exact Bool.eq_false_iff.mpr hlit), hpt, hpbool, rfl⟩)
      · rename_i hnotset
        simp_do_let (compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv) at hok
        rename_i pt hpt
        split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
        rename_i hpbool; subst hok
        exact Or.inr (Or.inr ⟨elemTy, pt, hnotnone', helemq, (by
          intro vs' ety' heq; exact absurd heq (hnotset vs' ety')), hpt, hpbool, rfl⟩)
    · simp only [reduceCtorEq] at hok

/-- SYMBOLIC leaf: the inner `set.all` interprets equally; wraps `_symbolic` + the
receiver `.some`-witness lift (`interpret_option_get_eq`). -/
private theorem compile_interpret_all_symbolic_leaf
  {p : PredExpr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t₁ pt : Term} {elemTy : TermType}
  (hI₁ : I₁.WellFormed εnv.entities) (hI₂ : I₂.WellFormed εnv.entities) (hwε : εnv.WellFormed)
  (hsm : εnv.SameOn ft I₁ I₂) (hnoit : p.NoItDependentIn = true)
  (hpvr : p.ValidRefs (εnv.entities.isValidEntityUID ·))
  (hwt₁ : t₁.WellFormed εnv.entities) (hty₁ : t₁.typeOf = .option (.set elemTy))
  (hpt : compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv = .ok pt)
  (hpbool : (Factory.option.get pt).typeOf = .bool)
  (hih₁ : t₁.interpret I₁ = t₁.interpret I₂)
  (hpft : footprintPred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv ⊆ ft)
  (w : Term) (hsome : t₁.interpret I₂ = .some w) :
  (Factory.set.all (Factory.option.get t₁) (Factory.option.get pt) (Factory.not (Factory.isSome pt))).interpret I₁
    = (Factory.set.all (Factory.option.get t₁) (Factory.option.get pt) (Factory.not (Factory.isSome pt))).interpret I₂
:= compile_interpret_all_symbolic_on_footprint hI₁ hI₂ hwε hsm hnoit hpvr hwt₁ hty₁ hpt hpbool
    (interpret_option_get_eq hwt₁ hty₁ hih₁ hsome) hpft

/-- The `.all` case of `compile_interpret_on_footprint` (D-70 option A): decompose the compiled
`.all` term along the compiler's three paths (`compile_all_ok_cases`) and dispatch each to its
path lemma, with footprint coverage from the matching `footprintAllPred_*_eq` slot (D-71). -/
private theorem compile_interpret_all_on_footprint {x₁ : Expr} {p : PredExpr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.all x₁ p))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.all x₁ p) εnv ⊆ ft)
  (hok : compile (.all x₁ p) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  have hwφ₁ : εnv.WellFormedFor x₁ := by
    refine ⟨hwε.left, ?_⟩
    have hv := hwε.right
    cases hv with | all_valid hvx _ => exact hvx
  have hpvr : p.ValidRefs (εnv.entities.isValidEntityUID ·) := by
    have hv := hwε.right
    cases hv with | all_valid _ hp => exact hp
  have hwe : εnv.WellFormed := hwε.left
  simp only [footprint, Set.union_subset] at hft
  obtain ⟨hnoit, t₁, hr₁, hc⟩ := compile_all_ok_cases hok
  have ⟨hwt₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hr₁
  have hih₁ : t₁.interpret I₁ = t₁.interpret I₂ := ih₁ hwφ₁ hI₁ hI₂ hsm hft.left hr₁
  have hgt := wf_option_get hwt₁ hty₁
  rcases hc with ⟨ty, hteq, rfl⟩ | ⟨elemTy, vs, pts, hnn, helemq, hget, hlit, hpts, rfl⟩ | ⟨elemTy, pt, hnn, helemq, hnotlit, hpt, hpbool, rfl⟩
  · exact compile_interpret_all_none_on_footprint
  · -- literal-fold path (D-68)
    have hty₁' : t₁.typeOf = .option (.set elemTy) := by rw [hty₁, ← hgt.right, helemq]
    -- the receiver is syntactically `.some u` (option.get of a non-`.some` option-typed term is an app)
    have hsome : ∃ u, t₁ = .some u := by
      cases t₁ <;> first
        | exact ⟨_, rfl⟩
        | (simp only [Factory.option.get, hty₁', reduceCtorEq] at hget)
    -- footprint slot ⇒ per-element predicate footprints are covered
    have hslot := footprintAllPred_litfold_eq (p := p) hr₁ hsome hget hlit
    rw [hslot] at hft
    have hpftv : ∀ vi ∈ vs, footprintPred p (Factory.someOf vi) εnv ⊆ ft := by
      intro vi hmem
      exact Set.subset_trans (List.mem_implies_subset_mapUnion (fun vi => footprintPred p (Factory.someOf vi) εnv) hmem) hft.right
    -- element facts from set-WF of (option.get t₁)
    have hsetw := hgt.left
    rw [hget] at hsetw
    have helts : ∀ vi ∈ vs, vi.WellFormed εnv.entities ∧ vi.typeOf = elemTy := by
      cases hsetw with | set_wf h₁ h₂ _ _ =>
      intro vi hmem; exact ⟨h₁ vi hmem, by rw [h₂ vi hmem]⟩
    have hvlit : ∀ vi ∈ vs, vi.isLiteral = true := by
      simp only [List.all_eq_true] at hlit; exact hlit
    -- pts = vs.map fval and per-element compile facts (as in compile_interpret_all)
    let fval : Term → Term := fun vi => (compilePred p (Factory.someOf vi) εnv).toOption.getD vi
    have hfe : ∀ vi, fval vi = (compilePred p (Factory.someOf vi) εnv).toOption.getD vi := fun _ => rfl
    have hrel : ∀ {vi pti}, (do
        let pti' ← compilePred p (Factory.someOf vi) εnv
        if (Factory.option.get pti').typeOf = TermType.bool then Except.ok pti' else Except.error SymCC.Error.typeError) = Except.ok pti →
        pti = fval vi := by
      intro vi pti hpti
      cases hcp : compilePred p (Factory.someOf vi) εnv <;>
        simp only [hcp, Except.bind_err, Except.bind_ok, reduceCtorEq] at hpti
      rename_i cpt
      split at hpti <;> simp only [Except.ok.injEq, reduceCtorEq] at hpti
      rw [← hpti, hfe, hcp]; rfl
    have hpe : ∀ vi ∈ vs, compilePred p (Factory.someOf vi) εnv = .ok (fval vi)
        ∧ (Factory.option.get (fval vi)).typeOf = .bool := by
      intro vi hmem
      obtain ⟨pti, _, hpti⟩ := List.forall₂_implies_all_left hpts vi hmem
      show compilePred p (Factory.someOf vi) εnv = .ok ((compilePred p (Factory.someOf vi) εnv).toOption.getD vi)
        ∧ (Factory.option.get ((compilePred p (Factory.someOf vi) εnv).toOption.getD vi)).typeOf = .bool
      cases hcp : compilePred p (Factory.someOf vi) εnv <;>
        simp only [hcp, Except.bind_err, Except.bind_ok, reduceCtorEq] at hpti ⊢
      rename_i cpt
      split at hpti <;> simp only [Except.ok.injEq, reduceCtorEq] at hpti
      rename_i hbool
      exact ⟨rfl, hbool⟩
    have hptsmap : pts = vs.map fval := by
      have hgen : ∀ (vs pts : List Term), List.Forall₂ (λ vi pti => (do
          let p' ← compilePred p (Factory.someOf vi) εnv
          if (Factory.option.get p').typeOf = TermType.bool then Except.ok p' else Except.error SymCC.Error.typeError) = Except.ok pti) vs pts →
          pts = vs.map fval := by
        intro vs pts h
        induction h with
        | nil => rfl
        | cons hr _htl ih =>
          simp only [List.map_cons]
          rw [hrel hr, ih]
      exact hgen vs pts hpts
    -- WF of the inner fold term, for interpret_ifSome
    have hptsw : ∀ pti ∈ pts, pti.WellFormed εnv.entities ∧ pti.typeOf = .option .bool := by
      intro pti hmem
      rw [hptsmap, List.mem_map] at hmem
      obtain ⟨vi, hvi, rfl⟩ := hmem
      have ⟨hcpok, hbool⟩ := hpe vi hvi
      have ⟨hcpw, cty, hcpty⟩ := compilePred_wf hwe
        (Term.WellFormed.some_wf (helts vi hvi).left)
        (by simp only [Factory.someOf, typeOf_term_some]; rw [(helts vi hvi).right]) hcpok
      have hg := wf_option_get hcpw hcpty
      refine ⟨hcpw, ?_⟩
      rw [hcpty]; rw [hg.right] at hbool; rw [hbool]
    have hinner := compile_all_fold_inner_wf (εs := εnv.entities) hptsw
    rw [interpret_ifSome hI₁ hwt₁ hinner.left, interpret_ifSome hI₂ hwt₁ hinner.left, hih₁]
    congr 1
    exact compile_interpret_all_litfold_on_footprint hI₁ hI₂ hwe hsm hnoit hpvr
      (fun vi h => (helts vi h).left) hvlit (fun vi h => (helts vi h).right) hpe hpftv hptsmap
  · -- symbolic path (D-52 encoding)
    have hty₁' : t₁.typeOf = .option (.set elemTy) := by rw [hty₁, ← hgt.right, helemq]
    have hslot := footprintAllPred_symbolic_eq (p := p) hr₁ hnn helemq hnotlit
    rw [hslot] at hft
    have hinner := compile_all_symbolic_inner_wf hwe hwt₁ hty₁' hpt hpbool
    rw [interpret_ifSome hI₁ hwt₁ hinner.left, interpret_ifSome hI₂ hwt₁ hinner.left, hih₁]
    -- the receiver interprets to a literal option: `.none` makes both sides `none`; `.some w` uses the leaf
    have hwl₂ := interpret_term_wfl hI₂ hwt₁
    rw [hty₁'] at hwl₂
    rcases wfl_of_type_option_is_option hwl₂.left hwl₂.right with hnone | ⟨w, hsomew, _⟩
    · have hwt₁₂ := interpret_term_wf hI₁ hinner.left
      have hwt₂₂ := interpret_term_wf hI₂ hinner.left
      rw [hinner.right] at hwt₁₂ hwt₂₂
      rw [hnone]
      simp only [pe_ifSome_none hwt₁₂.right, pe_ifSome_none hwt₂₂.right]
    · rw [hsomew]
      congr 1
      exact compile_interpret_all_symbolic_leaf hI₁ hI₂ hwe hsm hnoit hpvr hwt₁ hty₁' hpt hpbool hih₁ hft.right w hsomew

theorem compile_interpret_on_footprint {x : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor x)
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint x εnv ⊆ ft)
  (hok : compile x εnv = .ok t) :
  t.interpret I₁ = t.interpret I₂
:= by
  induction x using compile.induct generalizing t
  case case1 =>
    exact compile_interpret_lit_on_footprint hok
  case case2 =>
    exact compile_interpret_var_on_footprint hwε hsm hok
  case case3 ih₁ ih₂ ih₃ =>
    exact compile_interpret_ite_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε) (λ hwε _ _ _ => ih₂ hwε) (λ hwε _ _ _ => ih₃ hwε)
  case case4 ih₁ ih₂ =>
    exact compile_interpret_and_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε) (λ hwε _ _ _ => ih₂ hwε)
  case case5 ih₁ ih₂ =>
    exact compile_interpret_or_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε) (λ hwε _ _ _ => ih₂ hwε)
  case case6 ih₁ =>
    exact compile_interpret_unaryApp_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε)
  case case7 ih₁ ih₂ =>
    exact compile_interpret_binaryApp_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε) (λ hwε _ _ _ => ih₂ hwε)
  case case8 ih₁ =>
    exact compile_interpret_hasAttr_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε)
  case case9 ih₁ =>
    exact compile_interpret_extHasAttr_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε)
  case case10 ih₁ =>
    exact compile_interpret_getAttr_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε)
  case case11 ih =>
    exact compile_interpret_set_on_footprint hwε hI₁ hI₂ hsm hft hok (λ x₁ hmem _ hwε _ _ _ => ih x₁ hmem hwε)
  case case12 ih =>
    exact compile_interpret_record_on_footprint hwε hI₁ hI₂ hsm hft hok (λ a₁ x₁ hsizeOf t hwε _ _ _ => ih a₁ x₁ hsizeOf hwε)
  case case13 ih =>
    exact compile_interpret_call_on_footprint hwε hI₁ hI₂ hsm hft hok (λ x₁ hmem _ hwε _ _ _ => ih x₁ hmem hwε)
  case case14 =>
    -- guard-error: ¬ NoItDependentIn p ⇒ compile .all = .error, contradicts hok
    rename_i x₁ p hc
    rw [compile.eq_def] at hok
    simp only [hc, not_false_eq_true, ite_true, reduceCtorEq, reduceIte] at hok
  case case15 ih =>
    exact compile_interpret_all_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih hwε)

end Cedar.Thm
