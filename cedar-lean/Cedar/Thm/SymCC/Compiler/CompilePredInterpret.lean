/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.SymCC
import Cedar.Thm.SymCC.Compiler.LitVar
import Cedar.Thm.SymCC.Compiler.Unary
import Cedar.Thm.SymCC.Compiler.Binary
import Cedar.Thm.SymCC.Compiler.Attr
import Cedar.Thm.SymCC.Compiler.Control
import Cedar.Thm.SymCC.Compiler.Record
import Cedar.Thm.SymCC.Compiler.Call
import Cedar.Thm.SymCC.Compiler.ExtHasAttr
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Env.Interpret
import Cedar.Thm.Data.List
import Cedar.Thm.Tactics

/-! Per-arm `compilePred`/`interpret` commutation lemmas (M3). Each mirrors the corresponding
`compile_interpret_*` arm helper, taking the inductive hypothesis as an explicit premise; the final
`compilePred_interpret` dispatches over them. -/

namespace Cedar.Thm

open Spec SymCC Factory

theorem compilePred_interpret_unaryApp {op₁ : UnaryOp} {x₁ : PredExpr} {it : Term} {εnv : SymEnv}
    {I : Interpretation} {pt : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.unaryApp op₁ x₁) it εnv = .ok pt)
    (ih₁ : ∀ {t₁}, compilePred x₁ it εnv = .ok t₁ →
            compilePred x₁ (it.interpret I) (εnv.interpret I) = .ok (t₁.interpret I)) :
    compilePred (.unaryApp op₁ x₁) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  simp only [compilePred] at hok ⊢
  cases h1 : compilePred x₁ it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  rename_i t₁
  cases ha : compileApp₁ op₁ (option.get t₁) <;> simp only [ha, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  simp only [Except.ok.injEq] at hok; subst hok
  have ⟨hwφ₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty h1
  have hwo := wf_option_get hwφ₁ hty₁
  have hwφ₁' := interpret_term_wfl hI hwφ₁
  rw [hty₁] at hwφ₁'
  have hwo' := wf_option_get hwφ₁'.left.left hwφ₁'.right
  rw [eq_comm, ← hwo.right] at hwo'
  simp only [ih₁ h1, Except.bind_ok]
  have hi := interpret_compileApp₁ hI hwo.left ha
  simp_do_let (compileApp₁ op₁ (option.get (Term.interpret I t₁))) <;>
  rename_i heq
  case error =>
    have ⟨_, hok'⟩ := compileApp₁_ok_typeOf hwo'.right ha
    simp only [heq, reduceCtorEq] at hok'
  case ok t₃ =>
    have ⟨hwφ₂, ty₂, hty₂⟩ := compileApp₁_wf hwo.left ha
    simp only [interpret_ifSome hI hwφ₁ hwφ₂, Except.ok.injEq]
    rw [interpret_option_get I hwφ₁ hty₁] at hi
    have hty₃ := compileApp₁_ok_typeOf_eq hwo.left hwo'.left ha heq
    rw [eq_comm, hty₂] at hty₃
    rw [← (interpret_term_wf hI hwφ₂).right] at hty₂
    exact pe_ifSome_ok_get_eq_get' I (compileApp₁ op₁) hwφ₁' hty₂ hty₃ hi heq

theorem compilePred_interpret_item {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term}
    (hok : compilePred .item it εnv = .ok pt) :
    compilePred .item (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  simp only [compilePred, Except.ok.injEq] at hok; subst hok; simp only [compilePred]

theorem compilePred_interpret_lit {l : Prim} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term}
    (hok : compilePred (.lit l) it εnv = .ok pt) :
    compilePred (.lit l) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  simp only [compilePred] at hok ⊢
  have h := compile_interpret_lit (p := l) (εnv := εnv) (I := I) (t := pt) (by rw [compile.eq_def]; simpa [compilePrim] using hok)
  rw [compile.eq_def] at h; simpa [compilePrim] using h

theorem compilePred_interpret_var {v : Var} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hok : compilePred (.var v) it εnv = .ok pt) :
    compilePred (.var v) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  simp only [compilePred] at hok ⊢
  have h := compile_interpret_var (v := v) (εnv := εnv) (I := I) (t := pt) hI ⟨hwε, Expr.ValidRefs.var_valid⟩ (by rw [compile.eq_def]; simpa [compileVar] using hok)
  rw [compile.eq_def] at h; simpa [compileVar] using h

theorem compilePred_interpret_hasAttr {x₁ : PredExpr} {a : Attr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.hasAttr x₁ a) it εnv = .ok pt)
    (ih₁ : ∀ {t₁}, compilePred x₁ it εnv = .ok t₁ →
            compilePred x₁ (it.interpret I) (εnv.interpret I) = .ok (t₁.interpret I)) :
    compilePred (.hasAttr x₁ a) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  have hwε' := interpret_εntities_wf hwε.right hI
  simp only [compilePred] at hok ⊢
  cases h1 : compilePred x₁ it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  rename_i t₂
  cases ha : compileHasAttr (option.get t₂) a εnv.entities <;> simp only [ha, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  simp only [Except.ok.injEq] at hok; subst hok
  have ⟨hwφ₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty h1
  have hwo := wf_option_get hwφ₁ hty₁
  have hi := interpret_compileHasAttr hwε.right hI hwo.left ha
  simp only [ih₁ h1, Except.bind_ok]
  simp_do_let (compileHasAttr (option.get (Term.interpret I t₂)) a (SymEnv.interpret I εnv).entities) <;>
  rename_i heq <;>
  simp only [SymEnv.interpret] at heq
  case error =>
    have ⟨_, hok'⟩ := compileHasAttr_interpret_ok hI hwε.right hwφ₁ hty₁ hi
    simp only [hok', reduceCtorEq] at heq
  case ok t₄ =>
    have ⟨hwφ₃, hty₃⟩ := compileHasAttr_wf hwε.right hwo.left ha
    simp only [interpret_ifSome hI hwφ₁ hwφ₃, Except.ok.injEq]
    rw [interpret_option_get I hwφ₁ hty₁] at hi
    have hwφ₂ := interpret_term_wfl hI hwφ₁ ; rw [hty₁] at hwφ₂
    have hty₄ : Term.typeOf t₄ = TermType.option TermType.bool := by
      have hwo' := wf_option_get hwφ₂.left.left hwφ₂.right
      have hwφ₄ := wf_term_same_domain (interpret_entities_same_domain εnv.entities I) hwo'.left
      exact (compileHasAttr_wf hwε' hwφ₄ heq).right
    rw [← (interpret_term_wf hI hwφ₃).right] at hty₃
    exact pe_ifSome_ok_get_eq_get' I (compileHasAttr · a (SymEntities.interpret I εnv.entities)) hwφ₂ hty₃ hty₄ hi heq

end Cedar.Thm
