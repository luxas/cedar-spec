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
import Cedar.Thm.SymCC.Compiler.Invert
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

theorem compilePred_interpret_getAttr {x₁ : PredExpr} {a : Attr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.getAttr x₁ a) it εnv = .ok pt)
    (ih₁ : ∀ {t₁}, compilePred x₁ it εnv = .ok t₁ →
            compilePred x₁ (it.interpret I) (εnv.interpret I) = .ok (t₁.interpret I)) :
    compilePred (.getAttr x₁ a) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  have hwε' := interpret_εntities_wf hwε.right hI
  simp only [compilePred] at hok ⊢
  cases h1 : compilePred x₁ it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  rename_i t₂
  cases ha : compileGetAttr (option.get t₂) a εnv.entities <;> simp only [ha, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  simp only [Except.ok.injEq] at hok; subst hok
  have ⟨hwφ₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty h1
  have hwo := wf_option_get hwφ₁ hty₁
  have hi := interpret_compileGetAttr hwε.right hI hwo.left ha
  simp only [ih₁ h1, Except.bind_ok]
  simp_do_let (compileGetAttr (option.get (Term.interpret I t₂)) a (SymEnv.interpret I εnv).entities) <;>
  rename_i heq <;>
  simp only [SymEnv.interpret] at heq
  case error =>
    have ⟨_, hok'⟩ := compileGetAttr_interpret_ok hI hwε.right hwφ₁ hty₁ hi
    simp only [hok', reduceCtorEq] at heq
  case ok t₄ =>
    have ⟨hwφ₂, tyₐ, hty₂⟩ := compileGetAttr_wf hwε.right hwo.left ha
    simp only [interpret_ifSome hI hwφ₁ hwφ₂, Except.ok.injEq]
    rw [interpret_option_get I hwφ₁ hty₁] at hi
    have hwφ₃  := interpret_term_wfl hI hwφ₁ ; rw [hty₁] at hwφ₃
    have hty₄ : t₄.typeOf = .option tyₐ := by
      have hwo'  := wf_option_get hwφ₃.left.left hwφ₃.right
      have hwo'' := wf_option_get' hI hwφ₃.left.left hwφ₃.right
      have hwφ₄  := wf_term_same_domain (interpret_entities_same_domain εnv.entities I) hwo'.left
      have hwφ₄' := wf_term_same_domain (interpret_entities_same_domain εnv.entities I) hwo''.left
      have h := compileGetAttr_ok_typeOf_eq hwε' hwφ₄' hwφ₄ (by simp only [hwo''.right, hwo'.right]) hi heq
      simp only [interpret_term_wf hI hwφ₂] at h
      simp only [h, hty₂]
    rw [← (interpret_term_wf hI hwφ₂).right] at hty₂
    exact pe_ifSome_ok_get_eq_get' I (compileGetAttr · a (SymEntities.interpret I εnv.entities)) hwφ₃ hty₂ hty₄ hi heq

theorem compilePred_interpret_binaryApp {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.binaryApp op₂ x₁ x₂) it εnv = .ok pt)
    (ih₁ : ∀ {t₁}, compilePred x₁ it εnv = .ok t₁ →
            compilePred x₁ (it.interpret I) (εnv.interpret I) = .ok (t₁.interpret I))
    (ih₂ : ∀ {t₂}, compilePred x₂ it εnv = .ok t₂ →
            compilePred x₂ (it.interpret I) (εnv.interpret I) = .ok (t₂.interpret I)) :
    compilePred (.binaryApp op₂ x₁ x₂) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  simp only [compilePred] at hok ⊢
  cases hok₁ : compilePred x₁ it εnv <;> simp only [hok₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  cases hok₂ : compilePred x₂ it εnv <;> simp only [hok₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  rename_i t₁ t₂
  cases hcA : compileApp₂ op₂ (option.get t₁) (option.get t₂) εnv.entities <;> simp only [hcA, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  simp only [Except.ok.injEq] at hok; subst hok
  have ⟨hwφ₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hwo₁ := wf_option_get hwφ₁ hty₁
  have hwφ₁' := interpret_term_wfl hI hwφ₁ ; rw [hty₁] at hwφ₁'
  have hwo₁' := wf_option_get hwφ₁'.left.left hwφ₁'.right
  rw [eq_comm, ← hwo₁.right] at hwo₁'
  have ⟨hwφ₂, ty₂, hty₂⟩ := compilePred_wf hwε hitw hitty hok₂
  have hwo₂ := wf_option_get hwφ₂ hty₂
  have hwφ₂' := interpret_term_wfl hI hwφ₂ ; rw [hty₂] at hwφ₂'
  have hwo₂' := wf_option_get hwφ₂'.left.left hwφ₂'.right
  rw [eq_comm, ← hwo₂.right] at hwo₂'
  simp only [ih₁ hok₁, ih₂ hok₂, Except.bind_ok]
  have hi := interpret_compileApp₂ hwε.right hI hwo₁.left hwo₂.left hcA
  simp_do_let (compileApp₂ op₂ (option.get (Term.interpret I t₁)) (option.get (Term.interpret I t₂)) (SymEnv.interpret I εnv).entities) <;>
  rename_i heq
  case error =>
    simp only [SymEnv.interpret] at heq
    have ⟨_, hok'⟩ := compileApp₂_ok_typeOf I hwo₁'.right hwo₂'.right hcA
    simp only [heq, reduceCtorEq] at hok'
  case ok t₄ =>
    simp only [SymEnv.interpret] at heq
    have ⟨hwφ₃, ty₃, hty₃⟩ := compileApp₂_wf hwε.right hwo₁.left hwo₂.left hcA
    have hwφ₄ := wf_ifSome_option hwφ₂ hwφ₃ hty₃
    simp only [interpret_ifSome hI hwφ₁ hwφ₄.left, interpret_ifSome hI hwφ₂ hwφ₃, Except.ok.injEq]
    rw [interpret_option_get I hwφ₁ hty₁, interpret_option_get I hwφ₂ hty₂] at hi
    have hty₄ : Term.typeOf t₄ = TermType.option ty₃ := by
      rw [← hty₃, ← (interpret_term_wf hI hwφ₃).right]
      have hdom := interpret_entities_same_domain εnv.entities I
      have hty₅ : (option.get' I (Term.interpret I t₁)).typeOf = (option.get (Term.interpret I t₁)).typeOf := by
        simp only [wf_option_get' hI hwφ₁'.left.left hwφ₁'.right, ← hwo₁.right, ← hwo₁'.right]
      exact compileApp₂_ok_typeOf_eq (interpret_εntities_wf hwε.right hI)
        (wf_term_same_domain hdom (wf_option_get' hI hwφ₁'.left.left hwφ₁'.right).left)
        (wf_term_same_domain hdom (wf_option_get' hI hwφ₂'.left.left hwφ₂'.right).left)
        (wf_term_same_domain hdom hwo₁'.left)
        (wf_term_same_domain hdom hwo₂'.left)
        hty₅ hi heq
    rw [← (interpret_term_wf hI hwφ₃).right] at hty₃
    exact pe_ifSome_ok_get_eq_get'₂ I (compileApp₂ op₂ · · (SymEntities.interpret I εnv.entities)) hwφ₁' hwφ₂' hty₃ hty₄ hi heq

theorem compilePred_and_ok_implies {x₁ x₂ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
  (h₁ : compilePred (.and x₁ x₂) it εnv = .ok t) :
  ∃ t₁,
    (compilePred x₁ it εnv) = .ok t₁ ∧
    match t₁ with
     | .some (.prim (.bool false)) => t = t₁
     | _ => CompileAndSym t t₁ (compilePred x₂ it εnv)
:= by
  rw [compilePred.eq_def] at h₁
  simp_do_let (compilePred x₁ it εnv) at h₁ ; rename_i t₁ h₂
  exists t₁
  simp only [true_and, CompileAndSym]
  simp only [compileAnd] at h₁
  split at h₁
  case h_1 =>
    simp only [Except.ok.injEq] at *
    simp only [h₁]
  case h_2 h₃ h₄ =>
    simp_do_let (compilePred x₂ it εnv) at h₁ ; rename_i t₂ h₅
    split
    case h_1 => simp only [forall_const] at h₃
    case h_2 =>
      simp only [h₄, Except.ok.injEq, exists_eq_left', true_and]
      split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
      subst t
      simp [*, someOf]
  case h_3 => simp only [reduceCtorEq] at h₁

theorem compilePred_or_ok_implies {x₁ x₂ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
  (h₁ : compilePred (.or x₁ x₂) it εnv = .ok t) :
  ∃ t₁,
    (compilePred x₁ it εnv) = .ok t₁ ∧
    match t₁ with
    | .some (.prim (.bool true)) => t = t₁
    | _ => CompileOrSym t t₁ (compilePred x₂ it εnv)
:= by
  rw [compilePred.eq_def] at h₁
  simp_do_let (compilePred x₁ it εnv) at h₁ ; rename_i t₁ h₂
  exists t₁
  simp only [true_and, CompileOrSym]
  simp only [compileOr] at h₁
  split at h₁
  case h_1 =>
    simp only [Except.ok.injEq] at *
    simp only [h₁]
  case h_2 h₃ h₄ =>
    simp_do_let (compilePred x₂ it εnv) at h₁ ; rename_i t₂ h₅
    split
    case h_1 => simp only [forall_const] at h₃
    case h_2 =>
      simp only [h₄, Except.ok.injEq, exists_eq_left', true_and]
      split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
      rename_i h₆
      simp only [someOf] at h₁
      simp only [h₆, h₁, and_self]
  case h_3 => simp only [reduceCtorEq] at h₁

theorem compilePred_ite_ok_implies {x₁ x₂ x₃ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
  (h₁ : compilePred (.ite x₁ x₂ x₃) it εnv = .ok t) :
  ∃ t₁,
    (compilePred x₁ it εnv) = .ok t₁ ∧
    match t₁ with
     | .some (.prim (.bool true))  => t = compilePred x₂ it εnv
     | .some (.prim (.bool false)) => t = compilePred x₃ it εnv
     | t₁ => CompileIfSym t t₁ (compilePred x₂ it εnv) (compilePred x₃ it εnv)
:= by
  simp only [CompileIfSym]
  rw [compilePred.eq_def] at h₁
  simp_do_let (compilePred x₁ it εnv) at h₁
  rw [compileIf.eq_def] at h₁
  split at h₁
  case h_1 =>
    exists Term.some (Term.prim (TermPrim.bool true))
    simp only [h₁, and_self]
  case h_2 =>
    exists Term.some (Term.prim (TermPrim.bool false))
    simp only [h₁, and_self]
  case h_3 t₁ _ _ _ _ _ h₂ =>
    simp_do_let (compilePred x₂ it εnv) at h₁
    simp_do_let (compilePred x₃ it εnv) at h₁
    split at h₁ <;> try { contradiction }
    rename_i h₃
    simp only [Except.ok.injEq] at h₁
    exists t₁
    simp only [h₁, h₂, h₃, Except.ok.injEq, exists_and_left, exists_eq_left', true_and]
  case h_4 => simp only [reduceCtorEq] at h₁

theorem compilePred_interpret_and {x₁ x₂ : PredExpr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (h₁ : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (h₃ : compilePred (.and x₁ x₂) it εnv = .ok pt)
    (ih₁ : ∀ {t₁}, compilePred x₁ it εnv = .ok t₁ →
            compilePred x₁ (it.interpret I) (εnv.interpret I) = .ok (t₁.interpret I))
    (ih₂ : ∀ {t₂}, compilePred x₂ it εnv = .ok t₂ →
            compilePred x₂ (it.interpret I) (εnv.interpret I) = .ok (t₂.interpret I)) :
    compilePred (.and x₁ x₂) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  replace ⟨_, hr₁, h₃⟩ := compilePred_and_ok_implies h₃
  simp only [compilePred, ih₁ hr₁, Except.bind_ok]
  clear ih₁
  split at h₃
  case h_1 =>
    simp only [interpret_term_some, interpret_term_prim, compileAnd]
    subst h₃
    simp only [interpret_term_some, interpret_term_prim]
  case h_2 t₁ _ hneq =>
    replace ⟨ht₁, t₂, hr₂, ht₂, h₃⟩ := h₃
    simp only [compileAnd, ih₂ hr₂, Except.bind_ok]
    replace hwφ₁ := compilePred_wf hwε hitw hitty hr₁
    replace hwφ₂ := compilePred_wf hwε hitw hitty hr₂
    have hopt := wf_option_get hwφ₁.left ht₁
    have hite := @wf_ite
      εnv.entities (option.get t₁) t₂ (Term.some (Term.prim (TermPrim.bool false)))
      hopt.left hwφ₂.left (Term.WellFormed.some_wf wf_bool)
      hopt.right (by simp only [Term.typeOf, typeOf_bool, ht₂])
    split
    case h_1 heq =>
      simp only [heq, h₃, Except.ok.injEq]
      simp only [
        interpret_ifSome h₁ hwφ₁.left hite.left,
        interpret_ite h₁ hopt.left hwφ₂.left (wf_term_some wf_bool rfl).left
          hopt.right (by simp only [typeOf_term_some, typeOf_bool, ht₂]),
        interpret_term_some, interpret_term_prim, heq]
      simp only [interpret_option_get I hwφ₁.left ht₁, heq]
      simp only [pe_option_get'_some, pe_ite_false]
      simp only [pe_ifSome_some typeOf_term_some]
    case h_2 =>
      split
      case isTrue ht₁' _ ht₂' =>
        subst h₃
        simp only [Except.ok.injEq,
          interpret_ifSome h₁ hwφ₁.left hite.left, someOf,
          interpret_ite h₁ hopt.left hwφ₂.left (wf_term_some wf_bool rfl).left
            hopt.right (by simp only [typeOf_term_some, typeOf_bool, ht₂]),
          interpret_option_get I hwφ₁.left ht₁,
          interpret_term_some, interpret_term_prim]
        have hoptI := wf_option_get (interpret_term_wf h₁ hwφ₁.left).left ht₁'
        have hoptI' := interpret_term_wf h₁ hwφ₁.left
        simp only [ht₁] at hoptI'
        replace hoptI' := wf_option_get' h₁ hoptI'.left hoptI'.right
        replace hwφ₂ := (interpret_term_wf h₁ hwφ₂.left).left
        have ht' : Term.typeOf (Term.interpret I t₂) = Term.typeOf (Term.some (Term.prim (TermPrim.bool false))) := by
          simp only [Term.typeOf, typeOf_bool, ht₂']
        have hto := wf_ite hoptI.left hwφ₂ (Term.WellFormed.some_wf wf_bool) hoptI.right ht'
        have hto' := wf_ite hoptI'.left hwφ₂ (Term.WellFormed.some_wf wf_bool) hoptI'.right ht'
        rw [ht₂'] at hto hto'
        exact @pe_ifSome_get_eq_get'
          εnv.entities I (Term.interpret I t₁) .bool .bool
          (Factory.ite · (Term.interpret I t₂) (Term.some (Term.prim (TermPrim.bool false))))
          (interpret_term_wfl h₁ hwφ₁.left).left
          (by assumption) (by simp only [hto]) (by simp only [hto'])
      case isFalse ht₂' =>
        have hwφ₂' := (interpret_term_wf h₁ hwφ₂.left).right
        simp only [hwφ₂', ht₂, not_true_eq_false] at ht₂'
    case h_3 ht₁' =>
      have hwφ₁' := (interpret_term_wf h₁ hwφ₁.left).right
      simp only [hwφ₁', ht₁, forall_const] at ht₁'

end Cedar.Thm
