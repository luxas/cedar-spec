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
import Cedar.Thm.SymCC.Compiler.Args
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

public theorem compilePred_and_ok_implies {x₁ x₂ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
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

public theorem compilePred_or_ok_implies {x₁ x₂ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
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

public theorem compilePred_ite_ok_implies {x₁ x₂ x₃ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
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

theorem compilePred_interpret_or {x₁ x₂ : PredExpr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (h₁ : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (h₃ : compilePred (.or x₁ x₂) it εnv = .ok pt)
    (ih₁ : ∀ {t₁}, compilePred x₁ it εnv = .ok t₁ →
            compilePred x₁ (it.interpret I) (εnv.interpret I) = .ok (t₁.interpret I))
    (ih₂ : ∀ {t₂}, compilePred x₂ it εnv = .ok t₂ →
            compilePred x₂ (it.interpret I) (εnv.interpret I) = .ok (t₂.interpret I)) :
    compilePred (.or x₁ x₂) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  replace ⟨_, hr₁, h₃⟩ := compilePred_or_ok_implies h₃
  simp only [compilePred, ih₁ hr₁, Except.bind_ok]
  clear ih₁
  split at h₃
  case h_1 =>
    simp only [interpret_term_some, interpret_term_prim, compileOr]
    subst h₃
    simp only [interpret_term_some, interpret_term_prim]
  case h_2 t₁ _ hneq =>
    replace ⟨ht₁, t₂, hr₂, ht₂, h₃⟩ := h₃
    simp only [compileOr, ih₂ hr₂, Except.bind_ok]
    replace hwφ₁ := compilePred_wf hwε hitw hitty hr₁
    replace hwφ₂ := compilePred_wf hwε hitw hitty hr₂
    have hopt := wf_option_get hwφ₁.left ht₁
    have hite := @wf_ite
      εnv.entities (option.get t₁) (Term.some (Term.prim (TermPrim.bool true))) t₂
      hopt.left (Term.WellFormed.some_wf wf_bool) hwφ₂.left
      hopt.right (by simp only [Term.typeOf, typeOf_bool, ht₂])
    split
    case h_1 heq =>
      simp only [heq, h₃, Except.ok.injEq]
      simp only [
        interpret_ifSome h₁ hwφ₁.left hite.left,
        interpret_ite h₁ hopt.left (wf_term_some wf_bool rfl).left hwφ₂.left
          hopt.right (by simp only [typeOf_term_some, typeOf_bool, ht₂]),
        interpret_term_some, interpret_term_prim, heq]
      simp only [interpret_option_get I hwφ₁.left ht₁, heq]
      simp only [pe_option_get'_some, pe_ite_true]
      simp only [pe_ifSome_some typeOf_term_some]
    case h_2 =>
      split
      case isTrue ht₁' _ ht₂' =>
        subst h₃
        simp only [Except.ok.injEq,
          interpret_ifSome h₁ hwφ₁.left hite.left, someOf,
          interpret_ite h₁ hopt.left (wf_term_some wf_bool rfl).left hwφ₂.left
            hopt.right (by simp only [typeOf_term_some, typeOf_bool, ht₂]),
          interpret_option_get I hwφ₁.left ht₁,
          interpret_term_some, interpret_term_prim]
        have hoptI := wf_option_get (interpret_term_wf h₁ hwφ₁.left).left ht₁'
        have hoptI' := interpret_term_wf h₁ hwφ₁.left
        simp only [ht₁] at hoptI'
        replace hoptI' := wf_option_get' h₁ hoptI'.left hoptI'.right
        replace hwφ₂ := (interpret_term_wf h₁ hwφ₂.left).left
        have ht' : Term.typeOf (Term.some (Term.prim (TermPrim.bool true))) = Term.typeOf (Term.interpret I t₂) := by
          simp only [Term.typeOf, typeOf_bool, ht₂']
        have hto := wf_ite hoptI.left (Term.WellFormed.some_wf wf_bool) hwφ₂ hoptI.right ht'
        have hto' := wf_ite hoptI'.left (Term.WellFormed.some_wf wf_bool) hwφ₂ hoptI'.right ht'
        simp only [typeOf_term_some, typeOf_bool] at hto hto'
        exact @pe_ifSome_get_eq_get'
          εnv.entities I (Term.interpret I t₁) .bool .bool
          (Factory.ite · (Term.some (Term.prim (TermPrim.bool true))) (Term.interpret I t₂))
          (interpret_term_wfl h₁ hwφ₁.left).left
          (by assumption) (by simp only [hto]) (by simp only [hto'])
      case isFalse ht₂' =>
        have hwφ₂' := (interpret_term_wf h₁ hwφ₂.left).right
        simp only [hwφ₂', ht₂, not_true_eq_false] at ht₂'
    case h_3 ht₁' =>
      have hwφ₁' := (interpret_term_wf h₁ hwφ₁.left).right
      simp only [hwφ₁', ht₁, forall_const] at ht₁'

theorem compilePred_interpret_ite {x₁ x₂ x₃ : PredExpr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (h₁ : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (h₃ : compilePred (.ite x₁ x₂ x₃) it εnv = .ok pt)
    (ih₁ : ∀ {t₁}, compilePred x₁ it εnv = .ok t₁ →
            compilePred x₁ (it.interpret I) (εnv.interpret I) = .ok (t₁.interpret I))
    (ih₂ : ∀ {t₂}, compilePred x₂ it εnv = .ok t₂ →
            compilePred x₂ (it.interpret I) (εnv.interpret I) = .ok (t₂.interpret I))
    (ih₃ : ∀ {t₃}, compilePred x₃ it εnv = .ok t₃ →
            compilePred x₃ (it.interpret I) (εnv.interpret I) = .ok (t₃.interpret I)) :
    compilePred (.ite x₁ x₂ x₃) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  replace ⟨_, hr₁, h₃⟩ := compilePred_ite_ok_implies h₃
  simp only [compilePred, ih₁ hr₁, Except.bind_ok]
  clear ih₁
  split at h₃
  case h_1 =>
    simp only [interpret_term_some, interpret_term_prim, someOf, compileIf]
    rw [eq_comm] at h₃
    exact ih₂ h₃
  case h_2 =>
    simp only [interpret_term_some, interpret_term_prim, someOf, compileIf]
    rw [eq_comm] at h₃
    exact ih₃ h₃
  case h_3 t₁ _ h₄ h₅ =>
    replace ⟨hopt, t₂, t₃, hr₂, hr₃, hty, h₃⟩ := h₃
    simp only [compileIf, ih₂ hr₂, ih₃ hr₃, Except.bind_ok]
    clear ih₂ ih₃
    replace hwf₁ := compilePred_wf hwε hitw hitty hr₁
    replace hwf₂ := compilePred_wf hwε hitw hitty hr₂
    replace hwf₃ := compilePred_wf hwε hitw hitty hr₃
    have ⟨h₆, h₇⟩ := wf_option_get hwf₁.left hopt
    have h₈ := wf_ite h₆ hwf₂.left hwf₃.left h₇ hty
    clear hr₁ hr₂ hr₃
    split
    case h_3 hopt' _ _ =>
      have hwf₁' := wf_option_get (interpret_term_wf h₁ hwf₁.left).left hopt'
      have hwf₂' := interpret_term_wf h₁ hwf₂.left
      have hwf₃' := interpret_term_wf h₁ hwf₃.left
      simp only [hwf₂'.right, hty, hwf₃'.right, ite_true, Except.ok.injEq]
      simp only [h₃,
        interpret_ifSome h₁ hwf₁.left h₈.left,
        interpret_ite h₁ h₆ hwf₂.left hwf₃.left h₇ hty,
        interpret_option_get I hwf₁.left hopt]

      have h₉ := (wf_ite hwf₁'.left hwf₂'.left hwf₃'.left hwf₁'.right
        (by simp [hwf₂'.right, hwf₃'.right, hty])).right

      have h₇' := wf_option_get' h₁ hwf₁.left hopt
      have h₈' := wf_ite h₇'.left hwf₂.left hwf₃.left h₇'.right hty
      have h₉' := (interpret_term_wf h₁ h₈'.left).right
      simp only [h₈'.right,
        interpret_ite h₁ h₇'.left hwf₂.left hwf₃.left h₇'.right hty,
        interpret_option_get' h₁ hwf₁.left hopt] at h₉'

      replace ⟨_, hwf₂⟩ := hwf₂.right
      simp only [hwf₂, hwf₂'.right] at h₉ h₉'
      simp [pe_ifSome_get_eq_get' I
          (Factory.ite · (Term.interpret I t₂) (Term.interpret I t₃))
          (interpret_term_wfl h₁ hwf₁.left).left hopt' h₉ h₉']
    case h_4 h =>
      simp only [← (interpret_term_wf h₁ hwf₁.left).right] at hopt
      simp only [hopt, forall_const] at h
    case' h_1 =>
      have ⟨_, hty'⟩ := hwf₂.right
      simp only [← (interpret_term_wf h₁ hwf₂.left).right] at hty'
    case' h_2 =>
      have ⟨_, hty'⟩ := hwf₃.right
      simp only [← (interpret_term_wf h₁ hwf₃.left).right] at hty'
    case h_1 heq _ | h_2 heq _ =>
      subst h₃
      simp only [
        heq,
        interpret_ifSome h₁ hwf₁.left h₈.left,
        interpret_ite h₁ h₆ hwf₂.left hwf₃.left h₇ hty,
        interpret_option_get I hwf₁.left hopt,
        pe_option_get_some,
        pe_ite_true,
        pe_ite_false,
        pe_ifSome_some hty',
        option.get']

theorem compilePred_interpret_extHasAttr {x₁ : PredExpr} {a : Attr} {l : List Attr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.extHasAttr x₁ a l) it εnv = .ok pt)
    (ih₁ : ∀ {t₁}, compilePred x₁ it εnv = .ok t₁ →
            compilePred x₁ (it.interpret I) (εnv.interpret I) = .ok (t₁.interpret I)) :
    compilePred (.extHasAttr x₁ a l) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  simp only [compilePred] at hok ⊢
  cases hok₁ : compilePred x₁ it εnv <;> simp only [hok₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  rename_i t₁
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  have ⟨hwt₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  simp only [ih₁ hok₁, Except.bind_ok]
  simp only [SymEnv.interpret]
  rw [compileExtHasAttr_eq_compileExtHasAttrRec]
  exact compileExtHasAttrRec_interpret hI hwε.right hwt₁ ⟨ty₁, hty₁⟩ hok

/-- Per-element interpret commutation for the `.record` attribute list, carrying the forall-IH. -/
theorem compilePred_interpret_record_ihs {axs : List (Attr × PredExpr)} {ats : List (Attr × Term)}
    {it : Term} {εnv : SymEnv} {I : Interpretation} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (ih : ∀ a x, (a, x) ∈ axs → ∀ {t}, compilePred x it εnv = .ok t →
            compilePred x (it.interpret I) (εnv.interpret I) = .ok (t.interpret I))
    (hok : List.Forall₂ (λ px pt => px.fst = pt.fst ∧ compilePred px.snd it εnv = Except.ok pt.snd) axs ats) :
    List.Forall₂ (λ (ax : Attr × PredExpr) (at' : Attr × Term) =>
      ax.fst = at'.fst ∧ compilePred ax.snd (it.interpret I) (εnv.interpret I) = .ok (at'.snd.interpret I)) axs ats := by
  cases axs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.forall₂_nil_left_iff] at *
    exact hok
  case cons xhd xtl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.forall₂_cons_left_iff, exists_and_left] at *
    replace ⟨(a, t), heq, ttl, hok, htl⟩ := hok
    exists (a, t)
    have ih₁ := ih xhd.fst xhd.snd
    simp only [true_or, forall_const] at ih₁
    simp only [heq.left, ih₁ heq.right, and_self, true_and]
    exists ttl
    simp only [htl, and_true]
    apply compilePred_interpret_record_ihs hI hwε hitw hitty _ hok
    intro a x h
    apply ih a x
    exact Or.inr h

theorem compilePred_interpret_record_prods {axs : List (Attr × PredExpr)} {it : Term} {εnv : SymEnv} {I : Interpretation} {ats ats' : List (Attr × Term)}
    (h₁ : List.Forall₂ (λ (ax : Attr × PredExpr) (at' : Attr × Term) => ax.fst = at'.fst ∧ compilePred ax.snd (it.interpret I) (εnv.interpret I) = Except.ok (at'.snd.interpret I)) axs ats)
    (h₂ : List.Forall₂ (λ (q : Attr × PredExpr) t' => (do Except.ok (q.fst, ← compilePred q.snd (it.interpret I) (εnv.interpret I))) = Except.ok t') axs ats') :
    ats' = ats.map (Prod.map id (Term.interpret I)) := by
  cases h₁
  case nil =>
    simp only [List.forall₂_nil_left_iff] at *
    exact h₂
  case cons xhd thd xtl ttl hhd htl =>
    simp only [List.forall₂_cons_left_iff] at *
    replace ⟨_, ttl', h₂, h₃, h₄⟩ := h₂
    simp only [hhd.right, Except.bind_ok, Except.ok.injEq] at h₂
    subst h₂ h₄
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · unfold Prod.map id; simp only [hhd]
    · exact compilePred_interpret_record_prods htl h₃

theorem compilePred_interpret_record {axs : List (Attr × PredExpr)} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.record axs) it εnv = .ok pt)
    (ih : ∀ a x, (a, x) ∈ axs → ∀ {t}, compilePred x it εnv = .ok t →
            compilePred x (it.interpret I) (εnv.interpret I) = .ok (t.interpret I)) :
    compilePred (.record axs) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  simp only [compilePred] at hok
  simp_do_let (axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => do Except.ok (a₁, ← compilePred x₁ it εnv))) at hok
  rename_i ats hts
  simp only [List.mapM₂_eq_mapM λ (q : Attr × PredExpr) => do Except.ok (q.fst, ← compilePred q.snd it εnv),
    List.mapM_ok_iff_forall₂] at hts
  -- per-attr WF of ats
  have hwφ : ∀ a t, (a, t) ∈ ats → t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty := by
    intro a t hmem
    have ⟨px, hpx, hp⟩ := List.forall₂_implies_all_right hts (a, t) hmem
    cases hxv : compilePred px.snd it εnv <;>
      simp only [hxv, Except.bind_err, Except.bind_ok, reduceCtorEq, Except.ok.injEq] at hp
    rename_i tv
    have hwv := compilePred_wf (p := px.snd) hwε hitw hitty hxv
    simp only [Prod.mk.injEq] at hp
    obtain ⟨_, rfl⟩ := hp
    exact hwv
  -- strip Forall₂ to the compile-ok form for the ihs helper
  have htsf : List.Forall₂ (λ px pt => px.fst = pt.fst ∧ compilePred px.snd it εnv = Except.ok pt.snd) axs ats := by
    apply List.Forall₂.imp _ hts
    intro px pt hp
    cases hxv : compilePred px.snd it εnv with
    | error e => simp only [hxv, Except.bind_err, reduceCtorEq] at hp
    | ok tv =>
      simp only [hxv, Except.bind_ok, Except.ok.injEq] at hp
      subst hp
      refine ⟨rfl, ?_⟩
      simpa using hxv
  replace ih := compilePred_interpret_record_ihs hI hwε hitw hitty ih htsf
  simp only [Except.ok.injEq] at hok; subst hok
  simp only [compilePred, List.mapM₂_eq_mapM λ (p : Attr × PredExpr) => do Except.ok (p.fst, ← compilePred p.snd (Term.interpret I it) (SymEnv.interpret I εnv))]
  simp_do_let (axs.mapM λ (a₁, x₁) => do Except.ok (a₁, ← compilePred x₁ (Term.interpret I it) (SymEnv.interpret I εnv)))
  case error he =>
    replace ⟨ax, hmem, he⟩ := List.mapM_error_implies_exists_error he
    replace ⟨_, _, ih⟩ := List.forall₂_implies_all_left ih ax hmem
    simp only [ih, Except.bind_ok, reduceCtorEq] at he
  case ok ats'' hok' =>
    rw [List.mapM_ok_iff_forall₂] at hok'
    replace ih := compilePred_interpret_record_prods ih hok'
    subst ih
    simp only [compileRecord, someOf, Except.ok.injEq]
    have hwg := wf_prods_implies_wf_map_snd (wf_prods_option_implies_wf_prods hwφ)
    have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd hwφ)
    simp only [interpret_ifAllSome hI hwg hwo hty, interpret_term_some,
      interpret_recordOf, List.map_map, prod_snd_comp_prod_map_eq, prod_map_id_comp_eq]
    exact compile_interpret_record_ifAllSome hI hwφ

theorem compilePred_interpret_call_ihs {xs : List PredExpr} {elemTy : TermType} {it : Term} {εnv : SymEnv} {I : Interpretation} {ts : List Term}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (ih : ∀ x, x ∈ xs → ∀ {t}, compilePred x it εnv = .ok t →
            compilePred x (it.interpret I) (εnv.interpret I) = .ok (t.interpret I))
    (hok : List.Forall₂ (fun x t => compilePred x it εnv = Except.ok t) xs ts) :
    List.Forall₂ (fun x t => compilePred x (it.interpret I) (εnv.interpret I) = Except.ok (Term.interpret I t)) xs ts := by
  cases xs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.forall₂_nil_left_iff] at *
    assumption
  case cons xhd xtl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.forall₂_cons_left_iff, exists_and_left] at *
    replace ⟨thd, hok, ttl, htl, hts⟩ := hok
    subst hts
    exists thd
    simp only [ih.left hok, List.cons.injEq, true_and]
    exists ttl
    simp only [and_true]
    exact compilePred_interpret_call_ihs hI hwε hitw hitty ih.right htl

theorem compilePred_interpret_call {xfn : ExtFun} {xs : List PredExpr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.call xfn xs) it εnv = .ok pt)
    (ih : ∀ x, x ∈ xs → ∀ {t}, compilePred x it εnv = .ok t →
            compilePred x (it.interpret I) (εnv.interpret I) = .ok (t.interpret I)) :
    compilePred (.call xfn xs) (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  simp only [compilePred] at hok
  simp_do_let (xs.mapM₁ (λ ⟨x₁, _⟩ => compilePred x₁ it εnv)) at hok
  rename_i ts hts
  simp only [List.mapM₁_eq_mapM (λ x => compilePred x it εnv), List.mapM_ok_iff_forall₂] at hts
  -- per-arg WF
  have hwφ : ∀ t ∈ ts, t.WellFormed εnv.entities := by
    intro t ht
    replace ⟨x, hx, hxok⟩ := List.forall₂_implies_all_right hts t ht
    exact (compilePred_wf hwε hitw hitty hxok).left
  replace ih := compilePred_interpret_call_ihs (elemTy := elemTy) hI hwε hitw hitty ih hts
  simp only [compilePred, List.mapM₁_eq_mapM (λ x => compilePred x (it.interpret I) (εnv.interpret I))]
  simp_do_let (List.mapM (fun x => compilePred x (it.interpret I) (εnv.interpret I)) xs)
  case error h =>
    replace ⟨x, hmem, h⟩ := List.mapM_error_implies_exists_error h
    replace ⟨_, _, ih⟩ := List.forall₂_implies_all_left ih x hmem
    simp only [h, reduceCtorEq] at ih
  case ok ts' hok' =>
    rw [List.mapM_ok_iff_forall₂] at hok'
    have hteq : List.Forall₂ (λ t t' => Term.interpret I t = t') ts ts' := by
      rw [List.forall₂_iff_map_eq] at ih hok'
      rw [ih, ← List.forall₂_iff_map_eq] at hok'
      simpa only [Except.ok.injEq] using hok'
    simp only [List.forall₂_iff_map_eq, List.map_id'] at hteq
    subst hteq
    exact compileCall_interpret hI hwφ hok

/-- Dispatcher: `compilePred` commutes with interpretation on a well-formed `it`. -/
theorem compilePred_interpret {p : PredExpr} {it : Term} {εnv : SymEnv} {I : Interpretation} {pt : Term} {elemTy : TermType}
    (hI : I.WellFormed εnv.entities) (hwε : εnv.WellFormed)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred p it εnv = .ok pt) :
    compilePred p (it.interpret I) (εnv.interpret I) = .ok (pt.interpret I) := by
  match p with
  | .item => exact compilePred_interpret_item hok
  | .lit l => exact compilePred_interpret_lit hok
  | .var v => exact compilePred_interpret_var hI hwε hok
  | .ite x₁ x₂ x₃ =>
    exact compilePred_interpret_ite hI hwε hitw hitty hok
      (fun h => compilePred_interpret hI hwε hitw hitty h)
      (fun h => compilePred_interpret hI hwε hitw hitty h)
      (fun h => compilePred_interpret hI hwε hitw hitty h)
  | .and x₁ x₂ =>
    exact compilePred_interpret_and hI hwε hitw hitty hok
      (fun h => compilePred_interpret hI hwε hitw hitty h)
      (fun h => compilePred_interpret hI hwε hitw hitty h)
  | .or x₁ x₂ =>
    exact compilePred_interpret_or hI hwε hitw hitty hok
      (fun h => compilePred_interpret hI hwε hitw hitty h)
      (fun h => compilePred_interpret hI hwε hitw hitty h)
  | .unaryApp op₁ x₁ =>
    exact compilePred_interpret_unaryApp hI hwε hitw hitty hok
      (fun h => compilePred_interpret hI hwε hitw hitty h)
  | .binaryApp op₂ x₁ x₂ =>
    exact compilePred_interpret_binaryApp hI hwε hitw hitty hok
      (fun h => compilePred_interpret hI hwε hitw hitty h)
      (fun h => compilePred_interpret hI hwε hitw hitty h)
  | .hasAttr x₁ a =>
    exact compilePred_interpret_hasAttr hI hwε hitw hitty hok
      (fun h => compilePred_interpret hI hwε hitw hitty h)
  | .extHasAttr x₁ a l =>
    exact compilePred_interpret_extHasAttr hI hwε hitw hitty hok
      (fun h => compilePred_interpret hI hwε hitw hitty h)
  | .getAttr x₁ a =>
    exact compilePred_interpret_getAttr hI hwε hitw hitty hok
      (fun h => compilePred_interpret hI hwε hitw hitty h)
  | .record axs =>
    exact compilePred_interpret_record hI hwε hitw hitty hok
      (fun a x hpx {t} h => compilePred_interpret hI hwε hitw hitty h)
  | .call xfn xs =>
    exact compilePred_interpret_call hI hwε hitw hitty hok
      (fun x hpx {t} h => compilePred_interpret hI hwε hitw hitty h)
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := List.sizeOf_snd_lt_sizeOf_list hpx; omega)
      | (have := List.sizeOf_lt_of_mem hpx; omega)

end Cedar.Thm
