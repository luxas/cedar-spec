/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

-- NOTE (D-68/step C): non-module, parallel to CompilePredInterpret. States that
-- compiling a quantifier predicate `p` over an element term `it` that represents a
-- concrete value `v` agrees (via `∼`) with evaluating `p` on `v`. The `.item` base
-- case uses `it ∼ v` directly; `.lit`/`.var` reuse the existing `compile_evaluate`
-- lemmas (compilePred and compile coincide on those arms); the recursive arms mirror
-- the corresponding `compile_evaluate` helpers against compilePred/evaluatePred.

import Cedar.SymCC
import Cedar.Thm.SymCC.Compiler.LitVar
import Cedar.Thm.SymCC.Compiler.Unary
import Cedar.Thm.SymCC.Compiler.Binary
import Cedar.Thm.SymCC.Compiler.Attr
import Cedar.Thm.SymCC.Compiler.ExtHasAttr
import Cedar.Thm.SymCC.Compiler.Record
import Cedar.Thm.SymCC.Compiler.Call
import Cedar.Thm.SymCC.Compiler.Args
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Compiler.CompilePredInterpret
import Cedar.Thm.SymCC.Compiler.EvaluatePredWF
import Cedar.Thm.SymCC.Term.Same
import Cedar.Thm.Tactics

namespace Cedar.Thm

open Spec SymCC Factory

/-- IH predicate for `compilePred_evaluate`: compiling `p` over an element term `it`
that represents the value `v` agrees with evaluating `p` on `v`. -/
@[expose]
def CompilePredEvaluate (p : PredExpr) : Prop :=
  ∀ {env : Env} {εnv : SymEnv} {it pt : Term} {v : Value} {elemTy : TermType},
    env ∼ εnv →
    env.WellFormed →
    εnv.WellFormed →
    v.WellFormed env.entities →
    ((Except.ok v : Spec.Result Value) ∼ it) →
    it.WellFormed εnv.entities →
    it.typeOf = .option elemTy →
    compilePred p it εnv = .ok pt →
    evaluatePred p v env.request env.entities ∼ pt

/-- `.item`: `compilePred .item it = .ok it` and `evaluatePred .item v = .ok v`,
so the goal is exactly the `it ∼ v` hypothesis. -/
theorem compilePred_evaluate_item {env : Env} {εnv : SymEnv} {it pt : Term} {v : Value}
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hok : compilePred .item it εnv = .ok pt) :
    evaluatePred .item v env.request env.entities ∼ pt := by
  simp only [compilePred, Except.ok.injEq] at hok
  subst hok
  simp only [evaluatePred]
  exact hitv

/-- `.lit`: coincides with `compile`/`evaluate` on a literal. -/
theorem compilePred_evaluate_lit {l : Prim} {env : Env} {εnv : SymEnv} {it pt : Term}
    (hok : compilePred (.lit l) it εnv = .ok pt) :
    evaluatePred (.lit l) v env.request env.entities ∼ pt := by
  have hcomp : compile (.lit l) εnv = .ok pt := by
    simp only [compilePred] at hok; simp only [compile]; exact hok
  have := compile_evaluate_lit (env := env) hcomp
  simpa only [evaluatePred, evaluate] using this

/-- `.var`: coincides with `compile`/`evaluate` on a request variable. -/
theorem compilePred_evaluate_var {vr : Var} {env : Env} {εnv : SymEnv} {it pt : Term}
    (heq : env ∼ εnv)
    (hok : compilePred (.var vr) it εnv = .ok pt) :
    evaluatePred (.var vr) v env.request env.entities ∼ pt := by
  have hcomp : compile (.var vr) εnv = .ok pt := by
    simp only [compilePred] at hok; simp only [compile]; exact hok
  have heval : evaluatePred (.var vr) v env.request env.entities = evaluate (.var vr) env.request env.entities := by
    cases vr <;> simp only [evaluatePred, evaluate]
  rw [heval]
  exact compile_evaluate_var (env := env) heq hcomp

/-- Extraction for the `.unaryApp` predicate arm (mirrors `compile_unaryApp_ok_implies`). -/
theorem compilePred_unaryApp_ok_implies {op₁ : UnaryOp} {x₁ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
    (h₁ : compilePred (.unaryApp op₁ x₁) it εnv = .ok t) :
    ∃ t₁ t₂,
      (compilePred x₁ it εnv) = .ok t₁ ∧
      (compileApp₁ op₁ (option.get t₁)) = .ok t₂ ∧
      t = ifSome t₁ t₂ := by
  rw [compilePred.eq_def] at h₁
  simp_do_let (compilePred x₁ it εnv) at h₁
  rename_i t₂ h₂
  simp_do_let (compileApp₁ op₁ (option.get t₂)) at h₁
  rename_i t₃ h₃
  simp only [Except.ok.injEq] at h₁
  exists t₂, t₃
  simp only [h₃, h₁, and_self]

/-- `.unaryApp` arm (mirrors `compile_evaluate_unaryApp`). -/
theorem compilePred_evaluate_unaryApp {op₁ : UnaryOp} {x₁ : PredExpr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.unaryApp op₁ x₁) it εnv = .ok pt)
    (ih : CompilePredEvaluate x₁) :
    evaluatePred (.unaryApp op₁ x₁) v env.request env.entities ∼ pt := by
  replace ⟨t₁, t₂, hr, ha, ht⟩ := compilePred_unaryApp_ok_implies hok
  subst ht
  have ⟨hwφ₁, _, hty₁⟩ := compilePred_wf hwε hitw hitty hr
  have hwo := wf_option_get hwφ₁ hty₁
  have ⟨_, ty₂, hty₂⟩ := compileApp₁_wf hwo.left ha
  replace ih := ih heq hwfenv hwε hvwf hitv hitw hitty hr
  simp only [evaluatePred]
  simp_do_let (evaluatePred x₁ v env.request env.entities)
  case error e he =>
    rw [he] at ih
    exact same_error_implies_ifSome_error ih hty₂
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    replace ⟨t₁', ht₁, ih⟩ := same_ok_implies ih
    subst ht₁
    simp only [pe_ifSome_some hty₂]
    simp only [pe_option_get_some] at ha
    exact compileApp₁_implies_apply₁ (wf_term_some_implies hwφ₁) ih ha

/-- Extraction for the `.binaryApp` predicate arm (mirrors `compile_binaryApp_ok_implies`). -/
theorem compilePred_binaryApp_ok_implies {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
    (hok : compilePred (.binaryApp op₂ x₁ x₂) it εnv = .ok t) :
    ∃ t₁ t₂ t₃,
      (compilePred x₁ it εnv) = .ok t₁ ∧
      (compilePred x₂ it εnv) = .ok t₂ ∧
      (compileApp₂ op₂ (option.get t₁) (option.get t₂) εnv.entities) = .ok t₃ ∧
      t = ifSome t₁ (ifSome t₂ t₃) := by
  rw [compilePred.eq_def] at hok
  simp_do_let (compilePred x₁ it εnv) at hok
  simp_do_let (compilePred x₂ it εnv) at hok
  rename_i t₁ h₁ t₂ h₂
  simp_do_let (compileApp₂ op₂ (option.get t₁) (option.get t₂) εnv.entities) at hok
  rename_i t₃ h₃
  simp only [Except.ok.injEq] at h₃ hok
  exists t₁, t₂, t₃
  simp only [h₃, hok, and_self]

/-- `.binaryApp` arm (mirrors `compile_evaluate_binaryApp`). -/
theorem compilePred_evaluate_binaryApp {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hr₁refs : PredExpr.ValidRefs (λ uid => env.entities.contains uid) x₁)
    (hok : compilePred (.binaryApp op₂ x₁ x₂) it εnv = .ok pt)
    (ih₁ : CompilePredEvaluate x₁) (ih₂ : CompilePredEvaluate x₂) :
    evaluatePred (.binaryApp op₂ x₁ x₂) v env.request env.entities ∼ pt := by
  replace ⟨t₁, t₂, t₃, hok₁, hok₂, hok, ht⟩ := compilePred_binaryApp_ok_implies hok
  subst ht
  have ⟨hwφ₁, _, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hwo₁ := wf_option_get hwφ₁ hty₁
  have ⟨hwφ₂, _, hty₂⟩ := compilePred_wf hwε hitw hitty hok₂
  have hwo₂ := wf_option_get hwφ₂ hty₂
  have ⟨hwφ₃, ty₃, hty₃⟩ := compileApp₂_wf hwε.right hwo₁.left hwo₂.left hok
  have hty := (wf_ifSome_option hwφ₂ hwφ₃ hty₃).right
  replace ih₁ := ih₁ heq hwfenv hwε hvwf hitv hitw hitty hok₁
  replace ih₂ := ih₂ heq hwfenv hwε hvwf hitv hitw hitty hok₂
  simp only [evaluatePred]
  simp_do_let (evaluatePred x₁ v env.request env.entities)
  case error e he => rw [he] at ih₁; exact same_error_implies_ifSome_error ih₁ hty
  case ok v₁ hv₁ =>
    rw [hv₁] at ih₁
    replace ⟨t₁', ht₁, ih₁'⟩ := same_ok_implies ih₁
    subst ht₁
    simp only [pe_ifSome_some hty]
    simp_do_let (evaluatePred x₂ v env.request env.entities)
    case error e he => rw [he] at ih₂; exact same_error_implies_ifSome_error ih₂ hty₃
    case ok v₂ hv₂ =>
      rw [hv₂] at ih₂
      replace ⟨t₂', ht₂, ih₂'⟩ := same_ok_implies ih₂
      subst ht₂
      simp only [pe_ifSome_some hty₃]
      simp only [pe_option_get_some] at hok
      have hwf₁ := evaluatePred_wf hwfenv hvwf hr₁refs hv₁
      exact compileApp₂_implies_apply₂ heq.right hwf₁ (wf_term_some_implies hwφ₁) (wf_term_some_implies hwφ₂) ih₁' ih₂' hok

/-- Extraction for the `.hasAttr` predicate arm (mirrors `compile_hasAttr_ok_implies`). -/
theorem compilePred_hasAttr_ok_implies {a : Attr} {x₁ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
    (h₁ : compilePred (.hasAttr x₁ a) it εnv = .ok t) :
    ∃ t₁ t₂,
      (compilePred x₁ it εnv) = .ok t₁ ∧
      (compileHasAttr (option.get t₁) a εnv.entities) = .ok t₂ ∧
      t = ifSome t₁ t₂ := by
  rw [compilePred.eq_def] at h₁
  simp_do_let (compilePred x₁ it εnv) at h₁
  rename_i t₂ h₂
  simp_do_let (compileHasAttr (option.get t₂) a εnv.entities) at h₁
  rename_i t₃ h₃
  simp only [Except.ok.injEq] at h₁
  exists t₂, t₃
  simp only [h₃, h₁, and_self]

/-- `.hasAttr` arm (mirrors `compile_evaluate_hasAttr`). -/
theorem compilePred_evaluate_hasAttr {x₁ : PredExpr} {a : Attr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hr₁refs : PredExpr.ValidRefs (λ uid => env.entities.contains uid) x₁)
    (hok : compilePred (.hasAttr x₁ a) it εnv = .ok pt)
    (ih : CompilePredEvaluate x₁) :
    evaluatePred (.hasAttr x₁ a) v env.request env.entities ∼ pt := by
  replace ⟨t₁, t₂, hok₁, hr, ht⟩ := compilePred_hasAttr_ok_implies hok
  subst ht
  have ⟨hwφ₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hwo := wf_option_get hwφ₁ hty₁
  have hwφ₂ := compileHasAttr_wf hwε.right hwo.left hr
  replace ⟨t₃, rty, hr, ha⟩ := compileHasAttr_ok_implies hr
  replace ih := ih heq hwfenv hwε hvwf hitv hitw hitty hok₁
  simp only [evaluatePred]
  simp_do_let (evaluatePred x₁ v env.request env.entities)
  case error e he => rw [he] at ih; exact same_error_implies_ifSome_error ih hwφ₂.right
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    replace hr := compileAttrsOf_ok_implies hr
    rcases hr with ⟨rty', htyₒ, ht₃⟩ | ⟨ety, fₐ, htyₒ, hf, ht₃⟩ <;>
      subst ht₃ <;> simp only [hwo.right] at htyₒ <;> subst htyₒ
    case inl => exact compile_evaluate_hasAttr_record hwφ₁ hty₁ hwo hwφ₂ ha ih
    case inr =>
      have hwf₁ := evaluatePred_wf hwfenv hvwf hr₁refs hv₁
      exact compile_evaluate_hasAttr_entity heq.right hwε.right hwf₁ hwφ₁ hty₁ hwo hwφ₂ hf ha ih

/-- Extraction for the `.getAttr` predicate arm (mirrors `compile_getAttr_ok_implies`). -/
theorem compilePred_getAttr_ok_implies {a : Attr} {x₁ : PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
    (h₁ : compilePred (.getAttr x₁ a) it εnv = .ok t) :
    ∃ t₁ t₂,
      (compilePred x₁ it εnv) = .ok t₁ ∧
      (compileGetAttr (option.get t₁) a εnv.entities) = .ok t₂ ∧
      t = ifSome t₁ t₂ := by
  rw [compilePred.eq_def] at h₁
  simp_do_let (compilePred x₁ it εnv) at h₁
  rename_i t₂ h₂
  simp_do_let (compileGetAttr (option.get t₂) a εnv.entities) at h₁
  rename_i t₃ h₃
  simp only [Except.ok.injEq] at h₁
  exists t₂, t₃
  simp only [h₃, h₁, and_self]

/-- `.getAttr` arm (mirrors `compile_evaluate_getAttr`). -/
theorem compilePred_evaluate_getAttr {x₁ : PredExpr} {a : Attr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hr₁refs : PredExpr.ValidRefs (λ uid => env.entities.contains uid) x₁)
    (hok : compilePred (.getAttr x₁ a) it εnv = .ok pt)
    (ih : CompilePredEvaluate x₁) :
    evaluatePred (.getAttr x₁ a) v env.request env.entities ∼ pt := by
  replace ⟨t₁, t₂, hok₁, hr, ht⟩ := compilePred_getAttr_ok_implies hok
  subst ht
  have ⟨hwφ₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hwo := wf_option_get hwφ₁ hty₁
  have ⟨hwφ₂, tyₐ, htyₐ⟩ := compileGetAttr_wf hwε.right hwo.left hr
  replace ⟨t₃, rty, hr, ha⟩ := compileGetAttr_ok_implies hr
  replace ih := ih heq hwfenv hwε hvwf hitv hitw hitty hok₁
  simp only [evaluatePred]
  simp_do_let (evaluatePred x₁ v env.request env.entities)
  case error e he => rw [he] at ih; exact same_error_implies_ifSome_error ih htyₐ
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    replace hr := compileAttrsOf_ok_implies hr
    rcases hr with ⟨rty', htyₒ, ht₃⟩ | ⟨ety, fₐ, htyₒ, hf, ht₃⟩ <;>
      subst ht₃ <;> simp only [hwo.right] at htyₒ <;> subst htyₒ
    case inl => exact compile_evaluate_getAttr_record hwφ₁ hty₁ hwo hwφ₂ htyₐ ha ih
    case inr =>
      have hwf₁ := evaluatePred_wf hwfenv hvwf hr₁refs hv₁
      exact compile_evaluate_getAttr_entity heq.right hwε.right hwf₁ hwφ₁ hty₁ hwo hwφ₂ htyₐ hf ha ih

/-- `.extHasAttr` arm (mirrors `compile_evaluate_extHasAttr`). -/
theorem compilePred_evaluate_extHasAttr {x₁ : PredExpr} {a : Attr} {l : List Attr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hr₁refs : PredExpr.ValidRefs (λ uid => env.entities.contains uid) x₁)
    (hok : compilePred (.extHasAttr x₁ a l) it εnv = .ok pt)
    (ih : CompilePredEvaluate x₁) :
    evaluatePred (.extHasAttr x₁ a l) v env.request env.entities ∼ pt := by
  rw [compilePred.eq_def] at hok
  simp only at hok
  simp_do_let (compilePred x₁ it εnv) at hok
  rename_i t₁ hok₁
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  have ⟨hwt₁, ty₁, hty₁⟩ := compilePred_wf hwε hitw hitty hok₁
  have hce := compileExtHasAttrRec_wf hwε.right hwt₁ ⟨ty₁, hty₁⟩ hok
  replace ih := ih heq hwfenv hwε hvwf hitv hitw hitty hok₁
  simp only [evaluatePred]
  simp_do_let (evaluatePred x₁ v env.request env.entities)
  case error e he =>
    rw [he] at ih
    have ⟨hne, ty', ht₁⟩ := same_error_implies ih
    subst ht₁
    have ht : pt = .none .bool := compileExtHasAttrRec_none_eq hwε.right hwt₁ hok
    subst ht
    exact same_error_implied_by hne
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    have ⟨t₁', ht₁, ih'⟩ := same_ok_implies ih
    subst ht₁
    exact compile_evaluate_extHasAttr_loop heq.right hwε.right hwfenv.right
      (evaluatePred_wf hwfenv hvwf hr₁refs hv₁) (wf_term_some_implies hwt₁) hok ih'

/-- Generic core of `compile_bool_same_implies_bool` with no `compile` hypothesis. -/
theorem same_bool_term_of_wfl {εs : SymEntities} {t : Term} {v : Value}
    (hwφ : Term.WellFormed εs t)
    (hs  : (Except.ok v : Spec.Result Value) ∼ t)
    (hty : Term.typeOf t = TermType.option TermType.bool) :
    ∃ b, t = .some (.prim (.bool b)) ∧ v = .prim (.bool b) := by
  have hlit := wfl_of_type_option_is_option (And.intro hwφ (same_ok_value_implies_lit hs)) hty
  rcases hlit with hlit | ⟨t', hlit, hty'⟩ <;> subst hlit
  case inl => simp only [Same.same, SameResults] at hs
  case inr =>
    cases hwφ ; rename_i hwφ
    have hlit := isLiteral_some.mp (same_ok_value_implies_lit hs)
    replace ⟨b, hlit⟩ := wfl_of_type_bool_is_bool (And.intro hwφ hlit) hty'
    subst hlit
    exists b
    simp only [true_and]
    exact same_ok_bool_term_implies hs

/-- Pred twin of `compile_evaluate_and_none`. -/
theorem compilePred_evaluate_and_none {x₂ : PredExpr} {εnv : SymEnv} {it : Term} {elemTy : TermType}
    {t : Term} {e : Spec.Error} {ty : TermType}
    (hwε : εnv.WellFormed) (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (h₁ : CompileAndSym t (Term.none ty) (compilePred x₂ it εnv))
    (h₂ : ¬e = Error.entityDoesNotExist) :
    (Except.error e : Spec.Result Value) ∼ t := by
  simp only [CompileAndSym, Term.typeOf, TermType.option.injEq] at h₁
  replace ⟨h₁, t₂, h₃, h₄, h₅⟩ := h₁
  subst h₁
  replace ⟨hwφ₂, _, _⟩ := compilePred_wf hwε hitw hitty h₃
  subst h₅
  have hopt := @wf_option_get εnv.entities (Term.none TermType.bool) .bool
    (Term.WellFormed.none_wf TermType.WellFormed.bool_wf) (typeOf_term_none .bool)
  have hite := @wf_ite
    εnv.entities (option.get (Term.none TermType.bool)) t₂ (Term.some (Term.prim (TermPrim.bool false)))
    hopt.left hwφ₂ (Term.WellFormed.some_wf wf_bool) hopt.right
    (by simp only [typeOf_term_some, typeOf_bool, h₄])
  rw [h₄] at hite
  simp [pe_ifSome_none hite.right]
  exact same_error_implied_by h₂

/-- Pred twin of `compile_evaluate_or_none`. -/
theorem compilePred_evaluate_or_none {x₂ : PredExpr} {εnv : SymEnv} {it : Term} {elemTy : TermType}
    {t : Term} {e : Spec.Error} {ty : TermType}
    (hwε : εnv.WellFormed) (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (h₁ : CompileOrSym t (Term.none ty) (compilePred x₂ it εnv))
    (h₂ : ¬e = Error.entityDoesNotExist) :
    (Except.error e : Spec.Result Value) ∼ t := by
  simp only [CompileOrSym, Term.typeOf, TermType.option.injEq] at h₁
  replace ⟨h₁, t₂, h₃, h₄, h₅⟩ := h₁
  subst h₁
  replace ⟨hwφ₂, _, _⟩ := compilePred_wf hwε hitw hitty h₃
  subst h₅
  have hopt := @wf_option_get εnv.entities (Term.none TermType.bool) .bool
    (Term.WellFormed.none_wf TermType.WellFormed.bool_wf) (typeOf_term_none .bool)
  have hite := @wf_ite
    εnv.entities (option.get (Term.none TermType.bool)) (Term.some (Term.prim (TermPrim.bool true))) t₂
    hopt.left (Term.WellFormed.some_wf wf_bool) hwφ₂ hopt.right
    (by simp only [typeOf_term_some, typeOf_bool, h₄])
  simp only [typeOf_term_some, typeOf_bool] at hite
  simp [pe_ifSome_none hite.right]
  exact same_error_implied_by h₂

/-- Pred twin of `compile_evaluate_ite_none`. -/
theorem compilePred_evaluate_ite_none {x₂ x₃ : PredExpr} {εnv : SymEnv} {it : Term} {elemTy : TermType}
    {t : Term} {e : Spec.Error} {ty : TermType}
    (hwε : εnv.WellFormed) (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (h₁ : CompileIfSym t (Term.none ty) (compilePred x₂ it εnv) (compilePred x₃ it εnv))
    (h₂ : ¬e = Error.entityDoesNotExist) :
    (Except.error e : Spec.Result Value) ∼ t := by
  simp only [CompileIfSym, Term.typeOf, TermType.option.injEq] at h₁
  replace ⟨h₁, t₂, t₃, h₃, h₄, h₅, h₆⟩ := h₁
  subst h₁
  replace ⟨hwφ₂, ty', hty⟩ := compilePred_wf hwε hitw hitty h₃
  replace hwφ₃ := (compilePred_wf hwε hitw hitty h₄).left
  have h₇ :
    (option.get (Term.none TermType.bool)).WellFormed εnv.entities ∧
    (option.get (Term.none TermType.bool)).typeOf = .bool :=
    wf_option_get (Term.WellFormed.none_wf TermType.WellFormed.bool_wf) (typeOf_term_none .bool)
  replace h₇ := (wf_ite h₇.left hwφ₂ hwφ₃ h₇.right h₅).right
  simp only [hty] at h₇
  simp only [pe_ifSome_none h₇] at h₆
  subst h₆
  exact same_error_implied_by h₂

/-- `.and` arm (mirrors `compile_evaluate_and`). -/
theorem compilePred_evaluate_and {x₁ x₂ : PredExpr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.and x₁ x₂) it εnv = .ok pt)
    (ih₁ : CompilePredEvaluate x₁) (ih₂ : CompilePredEvaluate x₂) :
    evaluatePred (.and x₁ x₂) v env.request env.entities ∼ pt := by
  replace ⟨_, hr₁, h₄⟩ := compilePred_and_ok_implies hok
  replace ih₁ := ih₁ heq hwfenv hwε hvwf hitv hitw hitty hr₁
  simp only [evaluatePred, Result.as, Coe.coe, Value.asBool]
  simp_do_let (evaluatePred x₁ v env.request env.entities) <;>
  rename_i h₅ <;>
  simp only [h₅] at ih₁
  case error =>
    replace ⟨ih₁, tty, ih₁'⟩ := same_error_implies ih₁
    subst ih₁'
    simp only at h₄
    exact compilePred_evaluate_and_none hwε hitw hitty h₄ ih₁
  case ok =>
    split <;> simp only [Bool.not_eq_true', Except.bind_ok, Except.bind_err]
    case h_1 t₁ v₀ b =>
      replace ih₁ := same_ok_bool_implies ih₁
      subst ih₁
      cases b <;> simp only [ite_true] at *
      case false => subst h₄; exact same_ok_bool
      case true =>
        replace ⟨t₂, h₄, hty, ht⟩ := h₄.right
        simp only [pe_option_get_some, pe_ite_true, pe_ifSome_some hty] at ht
        subst ht
        replace ih₂ := ih₂ heq hwfenv hwε hvwf hitv hitw hitty h₄
        simp_do_let (evaluatePred x₂ v env.request env.entities)
        case error hx₂ => simp only [hx₂] at ih₂; exact ih₂
        case ok hx₂ =>
          simp only [hx₂] at ih₂
          have ⟨_, _, hvt⟩ := same_bool_term_of_wfl ((compilePred_wf hwε hitw hitty h₄).left) ih₂ hty
          subst hvt
          simp only [↓reduceIte, pure, Except.pure, Except.bind_ok, ih₂]
    case h_2 t₁ v₁ _ hneq =>
      split at h₄
      case h_1 =>
        replace ih₁ := same_ok_bool_term_implies ih₁
        subst ih₁
        simp only [Value.prim.injEq, Prim.bool.injEq, forall_eq'] at hneq
      case h_2 =>
        have ⟨_, _, hvt⟩ := same_bool_term_of_wfl ((compilePred_wf hwε hitw hitty hr₁).left) ih₁ h₄.left
        subst hvt
        simp only [Value.prim.injEq, Prim.bool.injEq, forall_eq'] at hneq

/-- `.or` arm (mirrors `compile_evaluate_or`). -/
theorem compilePred_evaluate_or {x₁ x₂ : PredExpr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.or x₁ x₂) it εnv = .ok pt)
    (ih₁ : CompilePredEvaluate x₁) (ih₂ : CompilePredEvaluate x₂) :
    evaluatePred (.or x₁ x₂) v env.request env.entities ∼ pt := by
  replace ⟨_, hr₁, h₄⟩ := compilePred_or_ok_implies hok
  replace ih₁ := ih₁ heq hwfenv hwε hvwf hitv hitw hitty hr₁
  simp only [evaluatePred, Result.as, Coe.coe, Value.asBool]
  simp_do_let (evaluatePred x₁ v env.request env.entities) <;>
  rename_i h₅ <;>
  simp only [h₅] at ih₁
  case error =>
    replace ⟨ih₁, tty, ih₁'⟩ := same_error_implies ih₁
    subst ih₁'
    simp only at h₄
    exact compilePred_evaluate_or_none hwε hitw hitty h₄ ih₁
  case ok =>
    split <;> simp only [Except.bind_ok, Except.bind_err]
    case h_1 t₁ v₀ b =>
      replace ih₁ := same_ok_bool_implies ih₁
      subst ih₁
      cases b <;> simp only [ite_true] at *
      case true => subst h₄; exact same_ok_bool
      case false =>
        replace ⟨t₂, h₄, hty, ht⟩ := h₄.right
        simp only [pe_option_get_some, pe_ite_false, pe_ifSome_some hty] at ht
        subst ht
        replace ih₂ := ih₂ heq hwfenv hwε hvwf hitv hitw hitty h₄
        simp_do_let (evaluatePred x₂ v env.request env.entities)
        case error hx₂ => simp only [hx₂] at ih₂; exact ih₂
        case ok hx₂ =>
          simp only [hx₂] at ih₂
          have ⟨_, _, hvt⟩ := same_bool_term_of_wfl ((compilePred_wf hwε hitw hitty h₄).left) ih₂ hty
          subst hvt
          simp only [↓reduceIte, pure, Except.pure, Except.bind_ok, ih₂]
    case h_2 t₁ v₁ _ hneq =>
      split at h₄
      case h_1 =>
        replace ih₁ := same_ok_bool_term_implies ih₁
        subst ih₁
        simp only [Value.prim.injEq, Prim.bool.injEq, forall_eq'] at hneq
      case h_2 =>
        have ⟨_, _, hvt⟩ := same_bool_term_of_wfl ((compilePred_wf hwε hitw hitty hr₁).left) ih₁ h₄.left
        subst hvt
        simp only [Value.prim.injEq, Prim.bool.injEq, forall_eq'] at hneq

/-- `.ite` arm (mirrors `compile_evaluate_ite`). -/
theorem compilePred_evaluate_ite {x₁ x₂ x₃ : PredExpr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.ite x₁ x₂ x₃) it εnv = .ok pt)
    (ih₁ : CompilePredEvaluate x₁) (ih₂ : CompilePredEvaluate x₂) (ih₃ : CompilePredEvaluate x₃) :
    evaluatePred (.ite x₁ x₂ x₃) v env.request env.entities ∼ pt := by
  replace ⟨t₁, hr₁, h₄⟩ := compilePred_ite_ok_implies hok
  replace ih₁ := ih₁ heq hwfenv hwε hvwf hitv hitw hitty hr₁
  simp only [evaluatePred, Result.as, Coe.coe, Value.asBool]
  simp_do_let (evaluatePred x₁ v env.request env.entities) <;>
  rename_i h₅ <;>
  simp only [h₅] at ih₁
  case error e =>
    replace ⟨ih₁, tty, ih₁'⟩ := same_error_implies ih₁
    subst ih₁'
    simp only at h₄
    exact compilePred_evaluate_ite_none hwε hitw hitty h₄ ih₁
  case ok v₀ =>
    split <;> simp
    case h_1 b =>
      replace ih₁ := same_ok_bool_implies ih₁
      subst ih₁
      cases b <;>
      simp only at h₄ <;>
      rw [eq_comm] at h₄
      case false =>
        simp only [ite_false, h₄, reduceCtorEq]
        exact ih₃ heq hwfenv hwε hvwf hitv hitw hitty h₄
      case true =>
        simp only [ite_true, h₄]
        exact ih₂ heq hwfenv hwε hvwf hitv hitw hitty h₄
    case h_2 v' hneq =>
      split at h₄
      case h_1 =>
        replace ih₁ := same_ok_bool_term_implies ih₁
        specialize hneq true ih₁
        contradiction
      case h_2 =>
        replace ih₁ := same_ok_bool_term_implies ih₁
        specialize hneq false ih₁
        contradiction
      case h_3 =>
        replace ih₁ := same_ok_value_implies_lit ih₁
        replace ⟨hwφ₁, ty, hty⟩ := compilePred_wf hwε hitw hitty hr₁
        replace hr₁ := wfl_of_type_option_is_option (And.intro hwφ₁ ih₁) hty
        rcases hr₁ with hr₁ | hr₁
        case inl =>
          subst hr₁
          exact compilePred_evaluate_ite_none hwε hitw hitty h₄
            (by simp only [not_false_eq_true, reduceCtorEq])
        case inr h₅ h₆ =>
          replace ⟨t', hr₁, hr₁'⟩ := hr₁ ; subst hr₁ hr₁'
          simp only [CompileIfSym, Term.typeOf, TermType.option.injEq] at h₄
          replace hwφ₁ := wf_term_some_implies hwφ₁
          rw [isLiteral_some] at ih₁
          replace ih₁ := wfl_of_type_bool_is_true_or_false (And.intro hwφ₁ ih₁) h₄.left
          rcases ih₁ with ih₁ | ih₁ <;>
          simp [ih₁] at h₅ h₆

/-- Extraction for the `.record` predicate arm (mirrors `compile_record_ok_implies`). -/
theorem compilePred_record_ok_implies {axs : List (Attr × PredExpr)} {it : Term} {εnv : SymEnv} {t : Term}
    (hok : compilePred (.record axs) it εnv = .ok t) :
    ∃ ats,
      List.Forall₂ (λ px pt => px.fst = pt.fst ∧ compilePred px.snd it εnv = .ok pt.snd) axs ats ∧
      t = compileRecord ats := by
  rw [compilePred.eq_def] at hok
  simp_do_let (axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => do .ok (a₁, ← compilePred x₁ it εnv))) at hok
  rename_i ats hts
  simp only [List.mapM₂_eq_mapM λ (p : Attr × PredExpr) => do
      .ok (p.fst, ← compilePred p.snd it εnv),
    List.mapM_ok_iff_forall₂] at hts
  simp only [Except.ok.injEq] at hok
  exists ats
  simp only [hok, and_true]
  apply List.Forall₂.imp _ hts
  intro px pt hp
  simp_do_let (compilePred px.snd it εnv) at hp
  rename_i t' hr
  simp only [Except.ok.injEq] at hp
  simp only [← hp, and_self]

/-- Per-element IH threading for `.record`/`.call` (pred twin of `compile_evaluate_ihs`). -/
theorem compilePred_evaluate_ihs {axs : List (Attr × PredExpr)} {ats : List (Attr × Term)}
    {env : Env} {εnv : SymEnv} {it : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (ih  : ∀ a x, (a, x) ∈ axs → CompilePredEvaluate x)
    (hok : List.Forall₂ (fun px pt => px.fst = pt.fst ∧ compilePred px.snd it εnv = Except.ok pt.snd) axs ats) :
    List.Forall₂ (fun px pt => px.fst = pt.fst ∧ evaluatePred px.snd v env.request env.entities ∼ pt.snd) axs ats := by
  cases axs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.forall₂_nil_left_iff] at *
    assumption
  case cons xhd xtl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.forall₂_cons_left_iff, exists_and_left] at *
    replace ⟨thd, hok, ttl, htl, hts⟩ := hok
    subst hts
    exists thd
    simp only [hok.left,
      ih xhd.fst xhd.snd (by simp only [true_or]) heq hwfenv hwε hvwf hitv hitw hitty hok.right, and_self,
      List.cons.injEq, true_and, exists_eq_right']
    apply compilePred_evaluate_ihs heq hwfenv hwε hvwf hitv hitw hitty _ htl
    intro a x h
    apply ih a x
    exact Or.inr h

/-- Pred twin of `compile_evaluate_prods`. -/
theorem compilePred_evaluate_prods {axs : List (Attr × PredExpr)} {ats : List (Attr × Term)}
    {avs : List (Attr × Value)} {env : Env} {v : Value}
    (h₁ : List.Forall₂ (λ px pt => px.fst = pt.fst ∧ evaluatePred px.snd v env.request env.entities ∼ pt.snd) axs ats)
    (h₂ : List.Forall₂ (λ px pv => bindAttr px.fst (evaluatePred px.snd v env.request env.entities) = Except.ok pv) axs avs) :
    ∃ (ats' : List (Attr × Term)),
      ats = ats'.map (Prod.map id Term.some) ∧
      List.Forall₂ (λ pt pv => pt.fst = pv.fst ∧ pv.snd ∼ pt.snd) ats' avs := by
  cases axs
  case nil =>
    rw [List.forall₂_nil_left_iff] at h₁ h₂
    subst h₁ h₂
    exists []
    simp only [List.map_nil, List.Forall₂.nil, and_self]
  case cons xhd xtl =>
    replace ⟨thd, ttl, h₁, htl₁, hts⟩ := List.forall₂_cons_left_iff.mp h₁
    replace ⟨vhd, vtl, h₂, htl₂, hvs⟩ := List.forall₂_cons_left_iff.mp h₂
    subst hts hvs
    have ⟨tl', ih⟩ := compilePred_evaluate_prods htl₁ htl₂
    simp only [bindAttr] at h₂
    simp_do_let (evaluatePred xhd.snd v env.request env.entities) at h₂
    rename_i v' hok
    simp only [pure, Except.pure, Except.ok.injEq] at h₂
    subst h₂
    simp only [hok] at h₁
    have ⟨hd', hhd⟩ := same_ok_implies h₁.right
    exists ((thd.fst, hd') :: tl')
    simp only [ih.left, List.map_cons, Prod.map, id_eq, ← hhd.left, h₁.left, List.forall₂_cons,
      hhd.right, and_self, ih.right]

/-- `.record` arm (mirrors `compile_evaluate_record`). -/
theorem compilePred_evaluate_record {axs : List (Attr × PredExpr)} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.record axs) it εnv = .ok pt)
    (ih : ∀ a x, (a, x) ∈ axs → CompilePredEvaluate x) :
    evaluatePred (.record axs) v env.request env.entities ∼ pt := by
  replace ⟨ats, hok, ht⟩ := compilePred_record_ok_implies hok
  subst ht
  replace ih := compilePred_evaluate_ihs heq hwfenv hwε hvwf hitv hitw hitty ih hok
  simp only [compileRecord, someOf, evaluatePred,
      List.mapM₂_eq_mapM λ (p : Attr × PredExpr) => bindAttr p.fst (evaluatePred p.snd v env.request env.entities)]
  simp_do_let (axs.mapM λ p => bindAttr p.fst (evaluatePred p.snd v env.request env.entities))
  case error he =>
    replace ⟨px, hx, he⟩ := List.mapM_error_implies_exists_error he
    replace ⟨pt, ht, ih⟩ := List.forall₂_implies_all_left ih px hx
    simp only [bindAttr] at he
    simp_do_let (evaluatePred px.snd v env.request env.entities) at he
    case error =>
      simp at he ; subst he ; rename_i he
      rw [he] at ih
      have hmem : pt.snd ∈ List.map Prod.snd ats := by
        simp only [List.mem_map]
        exists pt
      exact same_error_implies_ifAllSome_error ih.right hmem typeOf_term_some
    case ok =>
      simp [pure, Except.pure] at he
  case ok avs hok' =>
    rw [List.mapM_ok_iff_forall₂] at hok'
    replace ⟨ats', hts, ih⟩ := compilePred_evaluate_prods ih hok'
    subst hts
    clear hok'
    simp only [List.map_map, prod_snd_comp_prod_map_eq, prod_map_id_comp_eq]
    rw [← List.map_map, pe_ifAllSome_some typeOf_term_some]
    have hid : (Prod.map (@id Attr) (option.get ∘ Term.some)) = id := by
      apply funext
      intro x
      simp only [Prod.map, id_eq, Function.comp_apply, pe_option_get_some]
    simp only [Same.same, SameResults, SameValues, recordOf, hid, List.map_id]
    exact same_forall₂_implies_same_record ih

local macro "simp_compileCall₁_evaluate_ext_pred" env:ident v:ident hwφ:ident ih:ident hok:ident compile_call_thm:ident wf_thm:ident wfl_arg_thm:ident pe_thm:ident ext_fun:ident : tactic => do
  `(tactic| (
    replace ⟨t, hts, hty, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_arg' $hwφ
    replace ⟨x, $ih, hxs⟩ := List.forall₂_singleton_right_iff.mp $ih
    subst hxs
    simp only [List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc]
    cases h₁ : evaluatePred x ($v) ($env).request ($env).entities with simp only [Except.bind_err, Except.bind_ok]
    | error =>
      simp only [h₁] at $ih:ident
      first
      | exact same_error_implies_ifSome_error $ih typeOf_term_some
      | exact same_error_implies_ifSome_error $ih ($wf_thm (wf_option_get $hwφ hty)).right
    | ok =>
      simp only [h₁] at $ih:ident
      replace ⟨_, ht, $ih⟩ := same_ok_implies $ih
      subst ht
      first
      | simp only [pe_ifSome_some typeOf_term_some]
      | simp only [pe_ifSome_some ($wf_thm (wf_option_get $hwφ hty)).right]
      simp only [pe_option_get_some]
      simp only [typeOf_term_some, TermType.option.injEq] at hty
      have ⟨_, ht⟩ := $wfl_arg_thm (And.intro (wf_term_some_implies $hwφ) (same_value_implies_lit $ih)) hty
      subst ht
      replace $ih := same_ext_term_implies $ih
      subst $ih
      simp only [call, $pe_thm:ident]
      first
      | simp only [same_ok_some_iff, Coe.coe, same_ext]
      | rename_i pt _
        cases h: $ext_fun pt <;> simp only [res]
        case none =>
          apply same_error_implied_by; exact ne_of_beq_false rfl
        case some =>
          simp only [same_ok_some_iff, Coe.coe, same_ext]
  ))

local macro "simp_compileCall₂_evaluate_ext_pred" env:ident v:ident hwφ:ident ih:ident hok:ident compile_call_thm:ident wf_thm:ident wfl_arg₁_thm:ident wfl_arg₂_thm:ident pe_thm:ident ext_fun:ident : tactic => do
  `(tactic| (
    replace ⟨t₁, t₂, hts, hty₁, hty₂, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_args' $hwφ
    replace ⟨x₁, x₂, h₁, h₂, $ih⟩ := List.forall₂_pair_right_iff.mp $ih
    subst $ih
    simp only [List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc] at *
    have hty := ($wf_thm (wf_option_get ($hwφ).left hty₁) (wf_option_get ($hwφ).right hty₂)).right
    cases h₃ : (evaluatePred x₁ ($v) ($env).request ($env).entities) with simp only [Except.bind_err, Except.bind_ok]
    | error =>
      simp only [h₃] at h₁
      exact same_error_implies_ifSome_error h₁ (typeOf_ifSome_option hty)
    | ok =>
      simp only [h₃] at h₁
      replace ⟨_, ht₁, h₁⟩ := same_ok_implies h₁
      subst ht₁
      simp only [pe_ifSome_some (typeOf_ifSome_option hty)]
      cases h₄ : (evaluatePred x₂ ($v) ($env).request ($env).entities) with simp only [Except.bind_err, Except.bind_ok]
      | error =>
        simp only [h₄] at h₂
        exact same_error_implies_ifSome_error h₂ hty
      | ok =>
        simp only [h₄] at h₂
        replace ⟨_, ht₂, h₂⟩ := same_ok_implies h₂
        subst ht₂
        simp only [typeOf_term_some, TermType.option.injEq] at hty₁ hty₂
        have ⟨_, ht₁⟩ := $wfl_arg₁_thm (And.intro (wf_term_some_implies ($hwφ).left) (same_value_implies_lit h₁)) hty₁
        have ⟨_, ht₂⟩ := $wfl_arg₂_thm (And.intro (wf_term_some_implies ($hwφ).right) (same_value_implies_lit h₂)) hty₂
        subst ht₁ ht₂
        replace h₁ := same_ext_term_implies h₁
        replace h₂ := same_ext_term_implies h₂
        subst h₁ h₂
        simp only [pe_option_get_some]
        rename_i pt₁ pt₂ _
        simp only [pe_ifSome_some ($wf_thm (And.intro (wf_term_some_implies ($hwφ).left) hty₁) (And.intro (wf_term_some_implies ($hwφ).right) hty₂)).right,
          call]
        simp only [$pe_thm:ident]
        cases $ext_fun pt₁ pt₂ <;> simp only [res]
        case none =>
          apply same_error_implied_by; exact ne_of_beq_false rfl
        case some =>
          simp only [same_ok_some_iff, Coe.coe, same_ext]
  ))

local macro "simp_compileCall₀_evaluate_pred" env:ident v:ident ih:ident hok:ident compile_call_thm:ident : tactic => do
  `(tactic| (
    replace ⟨_, _, hts, hv, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace ⟨x, $ih, hxs⟩ := List.forall₂_singleton_right_iff.mp $ih
    subst hxs
    simp only [List.mem_singleton, forall_eq, List.mapM_cons, List.mapM_nil, pure_bind,
      bind_assoc] at *
    simp_do_let (evaluatePred x ($v) ($env).request ($env).entities) <;>
    rename_i h <;>
    simp only [Same.same, SameResults, h] at $ih:ident
    replace $ih := same_string_term_implies $ih
    subst $ih
    simp only [call, res, hv, Coe.coe, Same.same, SameResults]
    exact same_ext
  ))

local macro "simp_compileCall₁_evaluate_pred" env:ident v:ident hwφ:ident ih:ident hok:ident compile_call_thm:ident wfl_thm:ident pe_thm:ident : tactic => do
  `(tactic| (
    replace ⟨t, hts, hty, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_arg' $hwφ
    replace ⟨x, $ih, hxs⟩ := List.forall₂_singleton_right_iff.mp $ih
    subst hxs
    simp only [List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc]
    cases h₁ : evaluatePred x ($v) ($env).request ($env).entities with simp only [Except.bind_err, Except.bind_ok]
    | error =>
      simp only [h₁] at $ih:ident
      exact same_error_implies_ifSome_error $ih typeOf_term_some
    | ok =>
      simp only [h₁] at $ih:ident
      replace ⟨_, ht, $ih⟩ := same_ok_implies $ih
      subst ht
      simp only [pe_ifSome_some typeOf_term_some, pe_option_get_some]
      simp only [typeOf_term_some, TermType.option.injEq] at hty
      have ⟨_, ht⟩ := $wfl_thm (And.intro (wf_term_some_implies $hwφ) (same_value_implies_lit $ih)) hty
      subst ht
      replace $ih := same_ext_term_implies $ih
      subst $ih
      simp only [call, $pe_thm:ident, same_ok_bool]
      try simp only [same_ok_some_iff, same_int64]
    ))

local macro "simp_compileCall₂_evaluate_pred" env:ident v:ident hwφ:ident ih:ident hok:ident compile_call_thm:ident wfl_thm:ident pe_thm:ident : tactic => do
  `(tactic| (
    replace ⟨t₁, t₂, hts, hty₁, hty₂, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_args' $hwφ
    replace ⟨x₁, x₂, h₁, h₂, $ih⟩ := List.forall₂_pair_right_iff.mp $ih
    subst $ih
    simp only [List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc] at *
    cases h₃ : (evaluatePred x₁ ($v) ($env).request ($env).entities) with simp only [Except.bind_err, Except.bind_ok]
    | error =>
      simp only [h₃] at h₁
      exact same_error_implies_ifSome_error h₁ (typeOf_ifSome_option typeOf_term_some)
    | ok =>
      simp only [h₃] at h₁
      replace ⟨_, ht₁, h₁⟩ := same_ok_implies h₁
      subst ht₁
      simp only [pe_ifSome_some (typeOf_ifSome_option typeOf_term_some)]
      cases h₄ : (evaluatePred x₂ ($v) ($env).request ($env).entities) with simp only [Except.bind_err, Except.bind_ok]
      | error =>
        simp only [h₄] at h₂
        exact same_error_implies_ifSome_error h₂ typeOf_term_some
      | ok =>
        simp only [h₄] at h₂
        replace ⟨_, ht₂, h₂⟩ := same_ok_implies h₂
        subst ht₂
        simp only [typeOf_term_some, TermType.option.injEq] at hty₁ hty₂
        have ⟨_, ht₁⟩ := $wfl_thm (And.intro (wf_term_some_implies ($hwφ).left) (same_value_implies_lit h₁)) hty₁
        have ⟨_, ht₂⟩ := $wfl_thm (And.intro (wf_term_some_implies ($hwφ).right) (same_value_implies_lit h₂)) hty₂
        subst ht₁ ht₂
        replace h₁ := same_ext_term_implies h₁
        replace h₂ := same_ext_term_implies h₂
        subst h₁ h₂
        simp only [pe_option_get_some, pe_ifSome_some typeOf_term_some, call, $pe_thm:ident, same_ok_bool]
  ))

theorem compile_evaluate_call_decimal_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {t : Term}
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.decimal ts = Except.ok t) :
  (do call ExtFun.decimal (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₀_evaluate_pred env v ih hok compileCall_decimal_ok_implies

theorem compile_evaluate_call_ip_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {t : Term}
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.ip ts = Except.ok t) :
  (do call ExtFun.ip (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₀_evaluate_pred env v ih hok compileCall_ipAddr_ok_implies

theorem compile_evaluate_call_decimal_lessThan_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.lessThan ts = Except.ok t) :
  (do call ExtFun.lessThan (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_pred env v hwφ ih hok compileCall_decimal_lessThan_ok_implies
    wfl_of_type_ext_decimal_is_ext_decimal pe_decimal_lessThan

theorem compile_evaluate_call_decimal_lessThanOrEqual_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.lessThanOrEqual ts = Except.ok t) :
  (do call ExtFun.lessThanOrEqual (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_pred env v hwφ ih hok compileCall_decimal_lessThanOrEqual_ok_implies
    wfl_of_type_ext_decimal_is_ext_decimal pe_decimal_lessThanOrEqual

theorem compile_evaluate_call_decimal_greaterThan_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.greaterThan ts = Except.ok t) :
  (do call ExtFun.greaterThan (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_pred env v hwφ ih hok compileCall_decimal_greaterThan_ok_implies
    wfl_of_type_ext_decimal_is_ext_decimal pe_decimal_greaterThan

theorem compile_evaluate_call_decimal_greaterThanOrEqual_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.greaterThanOrEqual ts = Except.ok t) :
  (do call ExtFun.greaterThanOrEqual (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_pred env v hwφ ih hok compileCall_decimal_greaterThanOrEqual_ok_implies
    wfl_of_type_ext_decimal_is_ext_decimal pe_decimal_greaterThanOrEqual

theorem compile_evaluate_call_ipaddr_isIpv4_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isIpv4 ts = Except.ok t) :
  (do call ExtFun.isIpv4 (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok
    compileCall_ipAddr_isIpv4_ok_implies wfl_of_type_ext_ipaddr_is_ext_ipaddr
    pe_ipaddr_isIpv4

theorem compile_evaluate_call_ipaddr_isIpv6_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isIpv6 ts = Except.ok t) :
  (do call ExtFun.isIpv6 (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok
    compileCall_ipAddr_isIpv6_ok_implies wfl_of_type_ext_ipaddr_is_ext_ipaddr
    pe_ipaddr_isIpv6

theorem compile_evaluate_call_ipaddr_isInRange_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isInRange ts = Except.ok t) :
  (do call ExtFun.isInRange (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_pred env v hwφ ih hok compileCall_ipAddr_isInRange_ok_implies
    wfl_of_type_ext_ipaddr_is_ext_ipaddr pe_ipaddr_isInRange

theorem compile_evaluate_call_ipaddr_isLoopback_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isLoopback ts = Except.ok t) :
  (do call ExtFun.isLoopback (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok compileCall_ipAddr_isLoopback_ok_implies
    wfl_of_type_ext_ipaddr_is_ext_ipaddr pe_ipaddr_isLoopback

theorem compile_evaluate_call_ipaddr_isMulticast_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isMulticast  ts = Except.ok t) :
  (do call ExtFun.isMulticast  (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok compileCall_ipAddr_isMulticast_ok_implies
    wfl_of_type_ext_ipaddr_is_ext_ipaddr pe_ipaddr_isMulticast

theorem compile_evaluate_call_datetime_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {t : Term}
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.datetime ts = Except.ok t) :
  (do call ExtFun.datetime (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₀_evaluate_pred env v ih hok compileCall_datetime_ok_implies

theorem compile_evaluate_call_duration_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {t : Term}
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.duration ts = Except.ok t) :
  (do call ExtFun.duration (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₀_evaluate_pred env v ih hok compileCall_duration_ok_implies

theorem compile_evaluate_call_datetime_offset_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.offset ts = Except.ok t) :
  (do call ExtFun.offset (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_ext_pred env v hwφ ih hok compileCall_datetime_offset_ok_implies
    wf_datetime_offset wfl_of_type_ext_datetime_is_ext_datetime wfl_of_type_ext_duration_is_ext_duration
    pe_datetime_offset Ext.Datetime.offset

theorem compile_evaluate_call_datetime_durationSince_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.durationSince ts = Except.ok t) :
  (do call ExtFun.durationSince (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_ext_pred env v hwφ ih hok compileCall_datetime_durationSince_ok_implies
    wf_datetime_durationSince wfl_of_type_ext_datetime_is_ext_datetime wfl_of_type_ext_datetime_is_ext_datetime
    pe_datetime_durationSince Ext.Datetime.durationSince

theorem compile_evaluate_call_datetime_toDate_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toDate ts = Except.ok t) :
  (do call ExtFun.toDate (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_ext_pred env v hwφ ih hok compileCall_datetime_toDate_ok_implies
    wf_datetime_toDate wfl_of_type_ext_datetime_is_ext_datetime pe_datetime_toDate Ext.Datetime.toDate

theorem compile_evaluate_call_datetime_toTime_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toTime ts = Except.ok t) :
  (do call ExtFun.toTime (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_ext_pred env v hwφ ih hok compileCall_datetime_toTime_ok_implies
    wf_datetime_toTime wfl_of_type_ext_datetime_is_ext_datetime pe_datetime_toTime Ext.Datetime.toTime

theorem compile_evaluate_call_duration_toMilliseconds_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toMilliseconds ts = Except.ok t) :
  (do call ExtFun.toMilliseconds (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok compileCall_duration_toMilliseconds_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toMilliseconds

theorem compile_evaluate_call_duration_toSeconds_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toSeconds ts = Except.ok t) :
  (do call ExtFun.toSeconds (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok compileCall_duration_toSeconds_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toSeconds

theorem compile_evaluate_call_duration_toMinutes_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toMinutes ts = Except.ok t) :
  (do call ExtFun.toMinutes (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok compileCall_duration_toMinutes_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toMinutes

theorem compile_evaluate_call_duration_toHours_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toHours ts = Except.ok t) :
  (do call ExtFun.toHours (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok compileCall_duration_toHours_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toHours

theorem compile_evaluate_call_duration_toDays_pred {xs : List PredExpr} {v : Value} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluatePred x v env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toDays ts = Except.ok t) :
  (do call ExtFun.toDays (← xs.mapM (evaluatePred · v env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_pred env v hwφ ih hok compileCall_duration_toDays_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toDays

/-- Extraction for the `.call` predicate arm (mirrors `compile_call_ok_implies`). -/
theorem compilePred_call_ok_implies {f : ExtFun} {xs : List PredExpr} {it : Term} {εnv : SymEnv} {t : Term}
    (hok : compilePred (.call f xs) it εnv = .ok t) :
    ∃ ts,
      List.Forall₂ (λ x t => (compilePred x it εnv) = .ok t) xs ts ∧
      compileCall f ts = .ok t := by
  rw [compilePred.eq_def] at hok
  simp_do_let (List.mapM₁ xs fun x => compilePred x.val it εnv) at hok
  rename_i ts hm
  simp only [List.mapM₁_eq_mapM (fun x => compilePred x it εnv), ← List.mapM'_eq_mapM] at hm
  rw [List.mapM'_ok_iff_forall₂] at hm
  exists ts

/-- Per-element WF for the compiled argument terms (pred twin of `compile_wfs`). -/
theorem compilePred_wfs {xs : List PredExpr} {εnv : SymEnv} {it : Term} {elemTy : TermType} {ts : List Term}
    (hwε : εnv.WellFormed) (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : List.Forall₂ (λ x t => compilePred x it εnv = Except.ok t) xs ts) :
    ∀ t ∈ ts, t.WellFormed εnv.entities := by
  cases xs
  case nil =>
    rw [List.forall₂_nil_left_iff] at hok
    subst hok
    simp only [List.not_mem_nil, false_implies, implies_true]
  case cons xhd xtl =>
    replace ⟨thd, ttl, hhd, htl, hts⟩ := List.forall₂_cons_left_iff.mp hok
    subst hts
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with ht | ht
    case inl => subst ht; exact (compilePred_wf hwε hitw hitty hhd).left
    case inr => exact compilePred_wfs hwε hitw hitty htl t ht

/-- Per-element IH threading for `.call` (pred twin of `Args.compile_evaluate_ihs`). -/
theorem compilePred_evaluate_args_ihs {xs : List PredExpr} {env : Env} {εnv : SymEnv}
    {it : Term} {v : Value} {elemTy : TermType} {ts : List Term}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (ih  : ∀ (x : PredExpr), x ∈ xs → CompilePredEvaluate x)
    (hok : List.Forall₂ (fun x t => compilePred x it εnv = Except.ok t) xs ts) :
    List.Forall₂ (fun x t => evaluatePred x v env.request env.entities ∼ t) xs ts := by
  cases xs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.forall₂_nil_left_iff] at *
    assumption
  case cons xhd xtl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.forall₂_cons_left_iff, exists_and_left] at *
    replace ⟨thd, hok, ttl, htl, hts⟩ := hok
    subst hts
    exists thd
    simp only [ih.left heq hwfenv hwε hvwf hitv hitw hitty hok, List.cons.injEq, true_and]
    exists ttl
    simp only [and_true]
    exact compilePred_evaluate_args_ihs heq hwfenv hwε hvwf hitv hitw hitty ih.right htl

/-- `.call` arm (mirrors `compile_evaluate_call`). -/
theorem compilePred_evaluate_call {f : ExtFun} {xs : List PredExpr} {env : Env} {εnv : SymEnv}
    {it pt : Term} {v : Value} {elemTy : TermType}
    (heq : env ∼ εnv) (hwfenv : env.WellFormed) (hwε : εnv.WellFormed)
    (hvwf : v.WellFormed env.entities)
    (hitv : (Except.ok v : Spec.Result Value) ∼ it)
    (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
    (hok : compilePred (.call f xs) it εnv = .ok pt)
    (ih : ∀ x ∈ xs, CompilePredEvaluate x) :
    evaluatePred (.call f xs) v env.request env.entities ∼ pt := by
  replace ⟨ts, hok₂, hok⟩ := compilePred_call_ok_implies hok
  have hwφ := compilePred_wfs hwε hitw hitty hok₂
  replace ih := compilePred_evaluate_args_ihs heq hwfenv hwε hvwf hitv hitw hitty ih hok₂
  simp only [evaluatePred, List.mapM₁_eq_mapM (evaluatePred · v env.request env.entities)]
  cases f
  case decimal => exact compile_evaluate_call_decimal_pred ih hok
  case lessThan => exact compile_evaluate_call_decimal_lessThan_pred hwφ ih hok
  case lessThanOrEqual => exact compile_evaluate_call_decimal_lessThanOrEqual_pred hwφ ih hok
  case greaterThan => exact compile_evaluate_call_decimal_greaterThan_pred hwφ ih hok
  case greaterThanOrEqual => exact compile_evaluate_call_decimal_greaterThanOrEqual_pred hwφ ih hok
  case ip => exact compile_evaluate_call_ip_pred ih hok
  case isIpv4 => exact compile_evaluate_call_ipaddr_isIpv4_pred hwφ ih hok
  case isIpv6 => exact compile_evaluate_call_ipaddr_isIpv6_pred hwφ ih hok
  case isLoopback => exact compile_evaluate_call_ipaddr_isLoopback_pred hwφ ih hok
  case isMulticast => exact compile_evaluate_call_ipaddr_isMulticast_pred hwφ ih hok
  case isInRange => exact compile_evaluate_call_ipaddr_isInRange_pred hwφ ih hok
  case datetime => exact compile_evaluate_call_datetime_pred ih hok
  case duration => exact compile_evaluate_call_duration_pred ih hok
  case offset => exact compile_evaluate_call_datetime_offset_pred hwφ ih hok
  case durationSince => exact compile_evaluate_call_datetime_durationSince_pred hwφ ih hok
  case toDate => exact compile_evaluate_call_datetime_toDate_pred hwφ ih hok
  case toTime => exact compile_evaluate_call_datetime_toTime_pred hwφ ih hok
  case toMilliseconds => exact compile_evaluate_call_duration_toMilliseconds_pred hwφ ih hok
  case toSeconds => exact compile_evaluate_call_duration_toSeconds_pred hwφ ih hok
  case toMinutes => exact compile_evaluate_call_duration_toMinutes_pred hwφ ih hok
  case toHours => exact compile_evaluate_call_duration_toHours_pred hwφ ih hok
  case toDays => exact compile_evaluate_call_duration_toDays_pred hwφ ih hok

end Cedar.Thm
