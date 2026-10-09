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

end Cedar.Thm
