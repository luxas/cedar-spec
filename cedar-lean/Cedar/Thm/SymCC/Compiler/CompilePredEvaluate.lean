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
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Compiler.CompilePredInterpret
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
  replace ih := ih heq hwfenv hwε hitv hitw hitty hr
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

end Cedar.Thm
