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
import Cedar.Thm.SymCC.Compiler.WF
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

end Cedar.Thm
