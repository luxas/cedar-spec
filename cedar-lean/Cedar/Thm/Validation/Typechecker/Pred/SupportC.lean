/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic

/-!
# Predicate type soundness — shared support for arm C (`.and`/`.or`/`.ite`)

Arm C's three control operators (`.and`, `.or`, `.ite`) all coerce an operand's
`Result Value` to `Result Bool` via `Result.as Bool`. The guarded-capability and
value halves repeatedly need to recover the underlying `Value` from a
`Result.as Bool _ = .ok b` fact. This file provides that inversion as a single
reusable lemma (a pred-local copy of `as_bool_ok_inv` from the Levels theory, kept
here to keep arm C self-contained for the parallel merge — no edit to `Basic.lean`
or any sibling arm file).
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- Inversion for the boolean coercion: if `Result.as Bool r = .ok b`, then `r`
was already `.ok (.prim (.bool b))`. -/
theorem pred_as_bool_ok_inv {r : Result Value} {b : Bool} (h : Result.as Bool r = .ok b) :
    r = .ok (.prim (.bool b)) := by
  cases r
  case error e =>
    simp only [Result.as, reduceCtorEq] at h
  case ok v =>
    cases v
    case prim p =>
      cases p <;> simp only [Result.as, Coe.coe, Value.asBool, Except.ok.injEq, reduceCtorEq] at h
      subst h
      rfl
    all_goals simp only [Result.as, Coe.coe, Value.asBool, reduceCtorEq] at h

/-- Inversion for the *coerced* boolean result that the `.and`/`.or`/`.ite`
operators produce: when a `Result.as Bool` is mapped back into `Result Value`
via `>>= fun a => pure (.prim (.bool a))` and equals `.ok (.prim (.bool b))`,
the underlying operand result was `.ok (.prim (.bool b))`. -/
theorem pred_as_bool_mapped_ok_inv {r : Result Value} {b : Bool}
    (h : (Result.as Bool r >>= fun a => pure (Value.prim (Prim.bool a)))
      = .ok (Value.prim (Prim.bool b))) :
    r = .ok (.prim (.bool b)) := by
  cases r
  case error e =>
    simp only [Result.as, Except.bind_err, reduceCtorEq] at h
  case ok v =>
    cases v
    case prim p =>
      cases p <;>
        simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Except.bind_err, pure,
          Except.pure, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, reduceCtorEq] at h
      subst h; rfl
    all_goals
      simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Except.bind_err, pure,
        Except.pure, reduceCtorEq] at h

/-- A `.and` predicate yields `true` only when BOTH operands yield `true`
(the evaluator short-circuits on a `false`/error first operand). -/
theorem pred_and_eval_true_inv {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    (h : evaluatePred (.and x₁ x₂) it req es = .ok (.prim (.bool true))) :
    evaluatePred x₁ it req es = .ok (.prim (.bool true)) ∧
    evaluatePred x₂ it req es = .ok (.prim (.bool true)) := by
  simp only [evaluatePred] at h
  cases hx₁ : evaluatePred x₁ it req es with
  | error e => rw [hx₁] at h; simp only [Result.as, Except.bind_err, reduceCtorEq] at h
  | ok v₁ =>
    rw [hx₁] at h
    cases v₁ <;>
      simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Except.bind_err, reduceCtorEq] at h
    rename_i p; cases p <;>
      simp only [Value.asBool, Except.bind_ok, Except.bind_err, reduceCtorEq] at h
    rename_i b; cases b
    · simp only [Bool.not_false, ite_true, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
        reduceCtorEq] at h
    · simp only [Bool.not_true, ite_false] at h
      exact ⟨rfl, pred_as_bool_mapped_ok_inv h⟩

/-- An `.or` predicate yields `true` only when the first operand yields `true`,
or the first yields `false` and the second yields `true`. Returns the first
operand's boolean value together with the disjunction. -/
theorem pred_or_eval_true_inv {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    (h : evaluatePred (.or x₁ x₂) it req es = .ok (.prim (.bool true))) :
    evaluatePred x₁ it req es = .ok (.prim (.bool true)) ∨
    (evaluatePred x₁ it req es = .ok (.prim (.bool false)) ∧
     evaluatePred x₂ it req es = .ok (.prim (.bool true))) := by
  simp only [evaluatePred] at h
  cases hx₁ : evaluatePred x₁ it req es with
  | error e => rw [hx₁] at h; simp only [Result.as, Except.bind_err, reduceCtorEq] at h
  | ok v₁ =>
    rw [hx₁] at h
    cases v₁ <;>
      simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Except.bind_err, reduceCtorEq] at h
    rename_i p; cases p <;>
      simp only [Value.asBool, Except.bind_ok, Except.bind_err, reduceCtorEq] at h
    rename_i b; cases b
    · simp only [Bool.false_eq_true, ite_false] at h
      exact Or.inr ⟨rfl, pred_as_bool_mapped_ok_inv h⟩
    · exact Or.inl rfl

/-! ### Forward computation lemmas (value side).

These compute `evaluatePred (.and/.or x₁ x₂)` from the operand evaluations, so the
value half of each soundness proof can exhibit the result value directly instead
of re-reducing the `.as Bool`/`pure` coercion by hand. -/

/-- `.and` propagates a first-operand error. -/
theorem pred_and_eval_err₁ {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    {e : Error} (h₁ : evaluatePred x₁ it req es = .error e) :
    evaluatePred (.and x₁ x₂) it req es = .error e := by
  simp only [evaluatePred, h₁, Result.as, Except.bind_err]

/-- `.and` with a `false` first operand short-circuits to `false`. -/
theorem pred_and_eval_false₁ {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    (h₁ : evaluatePred x₁ it req es = .ok (.prim (.bool false))) :
    evaluatePred (.and x₁ x₂) it req es = .ok (.prim (.bool false)) := by
  simp only [evaluatePred, h₁, Result.as, Coe.coe, Value.asBool, Except.bind_ok,
    Bool.not_false, ite_true]

/-- `.and` with `true` first operand returns the second operand's boolean. -/
theorem pred_and_eval_true₁ {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    {b₂ : Bool} (h₁ : evaluatePred x₁ it req es = .ok (.prim (.bool true)))
    (h₂ : evaluatePred x₂ it req es = .ok (.prim (.bool b₂))) :
    evaluatePred (.and x₁ x₂) it req es = .ok (.prim (.bool b₂)) := by
  simp only [evaluatePred, h₁, h₂, Result.as, Coe.coe, Value.asBool, Except.bind_ok,
    Bool.not_true, Bool.false_eq_true, ite_false, pure, Except.pure]

/-- `.and` with `true` first operand propagates a second-operand error. -/
theorem pred_and_eval_err₂ {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    {e : Error} (h₁ : evaluatePred x₁ it req es = .ok (.prim (.bool true)))
    (h₂ : evaluatePred x₂ it req es = .error e) :
    evaluatePred (.and x₁ x₂) it req es = .error e := by
  simp only [evaluatePred, h₁, h₂, Result.as, Coe.coe, Value.asBool, Except.bind_ok,
    Bool.not_true, Bool.false_eq_true, ite_false, Except.bind_err]

/-- `.or` propagates a first-operand error. -/
theorem pred_or_eval_err₁ {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    {e : Error} (h₁ : evaluatePred x₁ it req es = .error e) :
    evaluatePred (.or x₁ x₂) it req es = .error e := by
  simp only [evaluatePred, h₁, Result.as, Except.bind_err]

/-- `.or` with a `true` first operand short-circuits to `true`. -/
theorem pred_or_eval_true₁ {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    (h₁ : evaluatePred x₁ it req es = .ok (.prim (.bool true))) :
    evaluatePred (.or x₁ x₂) it req es = .ok (.prim (.bool true)) := by
  simp only [evaluatePred, h₁, Result.as, Coe.coe, Value.asBool, Except.bind_ok, ite_true]

/-- `.or` with `false` first operand returns the second operand's boolean. -/
theorem pred_or_eval_false₁ {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    {b₂ : Bool} (h₁ : evaluatePred x₁ it req es = .ok (.prim (.bool false)))
    (h₂ : evaluatePred x₂ it req es = .ok (.prim (.bool b₂))) :
    evaluatePred (.or x₁ x₂) it req es = .ok (.prim (.bool b₂)) := by
  simp only [evaluatePred, h₁, h₂, Result.as, Coe.coe, Value.asBool, Except.bind_ok,
    Bool.false_eq_true, ite_false, pure, Except.pure]

/-- `.or` with `false` first operand propagates a second-operand error. -/
theorem pred_or_eval_err₂ {x₁ x₂ : PredExpr} {it : Value} {req : Request} {es : Entities}
    {e : Error} (h₁ : evaluatePred x₁ it req es = .ok (.prim (.bool false)))
    (h₂ : evaluatePred x₂ it req es = .error e) :
    evaluatePred (.or x₁ x₂) it req es = .error e := by
  simp only [evaluatePred, h₁, h₂, Result.as, Coe.coe, Value.asBool, Except.bind_ok,
    Bool.false_eq_true, ite_false, Except.bind_err]

end Cedar.Thm
