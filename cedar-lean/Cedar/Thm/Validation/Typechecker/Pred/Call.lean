/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Call

/-!
# Predicate type soundness — `.call` arm (Phase 9c, WEAK form D-94)

Mirror of `type_of_call_is_sound` (`Typechecker/Call.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the WEAK form: no capability
invariant, the error side admits ANY error.

`typeOfPred (.call f xs)` maps `justType ∘ (typeOfPred · itTy c env)` over `xs`
to produce `tys`, then calls the SAME `typeOfCall f tys (xs.map toExpr)` helper
the expression typechecker uses. `evaluatePred (.call f xs)` maps `evaluatePred`
over `xs` then `call f vs`.

Weak soundness means the two interesting cases are:
* some argument errors — the whole `.call` errors (left disjunct of
  `EvaluatesToPred`), witness is any inhabitant of the result type;
* every argument yields a value `vs` — then `call f vs` either errors (left
  disjunct again) or returns a value of the call's result type.

The last fact — that an extension-function call on well-typed arguments returns a
value of `typeOfCall`'s result type or an error — is the extension-function
result-typing lemma, mirrored from the per-function arms of the Expr proof
(`type_of_call_is_sound`). Under weak soundness we need only its *shape* (type or
error), so it is captured by `call_result_instance_of_typeOfCall` below.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Discharge a `∃ v, InstanceOfType env v <concrete ty₀> ∧ (call f vs errors ∨
call f vs = .ok v)` goal where `f` is a concrete `ExtFun`. Cases on the actual
`call f vs` value: `.error` takes the left disjunct (witness is any inhabitant of
the concrete `ty₀`), `.ok w` forces the matching `call` arm via `split`, whose
returned value is of the declared type (the parse arms wrap `res`, so an extra
`split` reads the option).
-/
local macro "solve_call_result" vs:term : tactic =>
  `(tactic| (
    cases hcv : call _ $vs with
    | error e =>
      first
        | exact ⟨_, decimal_is_instance_of_decimal, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, ipaddr_is_instance_of_ipaddr, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, datetime_is_instance_of_datetime, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, duration_is_instance_of_duration, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, bool_is_instance_of_anyBool false, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, InstanceOfType.instance_of_int, Or.inl ⟨e, rfl⟩⟩
    | ok w =>
      refine ⟨w, ?_, Or.inr rfl⟩
      simp only [call] at hcv
      split at hcv <;>
        (try (simp only [res] at hcv; split at hcv)) <;>
        simp only [res, reduceCtorEq, Except.ok.injEq, Coe.coe] at hcv <;>
        (try subst hcv) <;>
        first
          | exact decimal_is_instance_of_decimal
          | exact ipaddr_is_instance_of_ipaddr
          | exact datetime_is_instance_of_datetime
          | exact duration_is_instance_of_duration
          | exact bool_is_instance_of_anyBool _
          | exact InstanceOfType.instance_of_int))

/--
Per-argument inversion for the mapped `typeOfPred` list (pred twin of
`type_of_call_args_inversion`): each `justType (typeOfPred xᵢ ...) = ok txᵢ`
yields a full `typeOfPred xᵢ ... = ok (txᵢ, cᵢ)`.
-/
theorem type_of_pred_call_args_inversion {xs : List PredExpr} {tys : List TypedExpr}
    {itTy : CedarType} {c : Capabilities} {env : TypeEnv}
    (htys : (xs.mapM fun x => justType (typeOfPred x itTy c env)) = Except.ok tys) :
    List.Forall₂ (fun xᵢ txᵢ => ∃ cᵢ, typeOfPred xᵢ itTy c env = Except.ok (txᵢ, cᵢ)) xs tys := by
  cases xs
  case nil =>
    replace htys : tys = [] := by simpa [pure, Except.pure] using htys
    subst htys
    constructor
  case cons x xs =>
    simp only [List.mapM_cons, bind_pure_comp] at htys
    simp_do_let (justType (typeOfPred x itTy c env)) as htx at htys
    simp only [justType, Except.map] at htx
    split at htx <;> simp only [reduceCtorEq, Except.ok.injEq] at htx
    subst htx
    cases htys' : xs.mapM (fun x => justType (typeOfPred x itTy c env)) <;>
      simp only [htys', Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq, bind] at htys
    subst tys
    constructor
    · rename_i r _ _
      exact ⟨r.snd, by rename_i h _; exact h⟩
    · exact type_of_pred_call_args_inversion htys'

/--
Inversion of `typeOfPred (.call f xs)` (pred twin of `type_of_call_inversion`).
The result type is `.call f tys ty₀`, with each argument typed by `typeOfPred`.
-/
theorem type_of_pred_call_inversion {f : ExtFun} {xs : List PredExpr} {itTy : CedarType}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h₁ : typeOfPred (.call f xs) itTy c₁ env = Except.ok (tx, c₂)) :
    ∃ tys,
      (∃ ty₀, tx = .call f tys ty₀) ∧
      typeOfCall f tys (xs.map (fun x => x.toExpr)) = Except.ok (tx, c₂) ∧
      List.Forall₂ (fun xᵢ txᵢ => ∃ cᵢ, typeOfPred xᵢ itTy c₁ env = .ok (txᵢ, cᵢ)) xs tys := by
  simp only [typeOfPred] at h₁
  -- the mapped argument types
  simp_do_let (xs.mapM₁ fun x => justType (typeOfPred x.val itTy c₁ env)) as htys at h₁
  rename_i tys
  -- normalize `map₁`/`mapM₁` to `map`/`mapM`
  simp only [List.map₁_eq_map] at h₁
  have hmap : (xs.mapM fun x => justType (typeOfPred x itTy c₁ env)) = Except.ok tys := by
    rw [← List.mapM₁_eq_mapM (fun x => justType (typeOfPred x itTy c₁ env))]; exact htys
  exists tys
  refine ⟨?_, ?_, type_of_pred_call_args_inversion hmap⟩
  · -- the result shape: typeOfCall produces `.call f tys _`
    simp only [typeOfCall] at h₁
    split at h₁ <;>
    (first
      | contradiction
      | cases hc : typeOfConstructor Ext.Decimal.decimal (xs.map (fun x => x.toExpr)) (CedarType.ext ExtType.decimal) <;> simp only [hc] at h₁
      | cases hc : typeOfConstructor Ext.IPAddr.ip (xs.map (fun x => x.toExpr)) (CedarType.ext ExtType.ipAddr) <;> simp only [hc] at h₁
      | cases hc : typeOfConstructor Cedar.Spec.Ext.Datetime.parse (xs.map (fun x => x.toExpr)) (.ext .datetime) <;> simp only [hc] at h₁
      | cases hc : typeOfConstructor Cedar.Spec.Ext.Datetime.Duration.parse (xs.map (fun x => x.toExpr)) (.ext .duration) <;> simp only [hc] at h₁
      | skip) <;>
    simp only [ok, Except.ok.injEq, Prod.mk.injEq, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁ <;>
    simp only [← h₁] <;>
    exact ⟨_, rfl⟩
  · -- the typeOfCall equation
    exact h₁

/--
Extension-function result typing, WEAK shape (D-94): if
`typeOfCall f tys exprs = .ok (.call f tys ty₀, c)` then for ANY argument values
`vs`, `call f vs` either errors or returns a value that is an instance of `ty₀`.

Proved by cases on `f`: `typeOfCall` pins `ty₀` (and, for the operator arms, the
argument-type shape), and `call f vs` either matches that function's value
pattern — returning a value of `ty₀` (or `.error .extensionError` through `res`
for the fallible parse/arith arms) — or falls through to `.error .typeError`.
Mirrors the per-function result-type facts of `type_of_call_is_sound`; weak
soundness needs only the type-or-error shape.
-/
theorem call_result_instance_of_typeOfCall {f : ExtFun} {tys : List TypedExpr}
    {ty₀ : CedarType} {c : Capabilities} {env : TypeEnv} {exprs : List Expr}
    {vs : List Value}
    (htc : typeOfCall f tys exprs = Except.ok (.call f tys ty₀, c)) :
    ∃ v, InstanceOfType env v ty₀ ∧
         ((∃ e, call f vs = Except.error e) ∨ call f vs = Except.ok v) := by
  -- Pin the result type `ty₀` per function from `typeOfCall`.
  simp only [typeOfCall] at htc
  cases f <;>
    simp only [bind, Except.bind] at htc
  -- Constructor arms: unfold `typeOfConstructor`; the ok case pins `ty₀` to the
  -- declared ext type, every other case is `err = .ok _` and closes.
  case decimal =>
    simp only [typeOfConstructor] at htc
    split at htc <;> (try split at htc) <;>
      simp only [ok, err, Except.bind_ok, Except.bind_err, reduceCtorEq, Except.ok.injEq,
        Prod.mk.injEq, TypedExpr.call.injEq, true_and] at htc
    obtain ⟨hty, _⟩ := htc; subst hty
    solve_call_result vs
  case ip =>
    simp only [typeOfConstructor] at htc
    split at htc <;> (try split at htc) <;>
      simp only [ok, err, Except.bind_ok, Except.bind_err, reduceCtorEq, Except.ok.injEq,
        Prod.mk.injEq, TypedExpr.call.injEq, true_and] at htc
    obtain ⟨hty, _⟩ := htc; subst hty
    solve_call_result vs
  case datetime =>
    simp only [typeOfConstructor] at htc
    split at htc <;> (try split at htc) <;>
      simp only [ok, err, Except.bind_ok, Except.bind_err, reduceCtorEq, Except.ok.injEq,
        Prod.mk.injEq, TypedExpr.call.injEq, true_and] at htc
    obtain ⟨hty, _⟩ := htc; subst hty
    solve_call_result vs
  case duration =>
    simp only [typeOfConstructor] at htc
    split at htc <;> (try split at htc) <;>
      simp only [ok, err, Except.bind_ok, Except.bind_err, reduceCtorEq, Except.ok.injEq,
        Prod.mk.injEq, TypedExpr.call.injEq, true_and] at htc
    obtain ⟨hty, _⟩ := htc; subst hty
    solve_call_result vs
  -- Operator / recognizer / converter arms: `split` keeps the matching tys arm
  -- (binding `ty₀`), the `err` fallthrough (closed by `reduceCtorEq`), and the
  -- cross-constructor arms whose `xfn = _` discriminant equation is impossible.
  all_goals
    (split at htc <;>
      (try (rename_i heq; exact absurd heq (by decide))) <;>
      simp only [ok, err, reduceCtorEq, Except.ok.injEq, Prod.mk.injEq, TypedExpr.call.injEq,
        true_and, and_true] at htc) <;>
    (obtain ⟨hty, _⟩ := htc) <;>
    subst hty <;>
    solve_call_result vs

/--
`.call` predicate soundness (pred twin of `type_of_call_is_sound`), WEAK form.
-/
theorem type_of_pred_call_is_sound {f : ExtFun} {xs : List PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.call f xs) itTy c₁ env = Except.ok (ty, c₂))
    (ih : ∀ x, x ∈ xs → TypeOfPredIsSound x) :
    ∃ v, EvaluatesToPred (.call f xs) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have ⟨tys, ⟨ty₀, hty⟩, htc, _⟩ := type_of_pred_call_inversion h₃
  subst hty
  simp only [TypedExpr.typeOf]
  -- Evaluate the argument list.
  simp only [EvaluatesToPred, evaluatePred,
    List.mapM₁_eq_mapM (fun x => evaluatePred x it request entities)]
  cases hvs : (xs.mapM fun x => evaluatePred x it request entities) with
  | error e =>
    -- an argument errored: the whole call errors (left disjunct); the witness is
    -- the type-correct one the result lemma provides.
    have ⟨v, hinst, _⟩ := call_result_instance_of_typeOfCall (vs := []) (env := env) htc
    exact ⟨v, Or.inl ⟨e, by simp only [hvs, Except.bind_err]⟩, hinst⟩
  | ok vs =>
    simp only [hvs, Except.bind_ok]
    have ⟨v, hinst, hcall⟩ := call_result_instance_of_typeOfCall (vs := vs) (env := env) htc
    rcases hcall with ⟨e, herr⟩ | hok
    · exact ⟨v, Or.inl ⟨e, herr⟩, hinst⟩
    · exact ⟨v, Or.inr hok, hinst⟩

end Cedar.Thm
