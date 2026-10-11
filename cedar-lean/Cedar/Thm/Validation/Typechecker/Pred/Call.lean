/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Call

/-!
# Predicate type soundness — `.call` arm (Phase 9c, D-94)

Mirror of `type_of_call_is_sound` (`Typechecker/Call.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the full (D-97 option b) form: it takes
`hci : CapabilitiesInvariantPred c₁ …` and concludes
`GuardedCapabilitiesInvariantPred (.call f xs) c₂ …` AND the type-soundness
existential. `.call`'s output capabilities are **empty**, so the guarded
conclusion is discharged by `empty_guarded_capabilities_invariant_pred` with no
use of `hci`.

`typeOfPred (.call f xs)` maps `justType ∘ (typeOfPred · itTy c env)` over `xs`
to produce `tys`, then calls the SAME `typeOfCall f tys (xs.map toExpr)` helper
the expression typechecker uses (the extension-constructor arms inspect their
argument via `toExpr` string literals, exactly as the Expr typechecker does).
`evaluatePred (.call f xs)` maps `evaluatePred` over `xs` then `call f vs`.

Under D-94 weak soundness the two interesting cases are:
* some argument errors — the whole `.call` errors (left disjunct of
  `EvaluatesToPred`), witness is any inhabitant of the result type;
* every argument yields a value `vs` — then `call f vs` either errors (left
  disjunct again) or returns a value of the call's result type.

The last fact — that `call f vs` on any argument values returns a value of
`typeOfCall`'s result type or an error — is `call_result_instance_of_typeOfCall`,
mirrored from the per-function result-type facts of `type_of_call_is_sound`.
Weak soundness needs only its *shape* (type or error).
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

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
The result type is `.call f tys ty₀`, the output capabilities are empty, and the
SAME `typeOfCall f tys (xs.map toExpr)` equation the Expr proof uses holds.
-/
theorem type_of_pred_call_inversion {f : ExtFun} {xs : List PredExpr} {itTy : CedarType}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h₁ : typeOfPred (.call f xs) itTy c₁ env = Except.ok (tx, c₂)) :
    c₂ = ∅ ∧
    ∃ tys ty₀,
      tx = .call f tys ty₀ ∧
      typeOfCall f tys (xs.map (fun x => x.toExpr)) = Except.ok (tx, c₂) := by
  simp only [typeOfPred] at h₁
  -- the mapped argument types
  simp_do_let (xs.mapM₁ fun x => justType (typeOfPred x.val itTy c₁ env)) as htys at h₁
  rename_i tys
  -- normalize `map₁`/`mapM₁` to `map`/`mapM`; now `h₁ : typeOfCall f tys … = ok (tx, c₂)`.
  simp only [List.map₁_eq_map] at h₁
  -- derive the result shape (and empty caps) from `h₁`, keeping `h₁` for the equation
  have hshape : (∃ ty₀, tx = .call f tys ty₀) ∧ c₂ = ∅ := by
    simp only [typeOfCall, typeOfConstructor] at h₁
    split at h₁ <;> (try split at h₁) <;> (try split at h₁) <;>
    simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, Except.bind_ok, Except.bind_err,
      reduceCtorEq] at h₁ <;>
    (obtain ⟨htx, hc₂⟩ := h₁) <;>
    exact ⟨⟨_, htx.symm⟩, hc₂.symm⟩
  obtain ⟨⟨ty₀, htx⟩, hc₂⟩ := hshape
  exact ⟨hc₂, tys, ty₀, htx, h₁⟩

/--
Reduce `htc : typeOfCall f tys exprs = ok (.call f tys ty₀, c)` for a CONCRETE
`f` (after `cases f`), closing the spurious `match xfn` branches via
`contradiction` and pinning `ty₀` into the goal by `subst`. The constructor arms
need the `typeOfConstructor` cases; the operator arms fall through to `skip`.
-/
local macro "reduce_htc " h:ident e:ident : tactic =>
  `(tactic| (
    split at $h:ident <;>
      first
        | contradiction
        | (cases hc : typeOfConstructor Ext.Decimal.decimal $e (CedarType.ext ExtType.decimal) <;> simp only [hc] at $h:ident)
        | (cases hc : typeOfConstructor Ext.IPAddr.ip $e (CedarType.ext ExtType.ipAddr) <;> simp only [hc] at $h:ident)
        | (cases hc : typeOfConstructor Cedar.Spec.Ext.Datetime.parse $e (.ext .datetime) <;> simp only [hc] at $h:ident)
        | (cases hc : typeOfConstructor Cedar.Spec.Ext.Datetime.Duration.parse $e (.ext .duration) <;> simp only [hc] at $h:ident)
        | skip
    all_goals (simp only [ok, err, reduceCtorEq, Except.ok.injEq, Prod.mk.injEq,
      TypedExpr.call.injEq, true_and, and_true, Except.bind_ok, Except.bind_err] at $h:ident)
    all_goals (obtain ⟨hty, _⟩ := $h:ident; subst hty)))

/--
Close a `call_result_instance_of_typeOfCall` goal for a CONCRETE extension
function `$fn`, given that `ty₀` is already pinned to its concrete value.
Cases on `call $fn vs` (concrete, so elimination is non-dependent): `.error`
takes the left disjunct with a fixed inhabitant of `ty₀`; `.ok` reads the
matching `call` arm, whose coerced value is an instance of `ty₀`.
-/
local macro "close_call " fn:term " with " vst:ident envt:ident : tactic =>
  `(tactic| (
    cases hcv : call $fn $vst with
    | error e =>
      first
        | exact ⟨_, @decimal_is_instance_of_decimal $envt default, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, @ipaddr_is_instance_of_ipaddr $envt default, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, @datetime_is_instance_of_datetime $envt default, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, @duration_is_instance_of_duration $envt default, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, @bool_is_instance_of_anyBool $envt false, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, @InstanceOfType.instance_of_int $envt default, Or.inl ⟨e, rfl⟩⟩
    | ok w =>
      refine ⟨w, ?_, Or.inr rfl⟩
      simp only [call] at hcv
      split at hcv <;>
        (try (simp only [res] at hcv; split at hcv)) <;>
        simp only [res, reduceCtorEq, Except.ok.injEq] at hcv <;>
        (try subst hcv) <;>
        first
          | exact decimal_is_instance_of_decimal
          | exact ipaddr_is_instance_of_ipaddr
          | exact datetime_is_instance_of_datetime
          | exact duration_is_instance_of_duration
          | exact bool_is_instance_of_anyBool _
          | exact InstanceOfType.instance_of_int))

/--
Extension-function result typing, WEAK shape (D-94): if
`typeOfCall f tys exprs = .ok (.call f tys ty₀, c)` then for ANY argument values
`vs`, `call f vs` either errors or returns a value that is an instance of `ty₀`.

Proved by cases on `f`: `typeOfCall` pins `ty₀`, and `call f vs` either matches
that function's value pattern — a value of `ty₀` (or `.error .extensionError`
through `res` for the fallible parse arms) — or falls through to
`.error .typeError`. Mirrors the per-function result facts of
`type_of_call_is_sound`; weak soundness needs only the type-or-error shape.
-/
theorem call_result_instance_of_typeOfCall {f : ExtFun} {tys : List TypedExpr}
    {ty₀ : CedarType} {c : Capabilities} {env : TypeEnv} {exprs : List Expr}
    {vs : List Value}
    (htc : typeOfCall f tys exprs = Except.ok (.call f tys ty₀, c)) :
    ∃ v, InstanceOfType env v ty₀ ∧
         ((∃ e, call f vs = Except.error e) ∨ call f vs = Except.ok v) := by
  cases f <;> simp only [typeOfCall] at htc
  case decimal => reduce_htc htc exprs; close_call ExtFun.decimal with vs env
  case ip => reduce_htc htc exprs; close_call ExtFun.ip with vs env
  case datetime => reduce_htc htc exprs; close_call ExtFun.datetime with vs env
  case duration => reduce_htc htc exprs; close_call ExtFun.duration with vs env
  case lessThan => reduce_htc htc exprs; close_call ExtFun.lessThan with vs env
  case lessThanOrEqual => reduce_htc htc exprs; close_call ExtFun.lessThanOrEqual with vs env
  case greaterThan => reduce_htc htc exprs; close_call ExtFun.greaterThan with vs env
  case greaterThanOrEqual => reduce_htc htc exprs; close_call ExtFun.greaterThanOrEqual with vs env
  case isIpv4 => reduce_htc htc exprs; close_call ExtFun.isIpv4 with vs env
  case isIpv6 => reduce_htc htc exprs; close_call ExtFun.isIpv6 with vs env
  case isLoopback => reduce_htc htc exprs; close_call ExtFun.isLoopback with vs env
  case isMulticast => reduce_htc htc exprs; close_call ExtFun.isMulticast with vs env
  case isInRange => reduce_htc htc exprs; close_call ExtFun.isInRange with vs env
  case toMilliseconds => reduce_htc htc exprs; close_call ExtFun.toMilliseconds with vs env
  case toSeconds => reduce_htc htc exprs; close_call ExtFun.toSeconds with vs env
  case toMinutes => reduce_htc htc exprs; close_call ExtFun.toMinutes with vs env
  case toHours => reduce_htc htc exprs; close_call ExtFun.toHours with vs env
  case toDays => reduce_htc htc exprs; close_call ExtFun.toDays with vs env
  case offset => reduce_htc htc exprs; close_call ExtFun.offset with vs env
  case durationSince => reduce_htc htc exprs; close_call ExtFun.durationSince with vs env
  case toDate => reduce_htc htc exprs; close_call ExtFun.toDate with vs env
  case toTime => reduce_htc htc exprs; close_call ExtFun.toTime with vs env


/--
`.call` predicate soundness (pred twin of `type_of_call_is_sound`). `.call`'s
output capabilities are empty, so the guarded conclusion is discharged by
`empty_guarded_capabilities_invariant_pred`; `hci` is unused.
-/
theorem type_of_pred_call_is_sound {f : ExtFun} {xs : List PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.call f xs) itTy c₁ env = Except.ok (ty, c₂))
    (ih : ∀ x, x ∈ xs → TypeOfPredIsSound x) :
    GuardedCapabilitiesInvariantPred (.call f xs) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.call f xs) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have ⟨hc₂, tys, ty₀, hty, htc⟩ := type_of_pred_call_inversion h₃
  subst hc₂
  subst hty
  refine ⟨empty_guarded_capabilities_invariant_pred, ?_⟩
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
