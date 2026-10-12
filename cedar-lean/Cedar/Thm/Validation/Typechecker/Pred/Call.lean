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
Prove `call_result_instance_of_typeOfCall` for a CONSTRUCTOR arm (`decimal`,
`ip`, `datetime`, `duration`), bound by the enclosing `cases f`. `$h` is
`typeOfCall $fn tys exprs = ok (.call $fn tys ty₀, c)` after `simp only
[typeOfCall]`; `$mk` is the constructor's partial function, `$extTy` the ext
type it returns, `$inst` the instance lemma. Validated against the decimal arm.

`typeOfCall` is a `do`-bind over `typeOfConstructor $mk exprs $extTy`; `cases` it
(error contradicts `$h`); the ok branch pins `ty₀ = $extTy` by unfolding
`typeOfConstructor`. Then `cases` on `call $fn vs`: the `.ok` row's value is an
`$extTy`-instance, the spurious `call`-table rows closing by contradiction.
-/
local macro "prove_ctor_arm " h:ident e:ident fn:term " mkfn " mk:term " resty " extTy:term " inst " inst:ident " with " vst:ident envt:ident : tactic =>
  `(tactic| (
    cases hcon : typeOfConstructor $mk $e:ident $extTy with
    | error e => simp only [hcon, Except.bind_err, reduceCtorEq] at $h:ident
    | ok val =>
      simp only [hcon, Validation.ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq,
        TypedExpr.call.injEq, true_and] at $h:ident
      obtain ⟨hty, _⟩ := $h:ident
      simp only [typeOfConstructor] at hcon
      split at hcon <;> (try split at hcon) <;>
        simp only [Validation.ok, Validation.err, Except.ok.injEq, reduceCtorEq] at hcon
      subst hty
      rw [← hcon]
      cases hcv : call $fn $vst with
      | error e => exact ⟨_, @$inst $envt default, Or.inl ⟨e, rfl⟩⟩
      | ok w =>
        refine ⟨w, ?_, Or.inr rfl⟩
        simp only [call] at hcv
        split at hcv <;>
          (try simp only [res, reduceCtorEq, Except.ok.injEq] at hcv) <;>
          (try (split at hcv <;> (try simp only [res, reduceCtorEq, Except.ok.injEq] at hcv))) <;>
          (try subst hcv) <;>
          first
            | exact $inst
            | contradiction
            | simp_all))

/--
Prove `call_result_instance_of_typeOfCall` for an OPERATOR arm (comparators,
recognizers, converters, `isInRange`, `offset`, `durationSince`, `toDate`,
`toTime`), bound by the enclosing `cases f`. Validated against the lessThan arm.

`split at $h` peels the `match xfn, tys.map typeOf` table; `simp_all` discharges
every arm but `$fn`'s own via its FALSE `$fn = <otherFn>` discriminant equation.
The one surviving row pins `ty₀`. Then `cases` on `call $fn vs`: the matching
value row is a `ty₀`-instance (`$inst` tries every possible witness), the spurious
`call`-table rows closing by contradiction.
-/
local macro "prove_op_arm " h:ident fn:term " with " vst:ident envt:ident : tactic =>
  `(tactic| (
    split at $h:ident <;>
      simp_all only [Validation.ok, Validation.err, Except.ok.injEq, Prod.mk.injEq,
        TypedExpr.call.injEq, Except.bind_ok, Except.bind_err, reduceCtorEq, true_and, and_true]
    obtain ⟨hty, _⟩ := $h:ident
    subst hty
    cases hcv : call $fn $vst with
    | error e =>
      first
        | exact ⟨_, @bool_is_instance_of_anyBool $envt false, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, @datetime_is_instance_of_datetime $envt default, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, @duration_is_instance_of_duration $envt default, Or.inl ⟨e, rfl⟩⟩
        | exact ⟨_, @InstanceOfType.instance_of_int $envt default, Or.inl ⟨e, rfl⟩⟩
    | ok w =>
      refine ⟨w, ?_, Or.inr rfl⟩
      simp only [call] at hcv
      split at hcv <;>
        (try simp only [res, reduceCtorEq, Except.ok.injEq] at hcv) <;>
        (try (split at hcv <;> (try simp only [res, reduceCtorEq, Except.ok.injEq] at hcv))) <;>
        (try subst hcv) <;>
        first
          | exact bool_is_instance_of_anyBool _
          | exact datetime_is_instance_of_datetime
          | exact duration_is_instance_of_duration
          | exact InstanceOfType.instance_of_int
          | contradiction
          | simp_all))

set_option maxHeartbeats 4000000 in
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
  case decimal => prove_ctor_arm htc exprs ExtFun.decimal mkfn Cedar.Spec.Ext.Decimal.decimal resty (CedarType.ext ExtType.decimal) inst decimal_is_instance_of_decimal with vs env
  case ip => prove_ctor_arm htc exprs ExtFun.ip mkfn Cedar.Spec.Ext.IPAddr.ip resty (CedarType.ext ExtType.ipAddr) inst ipaddr_is_instance_of_ipaddr with vs env
  case datetime => prove_ctor_arm htc exprs ExtFun.datetime mkfn Cedar.Spec.Ext.Datetime.parse resty (CedarType.ext ExtType.datetime) inst datetime_is_instance_of_datetime with vs env
  case duration => prove_ctor_arm htc exprs ExtFun.duration mkfn Cedar.Spec.Ext.Datetime.Duration.parse resty (CedarType.ext ExtType.duration) inst duration_is_instance_of_duration with vs env
  case lessThan => prove_op_arm htc ExtFun.lessThan with vs env
  case lessThanOrEqual => prove_op_arm htc ExtFun.lessThanOrEqual with vs env
  case greaterThan => prove_op_arm htc ExtFun.greaterThan with vs env
  case greaterThanOrEqual => prove_op_arm htc ExtFun.greaterThanOrEqual with vs env
  case isIpv4 => prove_op_arm htc ExtFun.isIpv4 with vs env
  case isIpv6 => prove_op_arm htc ExtFun.isIpv6 with vs env
  case isLoopback => prove_op_arm htc ExtFun.isLoopback with vs env
  case isMulticast => prove_op_arm htc ExtFun.isMulticast with vs env
  case isInRange => prove_op_arm htc ExtFun.isInRange with vs env
  case toMilliseconds => prove_op_arm htc ExtFun.toMilliseconds with vs env
  case toSeconds => prove_op_arm htc ExtFun.toSeconds with vs env
  case toMinutes => prove_op_arm htc ExtFun.toMinutes with vs env
  case toHours => prove_op_arm htc ExtFun.toHours with vs env
  case toDays => prove_op_arm htc ExtFun.toDays with vs env
  case offset => prove_op_arm htc ExtFun.offset with vs env
  case durationSince => prove_op_arm htc ExtFun.durationSince with vs env
  case toDate => prove_op_arm htc ExtFun.toDate with vs env
  case toTime => prove_op_arm htc ExtFun.toTime with vs env


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
