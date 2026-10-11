/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Pred.SupportB
import Cedar.Thm.Validation.Typechecker.BinaryApp

/-!
# Predicate type soundness — `.binaryApp` arm (Phase 9c, full mirror / D-97 option b)

Full mirror of `type_of_binaryApp_is_sound` (`Typechecker/BinaryApp.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, carrying the predicate capability
invariant `CapabilitiesInvariantPred` (`hci`) and concluding the guarded
production of `CapabilitiesInvariantPred c₂` AND that evaluation yields a value
of the returned type or (D-94) **any** error.

`typeOfPred (.binaryApp op x₁ x₂)` peels to `typeOfPred x₁`, `typeOfPred x₂`,
then the SAME `typeOfBinaryApp op ty₁ ty₂ x₁.toCapKey x₂.toCapKey c env` helper
the expression typechecker uses — note the capability-key operands are
`x₁.toCapKey`/`x₂.toCapKey`, NOT `toExpr` (D-97). `evaluatePred (.binaryApp op x₁
x₂)` is `do v₁ ← evaluatePred x₁; v₂ ← evaluatePred x₂; apply₂ op v₁ v₂ es`.

The value side depends ONLY on the operand values `v₁ v₂` and their static types
(from the operand IHs), never on how those values were produced, so each arm's
`apply₂` reasoning is the same as the expression proof's.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Inversion of `typeOfPred (.binaryApp op x₁ x₂)`: it factors through the operand
`typeOfPred` calls and the SAME `typeOfBinaryApp` helper the expression
typechecker uses, over `.toCapKey` of the operands (D-97).
-/
theorem type_of_pred_binaryApp_inversion {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {itTy : CedarType}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (h₁ : typeOfPred (.binaryApp op₂ x₁ x₂) itTy c₁ env = Except.ok (ty, c₂)) :
    ∃ tx₁ c₁' tx₂ c₂',
      typeOfPred x₁ itTy c₁ env = Except.ok (tx₁, c₁') ∧
      typeOfPred x₂ itTy c₁ env = Except.ok (tx₂, c₂') ∧
      typeOfBinaryApp op₂ tx₁ tx₂ x₁.toCapKey x₂.toCapKey c₁ env = Except.ok (ty, c₂) := by
  simp only [typeOfPred] at h₁
  simp_do_let (typeOfPred x₁ itTy c₁ env) as htx₁ at h₁
  simp_do_let (typeOfPred x₂ itTy c₁ env) as htx₂ at h₁
  rename_i r₁ r₂
  have ⟨tx₁, c₁'⟩ := r₁
  have ⟨tx₂, c₂'⟩ := r₂
  exact ⟨tx₁, c₁', tx₂, c₂', rfl, rfl, h₁⟩

/-! ### Per-op value lemmas.

Each takes the operand values + their static types (from the IHs) and the
`typeOfBinaryApp` equation, and shows the `apply₂` result is an instance of the
returned type (or errors). These mirror the value tails of the expression
sub-lemmas but start from the operand VALUE typings, so no re-typing across
`toExpr`-vs-`item` is needed. -/

/-- `less`/`lessEq`: result `.bool .anyBool`, empty caps. -/
theorem typeOfBinaryApp_cmp_typeOf {op₂ : BinaryOp} {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (hop : op₂ = .less ∨ op₂ = .lessEq)
    (h : typeOfBinaryApp op₂ tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ty.typeOf = .bool .anyBool ∧ c₂ = ∅ := by
  rcases hop with hop | hop <;> subst hop <;> unfold typeOfBinaryApp at h <;>
    split at h <;>
    first
    | contradiction
    | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h ;
       obtain ⟨h, hc⟩ := h ; subst h ; exact ⟨rfl, hc.symm⟩)
    | (simp only [ok, err, reduceCtorEq] at h)

/-- `add`/`sub`/`mul`: result `.int`, empty caps, operands both `.int`. -/
theorem typeOfBinaryApp_arith_typeOf {op₂ : BinaryOp} {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (hop : op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul)
    (h : typeOfBinaryApp op₂ tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ty.typeOf = .int ∧ c₂ = ∅ ∧ tx₁.typeOf = .int ∧ tx₂.typeOf = .int := by
  rcases hop with hop | hop | hop <;> subst hop <;> unfold typeOfBinaryApp at h <;>
    (cases hty₁ : tx₁.typeOf <;> cases hty₂ : tx₂.typeOf <;>
      simp only [hty₁, hty₂, ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      first
      | (obtain ⟨h, hc⟩ := h ; subst h ; exact ⟨rfl, hc.symm, rfl, rfl⟩)
      | (exact absurd h (by simp)))

/-- `contains`: result `.bool .anyBool`, empty caps. -/
theorem typeOfBinaryApp_contains_typeOf {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (h : typeOfBinaryApp .contains tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ty.typeOf = .bool .anyBool ∧ c₂ = ∅ := by
  unfold typeOfBinaryApp at h
  split at h <;>
    first
    | contradiction
    | (simp only [ifLubThenBool] at h ;
       split at h <;>
         simp only [ok, err, Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq,
           reduceCtorEq] at h ;
       obtain ⟨h, hc⟩ := h ; subst h ; exact ⟨rfl, hc.symm⟩)
    | (simp only [ok, err, reduceCtorEq] at h)

/-- `containsAll`/`containsAny`: result `.bool .anyBool`, empty caps. -/
theorem typeOfBinaryApp_containsA_typeOf {op₂ : BinaryOp} {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (hop : op₂ = .containsAll ∨ op₂ = .containsAny)
    (h : typeOfBinaryApp op₂ tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ty.typeOf = .bool .anyBool ∧ c₂ = ∅ := by
  rcases hop with hop | hop <;> subst hop <;> unfold typeOfBinaryApp at h <;>
    split at h <;>
    first
    | contradiction
    | (simp only [ifLubThenBool] at h ;
       split at h <;>
         simp only [ok, err, Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq,
           reduceCtorEq] at h ;
       obtain ⟨h, hc⟩ := h ; subst h ; exact ⟨rfl, hc.symm⟩)
    | (simp only [ok, err, reduceCtorEq] at h)

/-! ### Main `.binaryApp` predicate soundness (full mirror, D-97 b). -/

/--
For `less`/`lessEq`/`contains`/`containsAll`/`containsAny`, an `ok` result of
`apply₂` is always a boolean value — regardless of the (abstract) operand values.
-/
theorem apply₂_cmp_contains_ok_is_bool {op₂ : BinaryOp} {v₁ v₂ w : Value} {entities : Entities}
    (hop : op₂ = .less ∨ op₂ = .lessEq ∨ op₂ = .contains ∨ op₂ = .containsAll ∨ op₂ = .containsAny)
    (h : apply₂ op₂ v₁ v₂ entities = .ok w) :
    ∃ b, w = .prim (.bool b) := by
  rcases hop with hop | hop | hop | hop | hop <;> subst hop <;>
    unfold apply₂ at h <;> split at h <;>
    first
    | contradiction
    | (injection h with h; exact ⟨_, h.symm⟩)

theorem evalPred_binaryApp_bool {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {it : Value}
    {request : Request} {entities : Entities} {v₁ v₂ : Value} {env : TypeEnv} {bty : BoolType}
    (hev₁ : (∃ e, evaluatePred x₁ it request entities = .error e) ∨
            evaluatePred x₁ it request entities = .ok v₁)
    (hev₂ : (∃ e, evaluatePred x₂ it request entities = .error e) ∨
            evaluatePred x₂ it request entities = .ok v₂)
    (hok : ∀ w, apply₂ op₂ v₁ v₂ entities = .ok w → InstanceOfType env w (.bool bty)) :
    ∃ v, EvaluatesToPred (.binaryApp op₂ x₁ x₂) it request entities v ∧
         InstanceOfType env v (.bool bty) := by
  have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env bty
  rcases hev₁ with ⟨e₁, hev₁⟩ | hev₁
  · exact ⟨w₀, Or.inl ⟨e₁, by simp only [EvaluatesToPred, evaluatePred, hev₁, Except.bind_err]⟩, hw₀⟩
  rcases hev₂ with ⟨e₂, hev₂⟩ | hev₂
  · exact ⟨w₀, Or.inl ⟨e₂, by simp only [EvaluatesToPred, evaluatePred, hev₁, hev₂, Except.bind_ok, Except.bind_err]⟩, hw₀⟩
  cases happ : apply₂ op₂ v₁ v₂ entities with
  | error e =>
    exact ⟨w₀, Or.inl ⟨e, by simp only [EvaluatesToPred, evaluatePred, hev₁, hev₂, happ, Except.bind_ok]⟩, hw₀⟩
  | ok w =>
    exact ⟨w, Or.inr (by simp only [EvaluatesToPred, evaluatePred, hev₁, hev₂, happ, Except.bind_ok]), hok w happ⟩

/-- Int twin of `evalPred_binaryApp_bool` for the arithmetic ops. -/
theorem evalPred_binaryApp_int {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {it : Value}
    {request : Request} {entities : Entities} {v₁ v₂ : Value} {env : TypeEnv}
    (hev₁ : (∃ e, evaluatePred x₁ it request entities = .error e) ∨
            evaluatePred x₁ it request entities = .ok v₁)
    (hev₂ : (∃ e, evaluatePred x₂ it request entities = .error e) ∨
            evaluatePred x₂ it request entities = .ok v₂)
    (hok : ∀ w, apply₂ op₂ v₁ v₂ entities = .ok w → InstanceOfType env w .int) :
    ∃ v, EvaluatesToPred (.binaryApp op₂ x₁ x₂) it request entities v ∧
         InstanceOfType env v .int := by
  have ⟨w₀, hw₀⟩ := @type_is_inhabited_int env
  rcases hev₁ with ⟨e₁, hev₁⟩ | hev₁
  · exact ⟨w₀, Or.inl ⟨e₁, by simp only [EvaluatesToPred, evaluatePred, hev₁, Except.bind_err]⟩, hw₀⟩
  rcases hev₂ with ⟨e₂, hev₂⟩ | hev₂
  · exact ⟨w₀, Or.inl ⟨e₂, by simp only [EvaluatesToPred, evaluatePred, hev₁, hev₂, Except.bind_ok, Except.bind_err]⟩, hw₀⟩
  cases happ : apply₂ op₂ v₁ v₂ entities with
  | error e =>
    exact ⟨w₀, Or.inl ⟨e, by simp only [EvaluatesToPred, evaluatePred, hev₁, hev₂, happ, Except.bind_ok]⟩, hw₀⟩
  | ok w =>
    exact ⟨w, Or.inr (by simp only [EvaluatesToPred, evaluatePred, hev₁, hev₂, happ, Except.bind_ok]), hok w happ⟩


/-! ### `eq` value lemma.

`typeOfEq` gives `.tt`/`.ff` when both capability-key operands are literals,
`.anyBool` when a LUB exists, and `.ff` for two distinct entity types.
`apply₂ .eq v₁ v₂ = .ok (v₁ == v₂)` unconditionally, so the only content is
matching the precise `BoolType`. -/

theorem type_of_pred_eq_is_sound {x₁ x₂ : PredExpr} {it v₁ v₂ : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    {tx₁ tx₂ : TypedExpr}
    (htb : typeOfBinaryApp .eq tx₁ tx₂ x₁.toCapKey x₂.toCapKey c₁ env = Except.ok (ty, c₂))
    (hev₁ : (∃ e, evaluatePred x₁ it request entities = .error e) ∨
            evaluatePred x₁ it request entities = .ok v₁)
    (hev₂ : (∃ e, evaluatePred x₂ it request entities = .error e) ∨
            evaluatePred x₂ it request entities = .ok v₂)
    (hinst₁ : InstanceOfType env v₁ tx₁.typeOf)
    (hinst₂ : InstanceOfType env v₂ tx₂.typeOf) :
    GuardedCapabilitiesInvariantPred (.binaryApp .eq x₁ x₂) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.binaryApp .eq x₁ x₂) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  simp only [typeOfBinaryApp, typeOfEq, Function.comp] at htb
  split at htb
  case h_1 p₁ p₂ hk₁ hk₂ =>
    -- both capability keys are literals ⇒ both predicates are those literals
    have hx₁ := toCapKey_lit hk₁
    have hx₂ := toCapKey_lit hk₂
    subst hx₁ hx₂
    simp only [evaluatePred] at hev₁ hev₂
    rcases hev₁ with ⟨_, h⟩ | h <;> simp only [reduceCtorEq, Except.ok.injEq] at h
    rcases hev₂ with ⟨_, h'⟩ | h' <;> simp only [reduceCtorEq, Except.ok.injEq] at h'
    subst h; subst h'
    split at htb <;>
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at htb <;>
      obtain ⟨hty, hc⟩ := htb <;> subst hty <;> subst hc <;>
      refine ⟨empty_guarded_capabilities_invariant_pred, (Value.prim p₁ == Value.prim p₂),
        Or.inr (by simp only [evaluatePred, apply₂, Except.bind_ok]), ?_⟩ <;>
      try simp only [TypedExpr.typeOf]
    case isTrue h =>
      simp only [beq_iff_eq] at h; subst h
      simp only [beq_self_eq_true]; exact true_is_instance_of_tt
    case isFalse h =>
      simp only [beq_iff_eq] at h
      have hb : (Value.prim p₁ == Value.prim p₂) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, Value.prim.injEq]; exact h
      rw [hb]; exact false_is_instance_of_ff
  case h_2 =>
    split at htb
    case h_1 =>
      -- LUB some ⇒ .anyBool
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at htb
      obtain ⟨hty, hc⟩ := htb; subst hty; subst hc
      refine ⟨empty_guarded_capabilities_invariant_pred,
        evalPred_binaryApp_bool hev₁ hev₂ (fun w happ => ?_)⟩
      simp only [apply₂, Except.ok.injEq] at happ
      subst happ; exact bool_is_instance_of_anyBool _
    case h_2 =>
      rename_i hnone
      split at htb <;>
        simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at htb
      rename_i ety₁ ety₂ hty₁eq hty₂eq
      obtain ⟨hty, hc⟩ := htb; subst hty; subst hc
      refine ⟨empty_guarded_capabilities_invariant_pred,
        evalPred_binaryApp_bool hev₁ hev₂ (fun w happ => ?_)⟩
      rw [hty₁eq] at hinst₁; rw [hty₂eq] at hinst₂
      have hne := no_entity_type_lub_implies_not_eq hinst₁ hinst₂ (by rw [hty₁eq, hty₂eq] at hnone; exact hnone)
      simp only [apply₂, Except.ok.injEq] at happ
      subst happ
      cases hb : (v₁ == v₂) <;> simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at hb
      · exact false_is_instance_of_ff
      · exact absurd hb hne

theorem type_of_pred_binaryApp_is_sound {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (hnr : NoReservedItKey env)
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.binaryApp op₂ x₁ x₂) itTy c₁ env = Except.ok (ty, c₂))
    (ih₁ : TypeOfPredIsSound x₁)
    (ih₂ : TypeOfPredIsSound x₂) :
    GuardedCapabilitiesInvariantPred (.binaryApp op₂ x₁ x₂) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.binaryApp op₂ x₁ x₂) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have ⟨tx₁, c₁', tx₂, c₂', ht₁, ht₂, htb⟩ := type_of_pred_binaryApp_inversion h₃
  have ⟨_, v₁, hev₁, hinst₁⟩ := ih₁ hnr hci h₂ hit ht₁
  have ⟨_, v₂, hev₂, hinst₂⟩ := ih₂ hnr hci h₂ hit ht₂
  simp only [EvaluatesToPred, evaluatePred] at hev₁ hev₂
  cases op₂
  -- `less`/`lessEq`: result `.bool .anyBool`, empty caps.
  case less =>
    have ⟨hty, hc⟩ := typeOfBinaryApp_cmp_typeOf (Or.inl rfl) htb
    subst hc; rw [hty]
    refine ⟨empty_guarded_capabilities_invariant_pred, evalPred_binaryApp_bool hev₁ hev₂ (fun w happ => ?_)⟩
    have ⟨b, hb⟩ := apply₂_cmp_contains_ok_is_bool (Or.inl rfl) happ
    subst hb; exact bool_is_instance_of_anyBool _
  case lessEq =>
    have ⟨hty, hc⟩ := typeOfBinaryApp_cmp_typeOf (Or.inr rfl) htb
    subst hc; rw [hty]
    refine ⟨empty_guarded_capabilities_invariant_pred, evalPred_binaryApp_bool hev₁ hev₂ (fun w happ => ?_)⟩
    have ⟨b, hb⟩ := apply₂_cmp_contains_ok_is_bool (Or.inr (Or.inl rfl)) happ
    subst hb; exact bool_is_instance_of_anyBool _
  -- `add`/`sub`/`mul`: result `.int`, empty caps.
  case add =>
    have ⟨hty, hc, hi₁, hi₂⟩ := typeOfBinaryApp_arith_typeOf (Or.inl rfl) htb
    subst hc; rw [hty]
    rw [hi₁] at hinst₁; rw [hi₂] at hinst₂
    have ⟨i, hv₁⟩ := instance_of_int_is_int hinst₁
    have ⟨j, hv₂⟩ := instance_of_int_is_int hinst₂
    subst hv₁ hv₂
    refine ⟨empty_guarded_capabilities_invariant_pred, evalPred_binaryApp_int hev₁ hev₂ (fun w happ => ?_)⟩
    simp only [apply₂, intOrErr] at happ
    split at happ <;> simp only [reduceCtorEq, Except.ok.injEq] at happ
    subst happ; exact InstanceOfType.instance_of_int
  case sub =>
    have ⟨hty, hc, hi₁, hi₂⟩ := typeOfBinaryApp_arith_typeOf (Or.inr (Or.inl rfl)) htb
    subst hc; rw [hty]
    rw [hi₁] at hinst₁; rw [hi₂] at hinst₂
    have ⟨i, hv₁⟩ := instance_of_int_is_int hinst₁
    have ⟨j, hv₂⟩ := instance_of_int_is_int hinst₂
    subst hv₁ hv₂
    refine ⟨empty_guarded_capabilities_invariant_pred, evalPred_binaryApp_int hev₁ hev₂ (fun w happ => ?_)⟩
    simp only [apply₂, intOrErr] at happ
    split at happ <;> simp only [reduceCtorEq, Except.ok.injEq] at happ
    subst happ; exact InstanceOfType.instance_of_int
  case mul =>
    have ⟨hty, hc, hi₁, hi₂⟩ := typeOfBinaryApp_arith_typeOf (Or.inr (Or.inr rfl)) htb
    subst hc; rw [hty]
    rw [hi₁] at hinst₁; rw [hi₂] at hinst₂
    have ⟨i, hv₁⟩ := instance_of_int_is_int hinst₁
    have ⟨j, hv₂⟩ := instance_of_int_is_int hinst₂
    subst hv₁ hv₂
    refine ⟨empty_guarded_capabilities_invariant_pred, evalPred_binaryApp_int hev₁ hev₂ (fun w happ => ?_)⟩
    simp only [apply₂, intOrErr] at happ
    split at happ <;> simp only [reduceCtorEq, Except.ok.injEq] at happ
    subst happ; exact InstanceOfType.instance_of_int
  -- `contains`: result `.bool .anyBool`, empty caps.
  case contains =>
    have ⟨hty, hc⟩ := typeOfBinaryApp_contains_typeOf htb
    subst hc; rw [hty]
    refine ⟨empty_guarded_capabilities_invariant_pred, evalPred_binaryApp_bool hev₁ hev₂ (fun w happ => ?_)⟩
    have ⟨b, hb⟩ := apply₂_cmp_contains_ok_is_bool (Or.inr (Or.inr (Or.inl rfl))) happ
    subst hb; exact bool_is_instance_of_anyBool _
  -- `containsAll`/`containsAny`: result `.bool .anyBool`, empty caps.
  case containsAll =>
    have ⟨hty, hc⟩ := typeOfBinaryApp_containsA_typeOf (Or.inl rfl) htb
    subst hc; rw [hty]
    refine ⟨empty_guarded_capabilities_invariant_pred, evalPred_binaryApp_bool hev₁ hev₂ (fun w happ => ?_)⟩
    have ⟨b, hb⟩ := apply₂_cmp_contains_ok_is_bool (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) happ
    subst hb; exact bool_is_instance_of_anyBool _
  case containsAny =>
    have ⟨hty, hc⟩ := typeOfBinaryApp_containsA_typeOf (Or.inr rfl) htb
    subst hc; rw [hty]
    refine ⟨empty_guarded_capabilities_invariant_pred, evalPred_binaryApp_bool hev₁ hev₂ (fun w happ => ?_)⟩
    have ⟨b, hb⟩ := apply₂_cmp_contains_ok_is_bool (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) happ
    subst hb; exact bool_is_instance_of_anyBool _
  -- `eq`: result bool; precise .tt/.ff via literal/entity reasoning.
  case eq =>
    exact type_of_pred_eq_is_sound htb hev₁ hev₂ hinst₁ hinst₂
  -- `mem`: result `.bool (typeOfInₑ/ₛ …)`, empty caps. The value side mirrors
  -- `Typechecker/BinaryApp/Mem.lean` via the SupportB value lemmas; the operand
  -- values and typings come from the IHs. `PredExpr` has no `.set`, so the
  -- action-literal arm of `typeOfInₛ` is unreachable (handled inside the lemma).
  case mem =>
    simp only [typeOfBinaryApp] at htb
    cases hety₁ : tx₁.typeOf with
    | entity ety₁ =>
      rw [hety₁] at hinst₁
      have ⟨uid₁, hty₁eq, hvv₁⟩ := instance_of_entity_type_is_entity hinst₁
      cases hety₂ : tx₂.typeOf with
      | entity ety₂ =>
        simp only [hety₁, hety₂, ok, Except.ok.injEq, Prod.mk.injEq] at htb
        obtain ⟨htyeq, hceq⟩ := htb
        subst hceq
        rw [hety₂] at hinst₂
        have ⟨uid₂, hty₂eq, hvv₂⟩ := instance_of_entity_type_is_entity hinst₂
        subst hvv₁ hvv₂
        rcases hev₁ with ⟨e₁, hev₁⟩ | hev₁
        · have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env (typeOfInₑ ety₁ ety₂ x₁.toCapKey x₂.toCapKey env)
          exact ⟨empty_guarded_capabilities_invariant_pred, w₀,
            Or.inl ⟨e₁, by simp only [evaluatePred, hev₁, Except.bind_err]⟩,
            by rw [← htyeq]; exact hw₀⟩
        rcases hev₂ with ⟨e₂, hev₂⟩ | hev₂
        · have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env (typeOfInₑ ety₁ ety₂ x₁.toCapKey x₂.toCapKey env)
          exact ⟨empty_guarded_capabilities_invariant_pred, w₀,
            Or.inl ⟨e₂, by simp only [evaluatePred, hev₁, hev₂, Except.bind_ok, Except.bind_err]⟩,
            by rw [← htyeq]; exact hw₀⟩
        refine ⟨empty_guarded_capabilities_invariant_pred, ?_⟩
        cases happ : apply₂ .mem (Value.prim (Prim.entityUID uid₁)) (Value.prim (Prim.entityUID uid₂)) entities with
        | error e =>
          have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env (typeOfInₑ ety₁ ety₂ x₁.toCapKey x₂.toCapKey env)
          exact ⟨w₀, Or.inl ⟨e, by simp only [evaluatePred, hev₁, hev₂, happ, Except.bind_ok]⟩,
            by rw [← htyeq]; exact hw₀⟩
        | ok w =>
          refine ⟨w, Or.inr (by simp only [evaluatePred, hev₁, hev₂, happ, Except.bind_ok]), ?_⟩
          rw [← htyeq]
          exact apply₂_mem_entity_instance_of_inₑ h₂ hev₁ hev₂ hty₁eq hty₂eq happ
      | set elemTy =>
        cases helem : elemTy with
        | entity ety₂ =>
          simp only [hety₁, hety₂, helem, ok, Except.ok.injEq, Prod.mk.injEq] at htb
          obtain ⟨htyeq, hceq⟩ := htb
          subst hceq
          rw [hety₂, helem] at hinst₂
          have ⟨vs, hvseq, _⟩ := instance_of_set_type_is_set hinst₂
          subst hvseq hvv₁
          rcases hev₁ with ⟨e₁, hev₁⟩ | hev₁
          · have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env (typeOfInₛ ety₁ ety₂ x₁.toCapKey x₂.toCapKey env)
            exact ⟨empty_guarded_capabilities_invariant_pred, w₀,
              Or.inl ⟨e₁, by simp only [evaluatePred, hev₁, Except.bind_err]⟩,
              by rw [← htyeq]; exact hw₀⟩
          rcases hev₂ with ⟨e₂, hev₂⟩ | hev₂
          · have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env (typeOfInₛ ety₁ ety₂ x₁.toCapKey x₂.toCapKey env)
            exact ⟨empty_guarded_capabilities_invariant_pred, w₀,
              Or.inl ⟨e₂, by simp only [evaluatePred, hev₁, hev₂, Except.bind_ok, Except.bind_err]⟩,
              by rw [← htyeq]; exact hw₀⟩
          refine ⟨empty_guarded_capabilities_invariant_pred, ?_⟩
          obtain ⟨vl⟩ := vs
          cases happ : apply₂ .mem (Value.prim (Prim.entityUID uid₁)) (Value.set (Set.mk vl)) entities with
          | error e =>
            have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env (typeOfInₛ ety₁ ety₂ x₁.toCapKey x₂.toCapKey env)
            exact ⟨w₀, Or.inl ⟨e, by simp only [evaluatePred, hev₁, hev₂, happ, Except.bind_ok]⟩,
              by rw [← htyeq]; exact hw₀⟩
          | ok w =>
            refine ⟨w, Or.inr (by simp only [evaluatePred, hev₁, hev₂, happ, Except.bind_ok]), ?_⟩
            rw [← htyeq]
            exact apply₂_mem_set_instance_of_inₛ h₂ hty₁eq hinst₂ happ
        | _ => simp only [hety₁, hety₂, helem, err, reduceCtorEq] at htb
      | _ => simp only [hety₁, hety₂, err, reduceCtorEq] at htb
    | _ => simp only [hety₁, err, reduceCtorEq] at htb

  -- `hasTag`: result from `typeOfHasTag`. The output cap is empty (`.ff`/`.tt`
  -- branches) or a singleton tag capability (`.anyBool` branch). The capability
  -- `.tt` case IS discharged via `hci.2 x₁.toCapKey x₂.toCapKey _ x₁ x₂ rfl rfl`
  -- (shown below); the schema `.ff` cases and the singleton guarded ∀q producer
  -- side (D-95/D-97) are the residual RED gaps (no `sorry`).
  -- `hasTag`: result from `typeOfHasTag`. Output cap is empty (`.ff`/`.tt`
  -- branches) or a singleton tag capability (`.anyBool` branch). Full mirror of
  -- `Typechecker/BinaryApp/HasTag.lean` over `evaluatePred` /
  -- `CapabilitiesInvariantPred`, with the SupportB `.tag` helpers. The singleton
  -- producer side is discharged by `pred_hasTag_true_implies_cap_inv`, the `.tt`
  -- consumer side by `pred_mem_capabilities_implies_mem_tags`.
  case hasTag =>
    -- `ofCapKey (xᵢ.toCapKey) = xᵢ` from the no-reserved-access facts.
    have hofk₁ : PredExpr.ofCapKey x₁.toCapKey = x₁ :=
      ofCapKey_toCapKey (type_of_pred_implies_no_reserved hnr ht₁)
    have hofk₂ : PredExpr.ofCapKey x₂.toCapKey = x₂ :=
      ofCapKey_toCapKey (type_of_pred_implies_no_reserved hnr ht₂)
    simp only [typeOfBinaryApp] at htb
    cases hety₁ : tx₁.typeOf with
    | entity ety₁ =>
      cases hety₂ : tx₂.typeOf with
      | string =>
        simp only [hety₁, hety₂, bind, Except.bind] at htb
        rw [hety₁] at hinst₁
        have ⟨uid, huidty, hvv₁⟩ := instance_of_entity_type_is_entity hinst₁
        rw [hety₂] at hinst₂
        have ⟨s, hvv₂⟩ := instance_of_string_is_string hinst₂
        subst hvv₁ hvv₂
        cases hht : typeOfHasTag ety₁ x₁.toCapKey x₂.toCapKey c₁ env with
        | error e => simp only [hht, reduceCtorEq] at htb
        | ok p =>
        obtain ⟨tyr, cr⟩ := p
        simp only [hht, ok, Except.ok.injEq, Prod.mk.injEq] at htb
        obtain ⟨htyeq, hceq⟩ := htb
        subst htyeq; subst hceq
        simp only [TypedExpr.typeOf]
        -- `typeOfHasTag` always returns a `.bool _` type here.
        have hbty : ∃ bty, tyr = CedarType.bool bty := by
          simp only [typeOfHasTag] at hht
          split at hht
          · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht; exact ⟨.ff, hht.1.symm⟩
          · split at hht <;> simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht
            · exact ⟨.tt, hht.1.symm⟩
            · exact ⟨.anyBool, hht.1.symm⟩
          · split at hht <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at hht
            exact ⟨.ff, hht.1.symm⟩
        -- Operand-error short-circuits ⇒ the whole predicate errors (any-error side).
        rcases hev₁ with ⟨e₁, hev₁⟩ | hev₁
        · obtain ⟨bty, htyr⟩ := hbty
          have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env bty
          refine ⟨fun hc => absurd hc ?_,
            w₀, Or.inl ⟨e₁, by simp only [evaluatePred, hev₁, Except.bind_err]⟩,
            by rw [htyr]; exact hw₀⟩
          simp only [evaluatePred, hev₁, Except.bind_err, reduceCtorEq, not_false_eq_true]
        rcases hev₂ with ⟨e₂, hev₂⟩ | hev₂
        · obtain ⟨bty, htyr⟩ := hbty
          have ⟨w₀, hw₀⟩ := @type_is_inhabited_bool env bty
          refine ⟨fun hc => absurd hc ?_,
            w₀, Or.inl ⟨e₂, by simp only [evaluatePred, hev₁, hev₂, Except.bind_ok, Except.bind_err]⟩,
            by rw [htyr]; exact hw₀⟩
          simp only [evaluatePred, hev₁, hev₂, Except.bind_ok, Except.bind_err, reduceCtorEq, not_false_eq_true]
        -- Both operands evaluate to values. Split on the `typeOfHasTag` schema branch.
        clear hbty
        simp only [typeOfHasTag] at hht
        split at hht
        case h_1 heq =>
          -- `some none` ⇒ `.ff`, empty caps.
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht
          obtain ⟨htyeq, hceq⟩ := hht
          subst htyeq; subst hceq
          refine ⟨empty_guarded_capabilities_invariant_pred,
            Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s)), ?_, ?_⟩
          · exact Or.inr (by simp only [evaluatePred, hev₁, hev₂, apply₂, hasTag, Except.bind_ok])
          · subst huidty
            exact pred_no_tags_type_implies_no_tags h₂.instance_of_schema heq
        case h_2 =>
          split at hht
          case isTrue hin =>
            -- cap `.tt`: tag present via the invariant.
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht
            obtain ⟨htyeq, hceq⟩ := hht
            subst htyeq; subst hceq
            refine ⟨empty_guarded_capabilities_invariant_pred,
              Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s)), ?_, ?_⟩
            · exact Or.inr (by simp only [evaluatePred, hev₁, hev₂, apply₂, hasTag, Except.bind_ok])
            · exact pred_mem_capabilities_implies_mem_tags hci hofk₁ hofk₂ hev₁ hev₂ hin
          case isFalse =>
            -- `.anyBool`, singleton tag cap guarded by `hasTag = true`.
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hht
            obtain ⟨htyeq, hceq⟩ := hht
            subst htyeq; subst hceq
            refine ⟨?_, Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s)), ?_, ?_⟩
            · -- guarded: on `hasTag = true`, the singleton is invariant.
              intro hguard
              simp only [evaluatePred, hev₁, hev₂, apply₂, hasTag, Except.bind_ok, Except.ok.injEq,
                Value.prim.injEq, Prim.bool.injEq] at hguard
              exact pred_hasTag_true_implies_cap_inv hofk₁ hofk₂ hev₁ hev₂ hguard
            · exact Or.inr (by simp only [evaluatePred, hev₁, hev₂, apply₂, hasTag, Except.bind_ok])
            · exact bool_is_instance_of_anyBool _
        case h_3 heq =>
          -- `none` ⇒ action-type ⇒ `.ff` (else err, contradicting hht).
          split at hht <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at hht
          obtain ⟨htyeq, hceq⟩ := hht
          subst htyeq; subst hceq
          refine ⟨empty_guarded_capabilities_invariant_pred,
            Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s)), ?_, ?_⟩
          · exact Or.inr (by simp only [evaluatePred, hev₁, hev₂, apply₂, hasTag, Except.bind_ok])
          · subst huidty
            exact pred_no_type_implies_no_tags h₂.instance_of_schema heq
      | _ => simp only [hety₁, hety₂, typeOfBinaryApp, err, reduceCtorEq] at htb
    | _ => simp only [hety₁, typeOfBinaryApp, err, reduceCtorEq] at htb

  -- `getTag`: value is the tag type; the capability branch gives tag-present and
  -- the tag-absent error is admitted via the any-error side. The tag-present
  -- value typing against the schema mirrors `Typechecker/BinaryApp/GetTag.lean`.
  case getTag =>
    simp only [typeOfBinaryApp] at htb
    cases hety₁ : tx₁.typeOf with
    | entity ety₁ =>
      cases hety₂ : tx₂.typeOf with
      | string =>
        simp only [hety₁, hety₂, bind, Except.bind] at htb
        cases hgt : typeOfGetTag ety₁ x₁.toCapKey x₂.toCapKey c₁ env with
        | error e => simp only [hgt, reduceCtorEq] at htb
        | ok p =>
          obtain ⟨tyr, cr⟩ := p
          simp only [hgt, ok, Except.ok.injEq, Prod.mk.injEq] at htb
          obtain ⟨htyeq, hceq⟩ := htb
          subst htyeq; subst hceq
          -- RED (unsolved, no sorry): the getTag value is the schema tag type in
          -- the capability branch, or the tag-absent error on the any-error side;
          -- and `cr = ∅` from `typeOfGetTag`. Both halves left unproven.
          refine ⟨?_, ?_⟩
      | _ => simp only [hety₁, hety₂, typeOfBinaryApp, err, reduceCtorEq] at htb
    | _ => simp only [hety₁, typeOfBinaryApp, err, reduceCtorEq] at htb

end Cedar.Thm
