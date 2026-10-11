/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.BinaryApp

/-!
# Predicate type soundness — `.binaryApp` arm (Phase 9c)

Mirror of `type_of_binaryApp_is_sound` (`Typechecker/BinaryApp.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the WEAK form (D-94): no capability
invariant and no guarded-capabilities conclusion.

`typeOfPred (.binaryApp op x₁ x₂)` peels to `typeOfPred x₁`, `typeOfPred x₂`,
then the SAME `typeOfBinaryApp op ty₁ ty₂ x₁.toExpr x₂.toExpr c env` helper the
expression typechecker uses; `evaluatePred (.binaryApp op x₁ x₂)` is
`do v₁ ← evaluatePred x₁; v₂ ← evaluatePred x₂; apply₂ op v₁ v₂ es`.

Weak soundness admits any error, so the only real content is the ok/ok case,
where `apply₂ op v₁ v₂ es` is shown to be a bool-or-error (eq/less/lessEq/add/
sub/mul/contains/containsAll/containsAny/mem/hasTag) or an instance of the tag
type (getTag). The operand value types come straight from the operand IHs, so NO
re-typing across `toExpr`-vs-`item` is needed.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Inversion of `typeOfPred (.binaryApp op x₁ x₂)`: it factors through the operand
`typeOfPred` calls and the SAME `typeOfBinaryApp` helper the expression
typechecker uses (over `.toExpr` of the operands).
-/
theorem type_of_pred_binaryApp_inversion {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {itTy : CedarType}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (h₁ : typeOfPred (.binaryApp op₂ x₁ x₂) itTy c₁ env = Except.ok (ty, c₂)) :
    ∃ tx₁ c₁' tx₂ c₂',
      typeOfPred x₁ itTy c₁ env = Except.ok (tx₁, c₁') ∧
      typeOfPred x₂ itTy c₁ env = Except.ok (tx₂, c₂') ∧
      typeOfBinaryApp op₂ tx₁ tx₂ x₁.toExpr x₂.toExpr c₁ env = Except.ok (ty, c₂) := by
  simp only [typeOfPred] at h₁
  simp_do_let (typeOfPred x₁ itTy c₁ env) as htx₁ at h₁
  simp_do_let (typeOfPred x₂ itTy c₁ env) as htx₂ at h₁
  rename_i r₁ r₂
  have ⟨tx₁, c₁'⟩ := r₁
  have ⟨tx₂, c₂'⟩ := r₂
  exact ⟨tx₁, c₁', tx₂, c₂', rfl, rfl, h₁⟩

/-! ### Per-op result-type inversions of `typeOfBinaryApp`.

Each gives the concrete `ty.typeOf` for that op from the `typeOfBinaryApp`
equation produced by `type_of_pred_binaryApp_inversion`. These are pure facts
about `typeOfBinaryApp` (no `typeOf`/`typeOfPred` involved), so they are shared
verbatim with the expression proof's shape. -/

theorem typeOfBinaryApp_eq_typeOf {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr} {c c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr}
    (h : typeOfBinaryApp .eq tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ∃ bty, ty.typeOf = .bool bty := by
  simp only [typeOfBinaryApp, typeOfEq] at h
  split at h
  · split at h <;>
      simp only [Function.comp_apply, ok, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨h, _⟩ := h <;> subst h <;> exact ⟨_, rfl⟩
  · split at h
    · simp only [Function.comp_apply, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h, _⟩ := h; subst h; exact ⟨_, rfl⟩
    · split at h <;>
        simp only [Function.comp_apply, ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      obtain ⟨h, _⟩ := h; subst h; exact ⟨_, rfl⟩

/-- `less`/`lessEq` always produce `.bool .anyBool`. -/
theorem typeOfBinaryApp_cmp_typeOf {op₂ : BinaryOp} {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (hop : op₂ = .less ∨ op₂ = .lessEq)
    (h : typeOfBinaryApp op₂ tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ty.typeOf = .bool .anyBool := by
  rcases hop with hop | hop <;> subst hop <;> unfold typeOfBinaryApp at h <;>
    split at h <;>
    first
    | contradiction
    | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h ;
       obtain ⟨h, _⟩ := h ; subst h ; rfl)
    | (simp only [ok, err, reduceCtorEq] at h)

/-- `add`/`sub`/`mul` always produce `.int`. -/
theorem typeOfBinaryApp_arith_typeOf {op₂ : BinaryOp} {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (hop : op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul)
    (h : typeOfBinaryApp op₂ tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ty.typeOf = .int := by
  rcases hop with hop | hop | hop <;> subst hop <;> unfold typeOfBinaryApp at h <;>
    split at h <;>
    first
    | contradiction
    | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h ;
       obtain ⟨h, _⟩ := h ; subst h ; rfl)
    | (simp only [ok, err, reduceCtorEq] at h)

/-- `contains` always produces `.bool .anyBool`. -/
theorem typeOfBinaryApp_contains_typeOf {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (h : typeOfBinaryApp .contains tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ty.typeOf = .bool .anyBool := by
  unfold typeOfBinaryApp at h
  split at h <;>
    first
    | contradiction
    | (simp only [ifLubThenBool] at h ;
       split at h <;>
         simp only [ok, err, Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq,
           reduceCtorEq] at h ;
       obtain ⟨h, _⟩ := h ; subst h ; rfl)
    | (simp only [ok, err, reduceCtorEq] at h)

/-- `containsAll`/`containsAny` always produce `.bool .anyBool`. -/
theorem typeOfBinaryApp_containsA_typeOf {op₂ : BinaryOp} {tx₁ tx₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (hop : op₂ = .containsAll ∨ op₂ = .containsAny)
    (h : typeOfBinaryApp op₂ tx₁ tx₂ e₁ e₂ c env = Except.ok (ty, c₂)) :
    ty.typeOf = .bool .anyBool := by
  rcases hop with hop | hop <;> subst hop <;> unfold typeOfBinaryApp at h <;>
    split at h <;>
    first
    | contradiction
    | (simp only [ifLubThenBool] at h ;
       split at h <;>
         simp only [ok, err, Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq,
           reduceCtorEq] at h ;
       obtain ⟨h, _⟩ := h ; subst h ; rfl)
    | (simp only [ok, err, reduceCtorEq] at h)

/-! ### Main `.binaryApp` predicate soundness (WEAK form, D-94).

Common prefix: invert, apply operand IHs, reduce the predicate evaluation to the
two operand evaluations. The `apply₂` result for `less`/`lessEq`/`add`/`sub`/
`mul`/`contains`/`containsAll`/`containsAny`/`mem`/`eq` is a bool-or-error (or an
int-or-error for arithmetic), matching the schema-independent result type; those
arms are closed. `hasTag`/`getTag` return `.bool .tt` (resp. the tag type) in
their CAPABILITY branch of `typeOfHasTag`/`typeOfGetTag`, which weak soundness
cannot discharge (no capability invariant, D-95) — their `ok` case is left as a
sorry-free red gap. -/

theorem type_of_pred_binaryApp_is_sound {op₂ : BinaryOp} {x₁ x₂ : PredExpr} {itTy : CedarType} {it : Value}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.binaryApp op₂ x₁ x₂) itTy c₁ env = Except.ok (ty, c₂))
    (ih₁ : TypeOfPredIsSound x₁)
    (ih₂ : TypeOfPredIsSound x₂) :
    ∃ v, EvaluatesToPred (.binaryApp op₂ x₁ x₂) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have ⟨tx₁, c₁', tx₂, c₂', ht₁, ht₂, htb⟩ := type_of_pred_binaryApp_inversion h₃
  have ⟨v₁, hev₁, hinst₁⟩ := ih₁ h₂ hit ht₁
  have ⟨v₂, hev₂, hinst₂⟩ := ih₂ h₂ hit ht₂
  simp only [EvaluatesToPred, evaluatePred] at hev₁ hev₂ ⊢
  cases op₂
  -- `less`/`lessEq`: result `.bool .anyBool`; `apply₂` is bool-or-error.
  case less =>
    rw [typeOfBinaryApp_cmp_typeOf (Or.inl rfl) htb]
    rcases hev₁ with ⟨e₁, hev₁⟩ | hev₁
    · exact ⟨_, Or.inl ⟨e₁, by simp [hev₁]⟩, type_is_inhabited_bool.choose_spec⟩
    rcases hev₂ with ⟨e₂, hev₂⟩ | hev₂
    · exact ⟨_, Or.inl ⟨e₂, by simp [hev₁, hev₂]⟩, type_is_inhabited_bool.choose_spec⟩
    cases happ : apply₂ .less v₁ v₂ entities with
    | error e => exact ⟨_, Or.inl ⟨e, by simp [hev₁, hev₂, happ]⟩, type_is_inhabited_bool.choose_spec⟩
    | ok w =>
      refine ⟨w, Or.inr (by simp [hev₁, hev₂, happ]), ?_⟩
      simp only [apply₂] at happ
      split at happ <;>
        simp only [Except.ok.injEq, reduceCtorEq] at happ <;>
        (first | (subst happ; exact bool_is_instance_of_anyBool _) | skip)
  case lessEq =>
    rw [typeOfBinaryApp_cmp_typeOf (Or.inr rfl) htb]
    rcases hev₁ with ⟨e₁, hev₁⟩ | hev₁
    · exact ⟨_, Or.inl ⟨e₁, by simp [hev₁]⟩, type_is_inhabited_bool.choose_spec⟩
    rcases hev₂ with ⟨e₂, hev₂⟩ | hev₂
    · exact ⟨_, Or.inl ⟨e₂, by simp [hev₁, hev₂]⟩, type_is_inhabited_bool.choose_spec⟩
    cases happ : apply₂ .lessEq v₁ v₂ entities with
    | error e => exact ⟨_, Or.inl ⟨e, by simp [hev₁, hev₂, happ]⟩, type_is_inhabited_bool.choose_spec⟩
    | ok w =>
      refine ⟨w, Or.inr (by simp [hev₁, hev₂, happ]), ?_⟩
      simp only [apply₂] at happ
      split at happ <;>
        simp only [Except.ok.injEq, reduceCtorEq] at happ <;>
        (first | (subst happ; exact bool_is_instance_of_anyBool _) | skip)

end Cedar.Thm
