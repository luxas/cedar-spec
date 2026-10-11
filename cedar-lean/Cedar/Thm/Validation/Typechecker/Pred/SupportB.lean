/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.BinaryApp

/-!
# Support lemmas for the `.mem` / `.hasTag` / `.getTag` predicate arms (Phase 9c, arm B)

Value-side and capability-side facts the `.binaryApp` predicate soundness proof
needs for `op₂ ∈ {.mem, .hasTag, .getTag}`, mirroring the expression-side proofs
in `Typechecker/BinaryApp/{Mem,HasTag,GetTag}.lean` but phrased over
`evaluatePred` / `CapabilitiesInvariantPred` and the capability-key operands
`x₁.toCapKey` / `x₂.toCapKey` (D-97 option b).

The value-side reasoning depends ONLY on the operand VALUES and their static
types (supplied by the operand IHs), never on how the values were produced.

A key structural fact used in the `.mem` set case: `PredExpr` has NO `.set`
constructor, so `PredExpr.toCapKey` can never produce an `Expr.set`, hence
`entityUIDs? x₂.toCapKey = none` for every `x₂ : PredExpr` and the action-literal
`.tt`/`.ff` arm of `typeOfInₛ` is unreachable.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- A capability key is a literal exactly when its predicate is that literal. -/
theorem toCapKey_lit {p : PredExpr} {l : Prim} (h : p.toCapKey = .lit l) : p = .lit l := by
  cases p <;>
    simp only [PredExpr.toCapKey, itCapKey, reduceCtorEq, Expr.lit.injEq] at h ⊢ <;>
    first | (subst h; rfl) | (simp_all)

/-- `PredExpr.toCapKey` never produces an `Expr.set`, so `entityUIDs?` of a
capability key is always `none`. -/
theorem entityUIDs?_toCapKey_none (p : PredExpr) :
    entityUIDs? p.toCapKey = none := by
  cases p <;> simp only [PredExpr.toCapKey, itCapKey, entityUIDs?]

/-! ### `.mem` value lemmas. -/

/--
`.mem` with a single-entity right operand: `apply₂ .mem` yields a bool that
instantiates `.bool (typeOfInₑ …)`. Mirror of the value tail of
`type_of_mem_is_soundₑ`, over `evaluatePred` and the capability-key operands.
The action-literal branch uses `toCapKey_lit` to pull `x₁.toCapKey = .lit
(.entityUID auid)` back to `evaluatePred x₁ it = .ok auid`, forcing `auid =
euid₁`. -/
theorem apply₂_mem_entity_instance_of_inₑ {x₁ x₂ : PredExpr} {it : Value} {euid₁ euid₂ : EntityUID}
    {w : Value} {env : TypeEnv} {ety₁ ety₂ : EntityType} {request : Request} {entities : Entities}
    (hwf : InstanceOfWellFormedEnvironment request entities env)
    (hev₁ : evaluatePred x₁ it request entities = .ok (Value.prim (Prim.entityUID euid₁)))
    (hev₂ : evaluatePred x₂ it request entities = .ok (Value.prim (Prim.entityUID euid₂)))
    (hty₁ : euid₁.ty = ety₁)
    (hty₂ : euid₂.ty = ety₂)
    (happ : apply₂ .mem (Value.prim (Prim.entityUID euid₁)) (Value.prim (Prim.entityUID euid₂)) entities = .ok w) :
    InstanceOfType env w (.bool (typeOfInₑ ety₁ ety₂ x₁.toCapKey x₂.toCapKey env)) := by
  simp only [apply₂, Except.ok.injEq] at happ
  subst happ
  subst hty₁
  subst hty₂
  apply InstanceOfType.instance_of_bool
  simp only [InstanceOfBoolType]
  split <;> try simp only
  rename_i b bty h₇ h₈ h₉
  simp only [typeOfInₑ] at *
  cases hₐ : actionUID? x₁.toCapKey env.acts <;> simp [hₐ] at h₇ h₈ h₉
  case none =>
    exact absurd (h₉ (entity_type_in_false_implies_inₑ_false hwf h₇)) (by simp [h₇])
  case some auid =>
    cases he : entityUID? x₂.toCapKey <;> simp [he] at h₇ h₈ h₉
    case none =>
      exact absurd (h₉ (entity_type_in_false_implies_inₑ_false hwf h₇)) (by simp [h₇])
    case some euid =>
      replace ⟨hₐ, hₐ'⟩ := actionUID?_some_implies_action_lit hₐ
      replace he := entityUID?_some_implies_entity_lit he
      -- `x₁.toCapKey = .lit (.entityUID auid)` ⇒ `x₁ = .lit …` ⇒ `evaluatePred x₁ = auid`.
      have hx₁ := toCapKey_lit hₐ
      have hx₂ := toCapKey_lit he
      subst hx₁ hx₂
      simp only [evaluatePred, Except.ok.injEq, Value.prim.injEq, Prim.entityUID.injEq] at hev₁ hev₂
      subst hev₁ hev₂
      have h₁₀ := action_type_in_eq_action_inₑ auid euid hwf hₐ'
      simp [h₁₀] at h₈ h₉
      cases heq : ActionSchema.descendentOf env.acts auid euid <;> simp [heq] at h₈ h₉

/--
`.mem` with a set right operand. Because `PredExpr` has no `.set`,
`entityUIDs? x₂.toCapKey = none`, so `typeOfInₛ` collapses to its schema
`.anyBool`/`.ff` arm. Mirror of the surviving arm of `type_of_mem_is_soundₛ`. -/
theorem apply₂_mem_set_instance_of_inₛ {x₁ x₂ : PredExpr} {euid₁ : EntityUID}
    {vs : List Value} {w : Value} {env : TypeEnv} {ety₁ ety₂ : EntityType}
    {request : Request} {entities : Entities}
    (hwf : InstanceOfWellFormedEnvironment request entities env)
    (hty₁ : euid₁.ty = ety₁)
    (hvs : InstanceOfType env (Value.set (Set.mk vs)) (CedarType.set (CedarType.entity ety₂)))
    (happ : apply₂ .mem (Value.prim (Prim.entityUID euid₁)) (Value.set (Set.mk vs)) entities = .ok w) :
    InstanceOfType env w (.bool (typeOfInₛ ety₁ ety₂ x₁.toCapKey x₂.toCapKey env)) := by
  simp only [apply₂, inₛ, Set.mapOrErr, Set.elts] at happ
  have ⟨euids, h₇, hty₇⟩ := entity_set_type_implies_set_of_entities hvs
  simp only [h₇, Except.bind_ok, Except.ok.injEq] at happ
  subst happ
  subst hty₁
  apply InstanceOfType.instance_of_bool
  simp only [InstanceOfBoolType]
  split <;> try simp only
  rename_i b bty h₈ h₉ h₁₀
  -- `entityUIDs? x₂.toCapKey = none` kills the action-literal arm of `typeOfInₛ`.
  simp only [typeOfInₛ, entityUIDs?_toCapKey_none] at *
  -- `h₈ : descendentOf = false`; `h₁₀`'s antecedent (pointwise `inₑ = false`) follows
  -- from the inₛ-false fact, giving `descendentOf = true`, contradicting `h₈`.
  have hptwise : ∀ (x : EntityUID), x ∈ euids → inₑ euid₁ x entities = false := by
    cases ha : actionUID? x₁.toCapKey env.acts <;> simp [ha] at h₈ <;>
    · have hany := entity_type_in_false_implies_inₛ_false hwf h₈ hty₇
      rw [Set.any_make, List.any_eq_false] at hany
      intro x hx
      simpa using hany x hx
  cases ha : actionUID? x₁.toCapKey env.acts <;> simp [ha] at h₈ h₉ h₁₀ <;>
  · exact absurd (h₁₀ hptwise) (by simp [h₈])

end Cedar.Thm
