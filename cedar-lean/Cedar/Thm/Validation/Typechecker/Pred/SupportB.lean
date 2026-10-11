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

/-! ### `.hasTag` helpers (predicate versions of the `HasTag.lean` privates). -/

private theorem pred_map_empty_contains_instance_of_ff [DecidableEq α] [DecidableEq β] {k : α} {env : TypeEnv} :
    InstanceOfType env (Value.prim (Prim.bool ((Map.empty : Map α β).contains k))) (CedarType.bool BoolType.ff) := by
  simp only [Map.not_contains_of_empty, false_is_instance_of_ff]

/-- Schema says the entity type has NO tags (`some none`) ⇒ `hasTag` yields a
`.ff`-typed bool. Port of `HasTag.lean`'s `no_tags_type_implies_no_tags`. -/
theorem pred_no_tags_type_implies_no_tags {uid : EntityUID} {env : TypeEnv} {entities : Entities} {s : String}
    (h₁ : InstanceOfSchema entities env)
    (h₂ : env.ets.tags? uid.ty = .some .none) :
    InstanceOfType env (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.ff) := by
  simp only [Entities.tagsOrEmpty]
  split
  · rename_i d hf
    cases h₁.1 uid d hf with
    | inl h₁ =>
      replace ⟨e, hf', _, _, h₁⟩ := h₁
      simp only [InstanceOfEntityTags] at h₁
      simp only [EntitySchema.tags?, Option.map_eq_some_iff] at h₂
      replace ⟨e', h₂, h₃⟩ := h₂
      simp only [hf', Option.some.injEq] at h₂
      subst h₂
      simp only [EntitySchemaEntry.tags?] at h₁ h₃
      split at h₃
      · simp only [h₃] at h₁
        simp only [h₁, pred_map_empty_contains_instance_of_ff]
      · simp only [h₁, pred_map_empty_contains_instance_of_ff]
    | inr h₁ =>
      replace ⟨_, h₁, ⟨e, _⟩⟩ := h₁
      simp only [h₁, Map.empty, Map.contains, Map.find?, Map.toList, List.find?, Option.isSome]
      constructor
      constructor
  · exact pred_map_empty_contains_instance_of_ff

/-- Schema does not know the entity type (`none`) but it is an action type ⇒
`hasTag` yields a `.ff`-typed bool. Port of `no_type_implies_no_tags`. -/
theorem pred_no_type_implies_no_tags {uid : EntityUID} {env : TypeEnv} {entities : Entities} {s : String}
    (h₁ : InstanceOfSchema entities env)
    (h₂ : env.ets.tags? uid.ty = .none) :
    InstanceOfType env (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.ff) := by
  simp only [Entities.tagsOrEmpty]
  split
  · rename_i d hf
    cases h₁.1 uid d hf with
    | inl h₁ =>
      replace ⟨e, h₁, _, _, _⟩ := h₁
      simp only [EntitySchema.tags?, Option.map_eq_none_iff] at h₂
      simp only [h₁, reduceCtorEq] at h₂
    | inr h₁ =>
      replace ⟨_, h₁, ⟨e, _⟩⟩ := h₁
      simp only [h₁, Map.empty, Map.contains, Map.find?, Map.toList, List.find?, Option.isSome]
      constructor
      constructor
  · exact pred_map_empty_contains_instance_of_ff

/-- Capability `.tag` ∈ caps ⇒ the tag IS present (`contains = true`), so a
`.tt`-typed bool. Predicate version using `CapabilitiesInvariantPred.right` over
`evaluatePred` and the capability-key form. `hofk₁`/`hofk₂` are the
`ofCapKey (toCapKey) = id` facts for the two operands. -/
theorem pred_mem_capabilities_implies_mem_tags {env : TypeEnv} {x₁ x₂ : PredExpr} {c₁ : Capabilities}
    {it : Value} {request : Request} {entities : Entities} {uid : EntityUID} {s : String}
    (h₁ : CapabilitiesInvariantPred c₁ it request entities)
    (hofk₁ : PredExpr.ofCapKey x₁.toCapKey = x₁)
    (hofk₂ : PredExpr.ofCapKey x₂.toCapKey = x₂)
    (ih₁ : evaluatePred x₁ it request entities = Except.ok (Value.prim (Prim.entityUID uid)))
    (ih₂ : evaluatePred x₂ it request entities = Except.ok (Value.prim (Prim.string s)))
    (hin : (x₁.toCapKey, Key.tag x₂.toCapKey) ∈ c₁) :
    InstanceOfType env (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.tt) := by
  replace h₁ := h₁.right x₁.toCapKey x₂.toCapKey hin
  rw [hofk₁, hofk₂] at h₁
  simp only [EvaluatesToPred, evaluatePred, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, Except.ok.injEq,
    Value.prim.injEq, Prim.bool.injEq, reduceCtorEq, exists_false, false_or] at h₁
  simp only [h₁, true_is_instance_of_tt]

/-- `hasTag = true` ⇒ the produced singleton `.tag` capability is predicate-invariant.
Predicate version of `hasTag_true_implies_cap_inv`. -/
theorem pred_hasTag_true_implies_cap_inv {x₁ x₂ : PredExpr} {it : Value} {request : Request}
    {entities : Entities} {uid : EntityUID} {s : String}
    (hofk₁ : PredExpr.ofCapKey x₁.toCapKey = x₁)
    (hofk₂ : PredExpr.ofCapKey x₂.toCapKey = x₂)
    (ih₁ : evaluatePred x₁ it request entities = Except.ok (Value.prim (Prim.entityUID uid)))
    (ih₂ : evaluatePred x₂ it request entities = Except.ok (Value.prim (Prim.string s)))
    (ht : (entities.tagsOrEmpty uid).contains s = true) :
    CapabilitiesInvariantPred (Capabilities.singleton x₁.toCapKey (Key.tag x₂.toCapKey)) it request entities := by
  constructor <;>
  intro e k hin <;>
  simp only [Capabilities.singleton, List.mem_singleton, Prod.mk.injEq, and_false, Key.tag.injEq, reduceCtorEq] at hin
  replace ⟨hin, hin'⟩ := hin
  subst hin hin'
  rw [hofk₁, hofk₂]
  simp only [EvaluatesToPred, evaluatePred, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, ht, or_true]

end Cedar.Thm
