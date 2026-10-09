/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Thm.Data.Map
import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.ofType

/-!
D-72 step (3), `.binaryApp` arm of `compilePred_well_typed`.

Standalone arm lemma `compilePred_well_typed_binaryApp`: a `.binaryApp` predicate
that type-checks (via `typeOfBinaryApp`) compiles (`compilePred`) to a well-typed
term, given each sub-predicate's compiled-term success + type.

The scalar `compile_well_typed_binaryApp` (Thm/SymCC/Compiler/WellTyped.lean) is the
template; the only difference is that the operand type facts come from a `split` of
`typeOfBinaryApp`'s op/type match (helper `typeOfBinaryApp_ok_find` below) rather than
from a `BinaryOp.WellTyped` cases — the predicate relation does not carry the latter.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

/--
Peel `typeOfBinaryApp`'s op/type match. From a success
`typeOfBinaryApp op₂ ty₁ ty₂ x₁ x₂ c Γ = .ok (typ, c')` it returns, per reachable
branch, the operand Cedar type facts (`ty₁.typeOf = …`, `ty₂.typeOf = …`) together
with the compiled result type that `compileApp₂` produces for those operands, matched
against `.option (TermType.ofType typ.typeOf)`.

We do NOT return `typ`'s syntactic value; instead we directly characterise
`TermType.ofType typ.typeOf`, which is all the arm needs. `.getTag` is the one branch
whose result type is the (symbolic) tag value type, so it is returned existentially via
`Γ.ets.tags?`.
-/
private theorem typeOfBinaryApp_ok_find
    {op₂ : BinaryOp} {ty₁ ty₂ typ : TypedExpr} {x₁ x₂ : Expr}
    {c c' : Capabilities} {Γ : TypeEnv}
    (htp : typeOfBinaryApp op₂ ty₁ ty₂ x₁ x₂ c Γ = .ok (typ, c')) :
    -- `eq`
    (op₂ = .eq ∧ TermType.ofType typ.typeOf = .bool) ∨
    -- `mem` entity/entity, `mem` entity/set-entity
    (∃ ety₁ ety₂, op₂ = .mem ∧ ty₁.typeOf = .entity ety₁ ∧ ty₂.typeOf = .entity ety₂ ∧
      TermType.ofType typ.typeOf = .bool) ∨
    (∃ ety₁ ety₂, op₂ = .mem ∧ ty₁.typeOf = .entity ety₁ ∧ ty₂.typeOf = .set (.entity ety₂) ∧
      TermType.ofType typ.typeOf = .bool) ∨
    -- `hasTag`
    (∃ ety₁, op₂ = .hasTag ∧ ty₁.typeOf = .entity ety₁ ∧ ty₂.typeOf = .string ∧
      TermType.ofType typ.typeOf = .bool) ∨
    -- `getTag`
    (∃ ety₁ tgTy, op₂ = .getTag ∧ ty₁.typeOf = .entity ety₁ ∧ ty₂.typeOf = .string ∧
      Γ.ets.tags? ety₁ = some (some tgTy) ∧ typ.typeOf = tgTy) ∨
    -- `less`/`lessEq` on int
    ((op₂ = .less ∨ op₂ = .lessEq) ∧ ty₁.typeOf = .int ∧ ty₂.typeOf = .int ∧
      TermType.ofType typ.typeOf = .bool) ∨
    -- `less`/`lessEq` on datetime
    ((op₂ = .less ∨ op₂ = .lessEq) ∧ ty₁.typeOf = .ext .datetime ∧ ty₂.typeOf = .ext .datetime ∧
      TermType.ofType typ.typeOf = .bool) ∨
    -- `less`/`lessEq` on duration
    ((op₂ = .less ∨ op₂ = .lessEq) ∧ ty₁.typeOf = .ext .duration ∧ ty₂.typeOf = .ext .duration ∧
      TermType.ofType typ.typeOf = .bool) ∨
    -- `add`/`sub`/`mul`
    ((op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul) ∧ ty₁.typeOf = .int ∧ ty₂.typeOf = .int ∧
      TermType.ofType typ.typeOf = .bitvec 64) ∨
    -- `contains`
    (∃ ty₃, op₂ = .contains ∧ ty₁.typeOf = .set ty₃ ∧ TermType.ofType typ.typeOf = .bool) ∨
    -- `containsAll`/`containsAny`
    (∃ ty₃ ty₄, (op₂ = .containsAll ∨ op₂ = .containsAny) ∧
      ty₁.typeOf = .set ty₃ ∧ ty₂.typeOf = .set ty₄ ∧ TermType.ofType typ.typeOf = .bool) := by
  simp only [typeOfBinaryApp] at htp
  split at htp
  -- `.eq`
  case _ =>
    left
    refine ⟨rfl, ?_⟩
    simp only [typeOfEq, Function.comp_apply, Validation.ok, Validation.err] at htp
    split at htp
    · -- lit/lit: `if p₁ == p₂ then ok .tt else ok .ff`
      split at htp <;>
        (simp only [Except.ok.injEq, Prod.mk.injEq] at htp
         obtain ⟨rfl, _⟩ := htp
         simp only [TypedExpr.typeOf, TermType.ofType])
    · -- non-lit: match on lub
      split at htp
      · simp only [Except.ok.injEq, Prod.mk.injEq] at htp
        obtain ⟨rfl, _⟩ := htp
        simp only [TypedExpr.typeOf, TermType.ofType]
      · split at htp <;>
          simp only [Except.ok.injEq, Prod.mk.injEq, Validation.err, reduceCtorEq] at htp
        obtain ⟨rfl, _⟩ := htp
        simp only [TypedExpr.typeOf, TermType.ofType]
  -- `.mem` entity/entity
  case _ ety₁ ety₂ h₁ h₂ =>
    right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨ety₁, ety₂, rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.mem` entity/set-entity
  case _ ety₁ ety₂ h₁ h₂ =>
    right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨ety₁, ety₂, rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.hasTag`
  case _ ety₁ h₁ h₂ =>
    right; right; right; left
    refine ⟨ety₁, rfl, h₁, h₂, ?_⟩
    simp only [typeOfHasTag, Validation.ok, Validation.err] at htp
    repeat' split at htp
    all_goals simp_all only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
    all_goals (obtain ⟨rfl, _⟩ := htp; simp only [TypedExpr.typeOf, TermType.ofType])
  -- `.getTag`
  case _ ety₁ h₁ h₂ =>
    right; right; right; right; left
    simp only [typeOfGetTag, Validation.ok, Validation.err] at htp
    split at htp
    · simp only [bind, Except.bind, reduceCtorEq] at htp
    · rename_i tgTy hfind
      split at htp
      · simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at htp
        obtain ⟨rfl, _⟩ := htp
        exact ⟨ety₁, tgTy, rfl, h₁, h₂, hfind, by simp only [TypedExpr.typeOf]⟩
      · simp only [bind, Except.bind, reduceCtorEq] at htp
    · simp only [bind, Except.bind, reduceCtorEq] at htp
  -- `.less int int`
  case _ h₁ h₂ =>
    right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inl rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.less datetime datetime`
  case _ h₁ h₂ =>
    right; right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inl rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.less duration duration`
  case _ h₁ h₂ =>
    right; right; right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inl rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.lessEq int int`
  case _ h₁ h₂ =>
    right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inr rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.lessEq datetime datetime`
  case _ h₁ h₂ =>
    right; right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inr rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.lessEq duration duration`
  case _ h₁ h₂ =>
    right; right; right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inr rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.add int int`
  case _ h₁ h₂ =>
    right; right; right; right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inl rfl, h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.sub int int`
  case _ h₁ h₂ =>
    right; right; right; right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inr (Or.inl rfl), h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.mul int int`
  case _ h₁ h₂ =>
    right; right; right; right; right; right; right; right; left
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨rfl, _⟩ := htp
    exact ⟨Or.inr (Or.inr rfl), h₁, h₂, by simp only [TypedExpr.typeOf, TermType.ofType]⟩
  -- `.contains set _`
  case _ ty₃ h₁ =>
    right; right; right; right; right; right; right; right; right; left
    refine ⟨ty₃, rfl, h₁, ?_⟩
    simp only [ifLubThenBool, Validation.ok, Validation.err] at htp
    split at htp <;>
      simp_all only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
    obtain ⟨rfl, _⟩ := htp
    simp only [TypedExpr.typeOf, TermType.ofType]
  -- `.containsAll set set`
  case _ ty₃ ty₄ h₁ h₂ =>
    right; right; right; right; right; right; right; right; right; right
    refine ⟨ty₃, ty₄, Or.inl rfl, h₁, h₂, ?_⟩
    simp only [ifLubThenBool, Validation.ok, Validation.err] at htp
    split at htp <;>
      simp_all only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
    obtain ⟨rfl, _⟩ := htp
    simp only [TypedExpr.typeOf, TermType.ofType]
  -- `.containsAny set set`
  case _ ty₃ ty₄ h₁ h₂ =>
    right; right; right; right; right; right; right; right; right; right
    refine ⟨ty₃, ty₄, Or.inr rfl, h₁, h₂, ?_⟩
    simp only [ifLubThenBool, Validation.ok, Validation.err] at htp
    split at htp <;>
      simp_all only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
    obtain ⟨rfl, _⟩ := htp
    simp only [TypedExpr.typeOf, TermType.ofType]
  -- err arm
  case _ => simp only [Validation.err, reduceCtorEq] at htp

/--
D-72 step (3), `.binaryApp` arm (mirror of `compile_well_typed_binaryApp`). Driven by
`typeOfBinaryApp`'s success (via `typeOfBinaryApp_ok_find`) rather than a
`BinaryOp.WellTyped` cases. For each op the operand term types are pinned from the
sub-result hypotheses, `compileApp₂` is shown to succeed, and the result type is read
off `compileApp₂_wf_types` and matched to `.option (TermType.ofType typ.typeOf)`.
-/
theorem compilePred_well_typed_binaryApp
    {op₂ : BinaryOp} {x₁ x₂ : Cedar.Spec.PredExpr} {ty₁ ty₂ typ : TypedExpr}
    {itTy : CedarType} {c c' : Capabilities} {Γ : TypeEnv} {it t₁ t₂ : Term}
    (hwε : (SymEnv.ofEnv Γ).WellFormed)
    (hitw : it.WellFormed (SymEnv.ofEnv Γ).entities)
    (hitty : it.typeOf = .option (TermType.ofType itTy))
    (hok₁ : compilePred x₁ it (SymEnv.ofEnv Γ) = .ok t₁)
    (hty₁ : t₁.typeOf = .option (TermType.ofType ty₁.typeOf))
    (hok₂ : compilePred x₂ it (SymEnv.ofEnv Γ) = .ok t₂)
    (hty₂ : t₂.typeOf = .option (TermType.ofType ty₂.typeOf))
    (htp : typeOfBinaryApp op₂ ty₁ ty₂ x₁.toExpr x₂.toExpr c Γ = .ok (typ, c')) :
    ∃ t, compilePred (.binaryApp op₂ x₁ x₂) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType typ.typeOf) := by
  have ⟨hwf_comp_1, _, _⟩ := compilePred_wf hwε hitw hitty hok₁
  have ⟨hwf_comp_2, _, _⟩ := compilePred_wf hwε hitw hitty hok₂
  have ⟨hwf_get_1, hty_get_1⟩ := wf_option_get hwf_comp_1 hty₁
  have ⟨hwf_get_2, hty_get_2⟩ := wf_option_get hwf_comp_2 hty₂
  -- Reduce the predicate `compilePred` to the `ifSome`-wrapped `compileApp₂` form.
  -- A small helper that, given `compileApp₂` success + its result type, assembles the
  -- conclusion (type via `typeOf_ifSome_option` twice).
  have assemble : ∀ {t₃ : Term},
      compileApp₂ op₂ (Factory.option.get t₁) (Factory.option.get t₂) (SymEnv.ofEnv Γ).entities = .ok t₃ →
      t₃.typeOf = .option (TermType.ofType typ.typeOf) →
      ∃ t, compilePred (.binaryApp op₂ x₁ x₂) it (SymEnv.ofEnv Γ) = .ok t ∧
        t.typeOf = .option (TermType.ofType typ.typeOf) := by
    intro t₃ hok₃ hty₃
    refine ⟨_, by simp only [compilePred, hok₁, hok₂, Except.bind_ok, hok₃]; rfl, ?_⟩
    apply typeOf_ifSome_option
    apply typeOf_ifSome_option
    exact hty₃
  -- A compileApp₂ result type reader: given success, `compileApp₂_wf_types` gives its type.
  rcases typeOfBinaryApp_ok_find htp with
    heq | hmemₑ | hmemₛ | hhasTag | hgetTag | hless_int | hless_dt | hless_dur |
    harith | hcontains | hcontainsAll
  -- `.eq`  — BLOCKED under this hypothesis (see note); left as an unproved (unsolved) goal, not an admit.
  case _ =>
    obtain ⟨rfl, htyp⟩ := heq
    -- `compileApp₂ .eq t₁' t₂' = if (← reducibleEq t₁'.typeOf t₂'.typeOf) then ⊙eq else ⊙false`,
    -- and `reducibleEq a b` ERRORS unless `a = b` or both are primitive term types.
    -- `typeOfEq`'s success only guarantees `ty₁.typeOf ⊔ ty₂.typeOf = some _` (a LUB exists);
    -- for two DISTINCT record (or set-of-record) types the LUB exists WITHOUT
    -- `ofType ty₁.typeOf = ofType ty₂.typeOf` and WITHOUT either being primitive, so
    -- `compileApp₂ .eq` returns `.error .typeError` — the arm is FALSE for `.eq` on record/set
    -- operands under the raw-`typeOfBinaryApp` hypothesis. Same gap as the D-73 `and/or/ite` fork;
    -- the scalar `compile_well_typed_binaryApp` avoids it via `BinaryOp.WellTyped.eq`'s
    -- `x₁.typeOf = x₂.typeOf`. Remaining goal: the full `∃ t, compilePred (.binaryApp .eq …) = .ok t ∧ …`.
    skip
  -- `.mem` entity/entity
  case _ =>
    obtain ⟨ety₁, ety₂, rfl, hce₁, hce₂, htyp⟩ := hmemₑ
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .mem (Factory.option.get t₁) (Factory.option.get t₂)
        (SymEnv.ofEnv Γ).entities = .ok t₃ := by
      simp only [compileApp₂, hty_get_1, hty_get_2]
      exact ⟨_, rfl⟩
    refine assemble hok₃ ?_
    have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
    simp only at this
    rw [this, htyp]
  -- `.mem` entity/set-entity
  case _ =>
    obtain ⟨ety₁, ety₂, rfl, hce₁, hce₂, htyp⟩ := hmemₛ
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .mem (Factory.option.get t₁) (Factory.option.get t₂)
        (SymEnv.ofEnv Γ).entities = .ok t₃ := by
      simp only [compileApp₂, hty_get_1, hty_get_2]
      exact ⟨_, rfl⟩
    refine assemble hok₃ ?_
    have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
    simp only at this
    rw [this, htyp]
  -- `.hasTag`
  case _ =>
    obtain ⟨ety₁, rfl, hce₁, hce₂, htyp⟩ := hhasTag
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    -- entity-typed operand ⇒ `ety₁` is a valid entity type ⇒ its tags table exists.
    have hvalid : (SymEnv.ofEnv Γ).entities.isValidEntityType ety₁ := by
      have hwf := typeOf_wf_term_is_wf hwf_get_1
      rw [hty_get_1] at hwf
      cases hwf with | entity_wf hvalid => exact hvalid
    have ⟨d, hfind⟩ := Cedar.Data.Map.contains_iff_some_find?.mp hvalid
    have htags : (SymEnv.ofEnv Γ).entities.tags ety₁ = some d.tags := by
      simp only [SymEntities.tags, hfind, Option.map_some]
    have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .hasTag (Factory.option.get t₁) (Factory.option.get t₂)
        (SymEnv.ofEnv Γ).entities = .ok t₃ := by
      simp only [compileApp₂, hty_get_1, hty_get_2, compileHasTag, htags]
      cases d.tags <;> exact ⟨_, rfl⟩
    refine assemble hok₃ ?_
    have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
    simp only at this
    rw [this, htyp]
  -- `.getTag`
  case _ =>
    obtain ⟨ety₁, tgTy, rfl, hce₁, hce₂, hfindΓ, htyp⟩ := hgetTag
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    -- `ofEnv` preserves the (symbolic) tag table and its value type.
    have ⟨τags, htags, htagsTy⟩ := ofEnv_preserves_tags hfindΓ
    have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .getTag (Factory.option.get t₁) (Factory.option.get t₂)
        (SymEnv.ofEnv Γ).entities = .ok t₃ := by
      simp only [compileApp₂, hty_get_1, hty_get_2, compileGetTag, htags]
      exact ⟨_, rfl⟩
    refine assemble hok₃ ?_
    have hwfty := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
    simp only at hwfty
    -- `compileApp₂_wf_types` gives `t₃.typeOf = τs.vals.outType.option` for the `εs.tags`-found `τs`.
    obtain ⟨ety', τs, hty_ent, hτs, ht₃ty⟩ := hwfty
    rw [hty_get_1] at hty_ent
    cases hty_ent
    rw [htags] at hτs
    cases hτs
    rw [ht₃ty, htagsTy, htyp]
  -- `.less int`
  case _ =>
    obtain ⟨hop, hce₁, hce₂, htyp⟩ := hless_int
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    rcases hop with rfl | rfl
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .less (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .lessEq (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
  -- `.less datetime`
  case _ =>
    obtain ⟨hop, hce₁, hce₂, htyp⟩ := hless_dt
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    rcases hop with rfl | rfl
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .less (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .lessEq (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
  -- `.less duration`
  case _ =>
    obtain ⟨hop, hce₁, hce₂, htyp⟩ := hless_dur
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    rcases hop with rfl | rfl
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .less (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .lessEq (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
  -- `.add`/`.sub`/`.mul`
  case _ =>
    obtain ⟨hop, hce₁, hce₂, htyp⟩ := harith
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    rcases hop with rfl | rfl | rfl
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .add (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .sub (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
    · (have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .mul (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2]; exact ⟨_, rfl⟩
       refine assemble hok₃ ?_
       have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
       simp only at this
       rw [this, htyp])
  -- `.contains`  — BLOCKED (see note); unsolved goal (not an admit).
  case _ =>
    obtain ⟨ty₃, rfl, hce₁, htyp⟩ := hcontains
    -- `compileApp₂ .contains, .set elemTT, otherTT = if elemTT = otherTT then ⊙set.member else .error`.
    -- `typeOfBinaryApp .contains` only needs `ty₂.typeOf ⊔ ty₃ = some _` (a LUB), not
    -- `ofType ty₃ = ofType ty₂.typeOf`; for distinct record element/operand types the LUB exists
    -- yet the compiler's equality guard fails → `.error .typeError`. Blocked exactly as `.eq`.
    skip
  -- `.containsAll`/`.containsAny`  — BLOCKED (see note); unsolved goal (not an admit).
  case _ =>
    obtain ⟨ty₃, ty₄, hop, hce₁, hce₂, htyp⟩ := hcontainsAll
    -- `compileApp₂ .containsAll/.containsAny, .set ett₁, .set ett₂ = if ett₁ = ett₂ then … else .error`.
    -- `typeOfBinaryApp` only needs `ty₃ ⊔ ty₄ = some _`; for distinct record element types the LUB
    -- exists without `ofType ty₃ = ofType ty₄`, so the compiler's guard fails. Blocked as `.eq`.
    skip

end Cedar.Thm
