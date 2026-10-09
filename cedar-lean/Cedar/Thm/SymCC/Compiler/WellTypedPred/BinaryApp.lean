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

end Cedar.Thm
