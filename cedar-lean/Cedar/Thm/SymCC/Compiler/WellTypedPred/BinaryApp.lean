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
import Cedar.Thm.WellTyped.Expr.TypeLifting

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

/- Twins of the private `ofType`-vs-`liftBoolTypes` lemmas in
   `Cedar/Thm/SymCC/Compiler/WellTyped.lean` (that file is currently unimportable — its
   `compilePred_well_typed` dispatcher is red). Copied verbatim as `private` twins. -/
mutual
  private theorem ofQualifiedType_eq_ofQualifiedType_liftBool' {qty : QualifiedType} :
      TermType.ofQualifiedType qty = TermType.ofQualifiedType qty.liftBoolTypes := by
    cases qty
    all_goals
      simp only [TermType.ofQualifiedType, QualifiedType.liftBoolTypes, TermType.option.injEq]
      apply ofType_eq_ofType_liftBool'
  private theorem ofRecordType_eq_ofRecordType_liftBool' (recs : List (Attr × QualifiedType)) :
      TermType.ofRecordType recs =
      TermType.ofRecordType (recs.map (λ (k, v) => (k, QualifiedType.liftBoolTypes v))) := by
    cases recs with
    | nil => simp [TermType.ofRecordType]
    | cons hd tail =>
      simp only [List.map, TermType.ofRecordType, List.cons.injEq]
      constructor
      · simp only [Prod.mk.injEq, true_and]
        apply ofQualifiedType_eq_ofQualifiedType_liftBool'
      · apply ofRecordType_eq_ofRecordType_liftBool' tail
  private theorem ofType_eq_ofType_liftBool' (ty : CedarType) :
      TermType.ofType ty = TermType.ofType ty.liftBoolTypes := by
    cases ty with
    | bool _ => simp [TermType.ofType, CedarType.liftBoolTypes]
    | int => simp [TermType.ofType, CedarType.liftBoolTypes]
    | string => simp [TermType.ofType, CedarType.liftBoolTypes]
    | entity ety => simp [TermType.ofType, CedarType.liftBoolTypes]
    | ext xty => simp [TermType.ofType, CedarType.liftBoolTypes]
    | set ty =>
      simp [TermType.ofType, CedarType.liftBoolTypes]
      apply ofType_eq_ofType_liftBool' ty
    | record rty =>
      simp only [TermType.ofType, CedarType.liftBoolTypes, RecordType.liftBoolTypes,
        Data.Map.mapOnValues₂_eq_mapOnValues, Data.Map.mapOnValues,
        TermType.record.injEq, Data.Map.mk.injEq]
      exact ofRecordType_eq_ofRecordType_liftBool' rty.toList
end

/--
If two Cedar types have a LUB, their `TermType.ofType` images are equal. (`lubRecordType`
requires identical keys + matching qualifiers, so the only lub-without-equality freedom is
Bool annotations, which `ofType` collapses: `lifted_type_lub` + `ofType_eq_ofType_liftBool'`.)
This is exactly the operand type-equality `compileApp₂`'s eq/contains guards require.
-/
private theorem lub_implies_ofType_eq {ty₁ ty₂ ty : CedarType}
    (h : (ty₁ ⊔ ty₂) = .some ty) :
    TermType.ofType ty₁ = TermType.ofType ty₂ := by
  have hlift := lifted_type_lub h
  rw [ofType_eq_ofType_liftBool' ty₁, ofType_eq_ofType_liftBool' ty₂, hlift]

/--
`compilePred` of a literal yields a primitive-typed `option` term, so `option.get` of it is
primitive. Used to discharge `reducibleEq`'s "both primitive" case for `.eq` of two literals
(where `typeOfEq` does not constrain the operand types but the operands are prims).
-/
private theorem compilePred_lit_option_get_isPrim {p : Prim} {it t : Term} {εnv : SymEnv}
    (hok : compilePred (.lit p) it εnv = .ok t) :
    (Factory.option.get t).typeOf.isPrimType = true := by
  cases p with
  | bool b =>
    simp only [compilePred, compilePrim, Factory.someOf, Except.ok.injEq] at hok; subst hok
    simp only [pe_option_get_some]; exact typeOf_term_prim_isPrimType _
  | int i =>
    simp only [compilePred, compilePrim, Factory.someOf, Except.ok.injEq] at hok; subst hok
    simp only [pe_option_get_some]; exact typeOf_term_prim_isPrimType _
  | string s =>
    simp only [compilePred, compilePrim, Factory.someOf, Except.ok.injEq] at hok; subst hok
    simp only [pe_option_get_some]; exact typeOf_term_prim_isPrimType _
  | entityUID uid =>
    simp only [compilePred, compilePrim] at hok
    split at hok <;> simp only [Factory.someOf, Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    simp only [pe_option_get_some]; exact typeOf_term_prim_isPrimType _

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
    (op₂ = .eq ∧
      ((∃ p₁ p₂, x₁ = .lit p₁ ∧ x₂ = .lit p₂) ∨
        (∃ b, reducibleEq (TermType.ofType ty₁.typeOf) (TermType.ofType ty₂.typeOf) = .ok b)) ∧
      TermType.ofType typ.typeOf = .bool) ∨
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
    (∃ ty₃, op₂ = .contains ∧ ty₁.typeOf = .set ty₃ ∧
      TermType.ofType ty₂.typeOf = TermType.ofType ty₃ ∧ TermType.ofType typ.typeOf = .bool) ∨
    -- `containsAll`/`containsAny`
    (∃ ty₃ ty₄, (op₂ = .containsAll ∨ op₂ = .containsAny) ∧
      ty₁.typeOf = .set ty₃ ∧ ty₂.typeOf = .set ty₄ ∧ TermType.ofType ty₃ = TermType.ofType ty₄ ∧
      TermType.ofType typ.typeOf = .bool) := by
  simp only [typeOfBinaryApp] at htp
  split at htp
  -- `.eq`
  case _ =>
    left
    refine ⟨rfl, ?_, ?_⟩
    · -- lit/lit discriminant (left) OR `reducibleEq`-ok (right).
      simp only [typeOfEq, Function.comp_apply, Validation.ok, Validation.err] at htp
      split at htp
      · -- lit/lit
        rename_i p₁ p₂
        exact Or.inl ⟨p₁, p₂, rfl, rfl⟩
      · -- non-lit: lub some ⇒ `ofType` equal ⇒ reducibleEq .ok true;
        -- lub none ⇒ both entity ⇒ both prim ⇒ reducibleEq .ok false.
        right
        split at htp
        · rename_i hlub
          have heqty := lub_implies_ofType_eq hlub
          exact ⟨true, by simp only [reducibleEq, heqty, if_true]⟩
        · split at htp
          · -- entity/entity: both `ofType` are prim ⇒ reducibleEq succeeds (.ok true/false).
            rename_i hent₁ hent₂
            simp only [reducibleEq, hent₁, hent₂, TermType.ofType, TermType.isPrimType,
              Bool.and_self]
            split
            · exact ⟨true, rfl⟩
            · exact ⟨false, rfl⟩
          · simp only [Validation.err, reduceCtorEq] at htp
    · -- result type is `.bool`
      simp only [typeOfEq, Function.comp_apply, Validation.ok, Validation.err] at htp
      split at htp
      · split at htp <;>
          (simp only [Except.ok.injEq, Prod.mk.injEq] at htp
           obtain ⟨rfl, _⟩ := htp
           simp only [TypedExpr.typeOf, TermType.ofType])
      · split at htp
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
    refine ⟨ty₃, rfl, h₁, ?_, ?_⟩
    · -- `ifLubThenBool ty₂.typeOf ty₃` succeeded ⇒ lub exists ⇒ `ofType` equal.
      simp only [ifLubThenBool] at htp
      split at htp
      · rename_i hlub; exact lub_implies_ofType_eq hlub
      · simp only [Validation.err, bind, Except.bind, reduceCtorEq] at htp
    · simp only [ifLubThenBool, Validation.ok, Validation.err] at htp
      split at htp <;>
        simp_all only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
      obtain ⟨rfl, _⟩ := htp
      simp only [TypedExpr.typeOf, TermType.ofType]
  -- `.containsAll set set`
  case _ ty₃ ty₄ h₁ h₂ =>
    right; right; right; right; right; right; right; right; right; right
    refine ⟨ty₃, ty₄, Or.inl rfl, h₁, h₂, ?_, ?_⟩
    · simp only [ifLubThenBool] at htp
      split at htp
      · rename_i hlub; exact lub_implies_ofType_eq hlub
      · simp only [Validation.err, bind, Except.bind, reduceCtorEq] at htp
    · simp only [ifLubThenBool, Validation.ok, Validation.err] at htp
      split at htp <;>
        simp_all only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
      obtain ⟨rfl, _⟩ := htp
      simp only [TypedExpr.typeOf, TermType.ofType]
  -- `.containsAny set set`
  case _ ty₃ ty₄ h₁ h₂ =>
    right; right; right; right; right; right; right; right; right; right
    refine ⟨ty₃, ty₄, Or.inr rfl, h₁, h₂, ?_, ?_⟩
    · simp only [ifLubThenBool] at htp
      split at htp
      · rename_i hlub; exact lub_implies_ofType_eq hlub
      · simp only [Validation.err, bind, Except.bind, reduceCtorEq] at htp
    · simp only [ifLubThenBool, Validation.ok, Validation.err] at htp
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
  -- `.eq`
  case _ =>
    obtain ⟨rfl, hdisc, htyp⟩ := heq
    -- `compileApp₂ .eq t₁' t₂' = if (← reducibleEq t₁'.typeOf t₂'.typeOf) then ⊙eq else ⊙false`.
    -- `reducibleEq` succeeds here: either the operands' `ofType`s are equal/both-prim (non-lit
    -- case, via the LUB), or both operands are literals (⇒ primitive compiled term types).
    have hre : ∃ b, reducibleEq (Factory.option.get t₁).typeOf (Factory.option.get t₂).typeOf
        = .ok b := by
      rw [hty_get_1, hty_get_2]
      rcases hdisc with ⟨p₁, p₂, hx₁, hx₂⟩ | hb
      · -- both operands are literals: `compilePred (.lit _)` ⇒ primitive compiled type.
        have hx₁' : x₁ = .lit p₁ := by
          cases x₁ <;> simp_all only [PredExpr.toExpr, itExpr, reduceCtorEq, Expr.lit.injEq,
            PredExpr.lit.injEq]
        have hx₂' : x₂ = .lit p₂ := by
          cases x₂ <;> simp_all only [PredExpr.toExpr, itExpr, reduceCtorEq, Expr.lit.injEq,
            PredExpr.lit.injEq]
        subst hx₁' hx₂'
        have hp₁ := compilePred_lit_option_get_isPrim hok₁
        have hp₂ := compilePred_lit_option_get_isPrim hok₂
        rw [hty_get_1] at hp₁; rw [hty_get_2] at hp₂
        simp only [reducibleEq, hp₁, hp₂, Bool.and_self]
        split
        · exact ⟨true, rfl⟩
        · exact ⟨false, rfl⟩
      · exact hb
    obtain ⟨b, hre⟩ := hre
    have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .eq (Factory.option.get t₁) (Factory.option.get t₂)
        (SymEnv.ofEnv Γ).entities = .ok t₃ := by
      simp only [compileApp₂, hre, Except.bind_ok]
      split <;> exact ⟨_, rfl⟩
    refine assemble hok₃ ?_
    have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
    simp only at this
    rw [this, htyp]
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
  -- `.contains`
  case _ =>
    obtain ⟨ty₃, rfl, hce₁, hofeq, htyp⟩ := hcontains
    -- `(option.get t₁).typeOf = .set (ofType ty₃)`, `(option.get t₂).typeOf = ofType ty₂.typeOf`,
    -- and `ofType ty₂.typeOf = ofType ty₃` from the LUB, so the equality guard passes.
    simp only [hce₁, TermType.ofType] at hty_get_1
    have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .contains (Factory.option.get t₁) (Factory.option.get t₂)
        (SymEnv.ofEnv Γ).entities = .ok t₃ := by
      simp only [compileApp₂, hty_get_1, hty_get_2, hofeq, if_true]
      exact ⟨_, rfl⟩
    refine assemble hok₃ ?_
    have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
    simp only at this
    rw [this, htyp]
  -- `.containsAll`/`.containsAny`
  case _ =>
    obtain ⟨ty₃, ty₄, hop, hce₁, hce₂, hofeq, htyp⟩ := hcontainsAll
    simp only [hce₁, TermType.ofType] at hty_get_1
    simp only [hce₂, TermType.ofType] at hty_get_2
    rcases hop with rfl | rfl
    · have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .containsAll (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2, hofeq, if_true]; exact ⟨_, rfl⟩
      refine assemble hok₃ ?_
      have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
      simp only at this
      rw [this, htyp]
    · have ⟨t₃, hok₃⟩ : ∃ t₃, compileApp₂ .containsAny (Factory.option.get t₁) (Factory.option.get t₂)
          (SymEnv.ofEnv Γ).entities = .ok t₃ := by
        simp only [compileApp₂, hty_get_1, hty_get_2, hofeq, if_true]; exact ⟨_, rfl⟩
      refine assemble hok₃ ?_
      have := (compileApp₂_wf_types hwε.right hwf_get_1 hwf_get_2 hok₃).right
      simp only at this
      rw [this, htyp]

end Cedar.Thm
