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

import Cedar.SymCC.Compiler
import Cedar.Thm.Data.Map
import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Compiler.ExtHasAttrRec
import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.ofType
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Term.TypeOf
import Cedar.Thm.SymCC.Data.Basic
import Cedar.Validation.Typechecker

/-!
# D-72 step (3), `.extHasAttr` arm of `compilePred_well_typed`

Standalone arm lemma `compilePred_well_typed_extHasAttr` for the predicate
`.extHasAttr x₁ a as`. `typeOfPred` on this constructor does
`let (bty, c') ← typeOfExtHasAttr ty₁ x₁.toExpr (a :: as) c env;
 ok (TypedExpr.extHasAttr ty₁ a as (.bool bty)) c'`, so the typing fact is
`htp : typeOfExtHasAttr ty₁ x₁.toExpr (a :: as) c Γ = .ok (bty, c')` and
`typ = TypedExpr.extHasAttr ty₁ a as (.bool bty)`.

Mirrors the scalar `compile_well_typed_extHasAttr` in
`Cedar.Thm.SymCC.Compiler.WellTyped`.

## Private twins
The sibling file `Cedar/Thm/SymCC/Compiler/WellTyped.lean` is edited in parallel by
other workers and (per the D-72 WIP) its `compilePred_well_typed` dispatcher is still
red, so importing it is not possible. The compile-success + typing machinery for
`compileExtHasAttrRec` lives entirely in that file, so the lemmas this arm needs are
copied here verbatim as `private` twins (their own dependencies all live in importable
files: `WF.lean`, `Invert.lean`, `Term/WF.lean`, `Term/ofType.lean`, `Env/ofEnv.lean`,
`Data/Basic.lean`). Each twin carries a `-- twin of …` comment. When the integrator
merges, these can be dropped in favour of the originals.

This file touches no existing file; the integrator imports it.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

/-! ## Twins of chain-valid-from-typing helpers (Cedar/Thm/WellTyped/Expr/Typechecking.lean). -/

-- twin of Cedar/Thm/WellTyped/Expr/Typechecking.lean:typeOfHasAttr_ok_implies_entity_or_record
private theorem p5b_typeOfHasAttr_ok_implies_entity_or_record
    {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr} {c : Capabilities} {env : TypeEnv}
    {r : TypedExpr × Capabilities} :
    typeOfHasAttr ty₁ x₁ a c env = .ok r →
    (∃ ety, ty₁.typeOf = .entity ety) ∨ (∃ rty, ty₁.typeOf = .record rty) := by
  intro h
  simp only [typeOfHasAttr] at h
  split at h
  case h_1 rty heq => exact Or.inr ⟨rty, heq⟩
  case h_2 ety heq => exact Or.inl ⟨ety, heq⟩
  case h_3 => simp only [Validation.err, reduceCtorEq] at h

-- twin (specialised) of Cedar/Thm/WellTyped/Expr/Typechecking.lean:typeOfExtHasAttr_tyNext_type_entity_or_record
private theorem p5b_typeOfExtHasAttr_ok_implies_entity_or_record
    {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {attrs : List Attr}
    {c : Capabilities} {env : TypeEnv} {res : BoolType × Capabilities}
    (h : typeOfExtHasAttr ty₁ x₁ (attr :: attrs) c env = .ok res) :
    (∃ ety, ty₁.typeOf = .entity ety) ∨ (∃ rty, ty₁.typeOf = .record rty) := by
  cases attrs with
  | nil =>
    simp only [typeOfExtHasAttr, bind, Except.bind] at h
    generalize hha : typeOfHasAttr ty₁ x₁ attr c env = resHA at h
    cases resHA with
    | error => simp at h
    | ok val => exact p5b_typeOfHasAttr_ok_implies_entity_or_record hha
  | cons b rest =>
    simp only [typeOfExtHasAttr, bind, Except.bind] at h
    generalize hha : typeOfHasAttr ty₁ x₁ attr c env = resHA at h
    cases resHA with
    | error => simp at h
    | ok val => exact p5b_typeOfHasAttr_ok_implies_entity_or_record hha

-- twin of Cedar/Thm/WellTyped/Expr/Typechecking.lean:typeOfGetAttr_entity_ok_implies
private theorem p5b_typeOfGetAttr_entity_ok_implies
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {c : Capabilities} {env : TypeEnv}
  {tyNext : TypedExpr} {cga : Capabilities} {ety : EntityType}
  (hga : typeOfGetAttr ty₁ x₁ attr c env = .ok (tyNext, cga))
  (hety : ty₁.typeOf = .entity ety) :
  ∃ rty qty, env.ets.attrs? ety = .some rty ∧ rty.find? attr = .some qty ∧ tyNext.typeOf = qty.getType := by
  unfold typeOfGetAttr at hga
  rw [hety] at hga
  simp only [bind, Except.bind] at hga
  split at hga
  case h_1 rty hschema =>
    split at hga
    case h_1 => simp at hga
    case h_2 val hgir =>
      simp [Validation.ok] at hga
      obtain ⟨heq, _⟩ := hga
      simp only [getAttrInRecord] at hgir
      split at hgir
      case h_1 aty hfind =>
        simp [Validation.ok] at hgir
        have hval : val = (aty, ∅) := by exact hgir.symm
        rw [hval] at heq
        simp at heq
        exact ⟨rty, .required aty, hschema, hfind, by rw [← heq]; simp [TypedExpr.typeOf, Qualified.getType]⟩
      case h_2 aty hfind =>
        split at hgir
        · simp [Validation.ok] at hgir
          have hval : val = (aty, ∅) := by exact hgir.symm
          rw [hval] at heq
          simp at heq
          exact ⟨rty, .optional aty, hschema, hfind, by rw [← heq]; simp [TypedExpr.typeOf, Qualified.getType]⟩
        · simp [Validation.err] at hgir
      case h_3 => simp [Validation.err] at hgir
  case h_2 => simp [Validation.err] at hga

-- twin of Cedar/Thm/WellTyped/Expr/Typechecking.lean:typeOfGetAttr_record_ok_implies
private theorem p5b_typeOfGetAttr_record_ok_implies
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {c : Capabilities} {env : TypeEnv}
  {tyNext : TypedExpr} {cga : Capabilities} {rty : RecordType}
  (hga : typeOfGetAttr ty₁ x₁ attr c env = .ok (tyNext, cga))
  (hrty : ty₁.typeOf = .record rty) :
  ∃ qty, rty.find? attr = .some qty ∧ tyNext.typeOf = qty.getType := by
  unfold typeOfGetAttr at hga
  rw [hrty] at hga
  simp only [bind, Except.bind] at hga
  split at hga
  case h_1 => simp at hga
  case h_2 val hgir =>
    simp [Validation.ok] at hga
    obtain ⟨heq, _⟩ := hga
    simp only [getAttrInRecord] at hgir
    split at hgir
    case h_1 aty hfind =>
      simp [Validation.ok] at hgir
      have hval : val = (aty, ∅) := by exact hgir.symm
      rw [hval] at heq; simp at heq
      exact ⟨.required aty, hfind, by rw [← heq]; simp [TypedExpr.typeOf, Qualified.getType]⟩
    case h_2 aty hfind =>
      split at hgir
      · simp [Validation.ok] at hgir
        have hval : val = (aty, ∅) := by exact hgir.symm
        rw [hval] at heq; simp at heq
        exact ⟨.optional aty, hfind, by rw [← heq]; simp [TypedExpr.typeOf, Qualified.getType]⟩
      · simp [Validation.err] at hgir
    case h_3 => simp [Validation.err] at hgir

-- twin of Cedar/Thm/WellTyped/Expr/Typechecking.lean:typeOfHasAttr_ff_implies_attr_not_found
private theorem p5b_typeOfHasAttr_ff_implies_attr_not_found
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {c : Capabilities} {env : TypeEnv} {ety : EntityType}
  {tyHas : TypedExpr} {ci : Capabilities}
  (hha : typeOfHasAttr ty₁ x₁ attr c env = .ok (tyHas, ci))
  (hety : ty₁.typeOf = .entity ety)
  (hff : tyHas.typeOf = .bool .ff) :
  env.ets.attrs? ety = .none ∨ ∀ rty, env.ets.attrs? ety = .some rty → rty.find? attr = .none := by
  simp only [typeOfHasAttr, hety, bind, Except.bind] at hha
  split at hha
  case h_1 rty hattrs =>
    right; intro rty' hrty'
    have hrty_eq : rty = rty' := by rw [hattrs] at hrty'; exact Option.some.inj hrty'
    subst hrty_eq
    simp only [hasAttrInRecord] at hha
    split at hha
    · simp at hha
    · rename_i v heq
      simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at hha
      obtain ⟨hty_eq, _⟩ := hha
      split at heq
      case h_1 qty hfind =>
        split at heq <;> {
          simp only [Validation.ok, Except.ok.injEq] at heq
          subst heq; simp [TypedExpr.typeOf, ← hty_eq] at hff
        }
      case h_2 hfind => exact hfind
  case h_2 hattrs =>
    exact Or.inl hattrs

-- twin of Cedar/Thm/WellTyped/Expr/Typechecking.lean:typeOfHasAttr_ff_implies_record_attr_not_found
private theorem p5b_typeOfHasAttr_ff_implies_record_attr_not_found
  {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {c : Capabilities} {env : TypeEnv} {rty : RecordType}
  {tyHas : TypedExpr} {ci : Capabilities}
  (hha : typeOfHasAttr ty₁ x₁ attr c env = .ok (tyHas, ci))
  (hrty : ty₁.typeOf = .record rty)
  (hff : tyHas.typeOf = .bool .ff) :
  rty.find? attr = .none := by
  simp only [typeOfHasAttr, hrty, bind, Except.bind] at hha
  simp only [hasAttrInRecord] at hha
  split at hha
  · simp at hha
  · rename_i v heq
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at hha
    obtain ⟨hty_eq, _⟩ := hha
    split at heq
    case h_1 qty hfind =>
      split at heq <;> {
        simp only [Validation.ok, Except.ok.injEq] at heq
        subst heq
        simp [TypedExpr.typeOf, ← hty_eq] at hff
      }
    case h_2 hfind =>
      exact hfind

-- twin of Cedar/Thm/WellTyped/Expr/Typechecking.lean:typeOfExtHasAttr_implies_chain_valid
private theorem p5b_typeOfExtHasAttr_implies_chain_valid
    {ty₁ : TypedExpr} {x₁ : Expr} {attr : Attr} {attrs : List Attr}
    {c : Capabilities} {env : TypeEnv} {res : BoolType × Capabilities}
    (h : typeOfExtHasAttr ty₁ x₁ (attr :: attrs) c env = .ok res) :
    (∀ ety, ty₁.typeOf = .entity ety → ExtHasAttrChainValid env.ets (.entity ety) (attr :: attrs)) ∧
    (∀ rty, ty₁.typeOf = .record rty → ExtHasAttrChainValid env.ets (.record rty) (attr :: attrs)) := by
  induction attrs generalizing ty₁ x₁ attr c res with
  | nil =>
    constructor
    · intro ety _; exact ExtHasAttrChainValid.last
    · intro rty _; exact ExtHasAttrChainValid.last
  | cons b rest ih =>
    simp only [typeOfExtHasAttr, bind, Except.bind] at h
    generalize hha : typeOfHasAttr ty₁ x₁ attr c env = resHA at h
    cases resHA with
    | error => simp at h
    | ok valHA =>
      obtain ⟨tyHas, ci⟩ := valHA
      simp only at h
      split at h
      case h_1 hff =>
        simp only [Except.ok.injEq] at h
        constructor
        · intro ety hety
          have hnotfound := p5b_typeOfHasAttr_ff_implies_attr_not_found hha hety hff
          exact .cons_not_in_schema_entity hnotfound
        · intro rty hrty
          have hnotfound := p5b_typeOfHasAttr_ff_implies_record_attr_not_found hha hrty hff
          exact .cons_not_in_record hnotfound
      case h_2 hnotff =>
        generalize hga : typeOfGetAttr ty₁ x₁ attr (c ∪ ci) env = resGA at h
        cases resGA with
        | error => simp at h
        | ok valGA =>
          obtain ⟨tyNext, cga⟩ := valGA
          simp only at h
          generalize hrec : typeOfExtHasAttr tyNext (Expr.getAttr x₁ attr) (b :: rest) (c ∪ ci) env = resRec at h
          cases resRec with
          | error => simp at h
          | ok valRec =>
            have ihResult := ih hrec
            have htyNext_ety_or_rty := typeOfExtHasAttr_tyNext_type_entity_or_record hrec
            constructor
            · intro ety hety
              have ⟨rty_schema, qty, hschema, hfind, htyNext⟩ := p5b_typeOfGetAttr_entity_ok_implies hga hety
              rcases htyNext_ety_or_rty with ⟨nextEty, hnext⟩ | ⟨nextRty, hnext⟩
              · have hqtyType : qty.getType = .entity nextEty := by rw [← htyNext]; exact hnext
                exact .cons_entity hschema hfind hqtyType (ihResult.1 nextEty hnext)
              · have hqtyType : qty.getType = .record nextRty := by rw [← htyNext]; exact hnext
                exact .cons_record_from_entity hschema hfind hqtyType (ihResult.2 nextRty hnext)
            · intro rty hrty
              have ⟨qty, hfind, htyNext⟩ := p5b_typeOfGetAttr_record_ok_implies hga hrty
              rcases htyNext_ety_or_rty with ⟨nextEty, hnext⟩ | ⟨nextRty, hnext⟩
              · have hqtyType : qty.getType = .entity nextEty := by rw [← htyNext]; exact hnext
                exact .cons_entity_from_record hfind hqtyType (ihResult.1 nextEty hnext)
              · have hqtyType : qty.getType = .record nextRty := by rw [← htyNext]; exact hnext
                exact .cons_record_from_record hfind hqtyType (ihResult.2 nextRty hnext)

/-! ## Twins of the compile-success machinery (Cedar/Thm/SymCC/Compiler/WellTyped.lean). -/

-- twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:ofRecordType_preserves_attr
private theorem p5b_ofRecordType_preserves_attr
  {rty : RecordType} {attr : Attr} {qty : Qualified CedarType} {ty : CedarType}
  (hattr_exists : Data.Map.find? rty attr = some qty)
  (hattr_ty : qty.getType = ty) :
  ∃ attr_ty : TermType,
    (Data.Map.mk (TermType.ofRecordType rty.1)).find? attr = some attr_ty ∧
    match attr_ty with
    | .option attr_ty' => TermType.ofType ty = attr_ty' ∧ ¬qty.isRequired
    | _ => TermType.ofType ty = attr_ty ∧ qty.isRequired
:= by
  cases rty with | mk rty_1 =>
  induction rty_1
  case nil => simp [Data.Map.find?] at hattr_exists
  case cons head tail ih =>
    have ⟨k, v⟩ := head
    simp only [Data.Map.find?, List.find?, TermType.ofRecordType, Data.Map.toList_mk_id, Bool.not_eq_true]
    simp only [Data.Map.find?, List.find?, Data.Map.toList_mk_id, Bool.not_eq_true] at hattr_exists ih
    cases e : k == attr
    case false =>
      simp only [e] at ⊢ hattr_exists
      apply ih hattr_exists
    case true =>
      simp only [e, Option.some.injEq] at hattr_exists
      simp only [hattr_exists, Option.some.injEq, exists_eq_left']
      cases qty with
      | optional =>
        simp only [TermType.ofQualifiedType, Qualified.isRequired, and_true]
        simp only [Qualified.getType] at hattr_ty
        simp [hattr_ty]
      | required =>
        simp only [
          TermType.ofQualifiedType, Qualified.isRequired,
          Bool.true_eq_false, and_false, and_true,
        ]
        simp only [Qualified.getType] at hattr_ty
        simp only [hattr_ty]
        unfold TermType.ofType
        split
        case h_1 hof_type =>
          split at hof_type
          all_goals contradiction
        simp

-- twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:compileHasAttr_always_ok
private theorem p5b_compileHasAttr_always_ok {t₁ : Term} {a : Attr} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hty₁ : (∃ ety, t₁.typeOf = .entity ety) ∨ (∃ rty, t₁.typeOf = .record rty))
  : ∃ t, compileHasAttr t₁ a εs = .ok t := by
  simp only [compileHasAttr, compileAttrsOf, bind, Except.bind]
  cases hty₁ with
  | inl hty =>
    obtain ⟨ety, hτ ⟩ := hty
    have hwf_ty := typeOf_wf_term_is_wf hw₁
    rw [hτ] at hwf_ty
    cases hwf_ty with | entity_wf hvalid =>
    simp only [SymEntities.isValidEntityType] at hvalid
    have ⟨d, hd⟩ := Map.contains_iff_some_find?.mp hvalid
    have hattrs : εs.attrs ety = .some d.attrs := by
      simp [SymEntities.attrs, hd]
    simp only [hτ, hattrs]
    have hwf_attrs := wf_εs_implies_wf_attrs hwε hattrs
    have ⟨r, hrty⟩ := isCedarRecordType_implies_term_record_type hwf_attrs.right.right
    have happ_ty : (Factory.app d.attrs t₁).typeOf = .record r := by
      rw [← hrty]
      exact (wf_app hw₁ (by rw [hτ]; exact hwf_attrs.right.left.symm) hwf_attrs.left).right
    simp only [happ_ty]
    split <;> exact ⟨_, rfl⟩
  | inr hty =>
    obtain ⟨_, hτ⟩ := hty
    simp only [hτ]
    split <;> exact ⟨_, rfl⟩

-- twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:compileGetAttr_error_eq_noSuchAttribute_of_compileHasAttr_ok
private theorem p5b_compileGetAttr_error_eq_noSuchAttribute_of_compileHasAttr_ok
  {t t_ha : Term} {a : Attr} {εs : SymEntities} {e : SymCC.Error}
  (hha : compileHasAttr t a εs = .ok t_ha)
  (hga : compileGetAttr t a εs = .error e) :
  e = .noSuchAttribute
:= by
  obtain ⟨attrs, rty, hattrs, hrecord⟩ := compileHasAttr_ok_implies hha
  simp only [RecordHasAttr] at hrecord
  simp only [compileGetAttr, hattrs, Except.bind_ok, hrecord.left] at hga
  split at hga <;> simp_all

-- twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:compileAnd_ne_error
private theorem p5b_compileAnd_ne_error {t₁ : Term} {r₂ : SymCC.Result Term} {e : SymCC.Error}
  (hty₁ : t₁.typeOf = .option .bool)
  (hr₂ : ∃ t₂, r₂ = .ok t₂ ∧ t₂.typeOf = .option .bool)
  : compileAnd t₁ r₂ ≠ .error e := by
  obtain ⟨_, h₂, h₃⟩ := hr₂; subst h₂
  simp only [compileAnd, bind, Except.bind, hty₁, h₃, ↓reduceIte, ne_eq]
  intro h
  split at h <;> simp_all [reduceCtorEq]

-- twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:chain_step_close
private theorem p5b_chain_step_close
  {t₁ t_ga : Term} {b : Attr} {rest' : List Attr}
  {Γ : TypeEnv} {cty' : CedarType} {ty_ga : TermType}
  (hty_ifsome : (Factory.ifSome t₁ t_ga).typeOf = .option ty_ga)
  (hchain_rest : ExtHasAttrChainValid Γ.ets cty' (b :: rest'))
  (hty_ga_eq : ty_ga = TermType.ofType cty')
  (hcty_shape : (∃ ety, cty' = .entity ety) ∨ (∃ rty, cty' = .record rty)) :
  ∃ cty'',
    ExtHasAttrChainValid Γ.ets cty'' (b :: rest') ∧
    (Factory.ifSome t₁ t_ga).typeOf = .option (TermType.ofType cty'') ∧
    ((∃ ety, (Factory.ifSome t₁ t_ga).typeOf = .option (.entity ety)) ∨
     (∃ rty, (Factory.ifSome t₁ t_ga).typeOf = .option (.record rty))) := by
  have heq : (Factory.ifSome t₁ t_ga).typeOf = .option (TermType.ofType cty') := by
    rw [hty_ifsome, hty_ga_eq]
  exact ⟨cty', hchain_rest, heq, by
    cases hcty_shape with
    | inl h => obtain ⟨ety, hety⟩ := h; subst hety; exact Or.inl ⟨_, heq⟩
    | inr h => obtain ⟨rty, hrty⟩ := h; subst hrty; exact Or.inr ⟨_, heq⟩⟩

-- twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:chain_step_close_attr
private theorem p5b_chain_step_close_attr
  {t₁ t₂ t_ga : Term} {a b : Attr} {rest' : List Attr}
  {Γ : TypeEnv} {cty' : CedarType} {ty_ga tyₐ tty_find : TermType} {p q : Prop}
  (hty_ifsome : (Factory.ifSome t₁ t_ga).typeOf = .option ty_ga)
  (hty_ga : t_ga.typeOf = .option ty_ga)
  (hshape : match tyₐ with
    | .option _ => t_ga = Factory.record.get t₂ a
    | _ => t_ga = .some (Factory.record.get t₂ a))
  (hrg_ty : (Factory.record.get t₂ a).typeOf = tyₐ)
  (hty_rel : match tty_find with
    | .option ty => TermType.ofType cty' = ty ∧ p
    | _ => TermType.ofType cty' = tty_find ∧ q)
  (htyₐ_eq : tyₐ = tty_find)
  (hchain_rest : ExtHasAttrChainValid Γ.ets cty' (b :: rest'))
  (hcty_shape : (∃ ety, cty' = .entity ety) ∨ (∃ rty, cty' = .record rty)) :
  ∃ cty'',
    ExtHasAttrChainValid Γ.ets cty'' (b :: rest') ∧
    (Factory.ifSome t₁ t_ga).typeOf = .option (TermType.ofType cty'') ∧
    ((∃ ety, (Factory.ifSome t₁ t_ga).typeOf = .option (.entity ety)) ∨
     (∃ rty, (Factory.ifSome t₁ t_ga).typeOf = .option (.record rty))) := by
  cases hty_find : tty_find with
  | option ti =>
    simp only [hty_find] at hty_rel htyₐ_eq
    simp only [htyₐ_eq] at hshape
    rw [hshape, hrg_ty, htyₐ_eq] at hty_ga
    exact p5b_chain_step_close hty_ifsome hchain_rest
      ((TermType.option.inj hty_ga) ▸ hty_rel.left).symm hcty_shape
  | _ =>
    simp only [hty_find] at hty_rel htyₐ_eq
    simp only [htyₐ_eq] at hshape
    rw [hshape] at hty_ga
    simp only [typeOf_term_some, hrg_ty] at hty_ga
    exact p5b_chain_step_close hty_ifsome hchain_rest
      ((TermType.option.inj hty_ga).symm.trans (htyₐ_eq.trans hty_rel.left.symm))
      hcty_shape

-- twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:compileGetAttr_chain_step
private theorem p5b_compileGetAttr_chain_step
  {t₁ : Term} {a b : Attr} {rest' : List Attr} {t_ga : Term}
  {εs : SymEntities} {Γ : TypeEnv} {cty : CedarType}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hεs : εs = (SymEnv.ofEnv Γ).entities)
  (hty_cty : t₁.typeOf = .option (TermType.ofType cty))
  (hchain : ExtHasAttrChainValid Γ.ets cty (a :: b :: rest'))
  (hga_ok : compileGetAttr (Factory.option.get t₁) a εs = .ok t_ga) :
  ∃ cty',
    ExtHasAttrChainValid Γ.ets cty' (b :: rest') ∧
    (Factory.ifSome t₁ t_ga).typeOf = .option (TermType.ofType cty') ∧
    ((∃ ety, (Factory.ifSome t₁ t_ga).typeOf = .option (.entity ety)) ∨
     (∃ rty, (Factory.ifSome t₁ t_ga).typeOf = .option (.record rty))) := by
  have hwo := wf_option_get hw₁ hty_cty
  have ⟨hwf_ga, ty_ga, hty_ga⟩ := compileGetAttr_wf hwε hwo.left hga_ok
  have hty_ifsome : (Factory.ifSome t₁ t_ga).typeOf = .option ty_ga :=
    (wf_ifSome_option hw₁ hwf_ga hty_ga).right
  have ⟨t₂, rty, hok_attrs, hrga⟩ := compileGetAttr_ok_implies hga_ok
  obtain ⟨hty_t₂, tyₐ, hfind_a, hshape⟩ := hrga
  have ⟨hw₂, r₁, h₂, h₃⟩ := compileAttrsOf_wf hwε hwo.left hok_attrs
  have h₄ : rty = r₁ := TermType.record.inj (hty_t₂.symm.trans h₂)
  subst h₄
  have hrg_ty : (Factory.record.get t₂ a).typeOf = tyₐ :=
    (wf_record_get hw₂ hty_t₂ hfind_a).right
  have h₁ := hwo.right
  cases hchain with
  | cons_entity h₅ h₆ h₇ h₈ =>
    rename_i ety₁ nextEty₁ _ _
    simp only [TermType.ofType] at h₁
    cases h₃ with
    | inl hrec => simp [h₁] at hrec
    | inr hent =>
      obtain ⟨ety', fₐ, h₉, h₁₀, h₁₁⟩ := hent
      simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at h₅
      obtain ⟨entry, h₁₃, h₁₄⟩ := h₅
      have h₁₇ := ofEnv_preserves_entity (εnv := SymEnv.ofEnv Γ) rfl h₁₃
      rw [← hεs] at h₁₇
      have h₀ : ety' = ety₁ := by have h := h₉.symm.trans h₁; injection h with h; injection h
      simp only [SymEntities.attrs, h₀, h₁₇, bind, Option.bind] at h₁₀
      have ⟨tty_find, hfind_schema, hty_rel⟩ := p5b_ofRecordType_preserves_attr (rty := entry.attrs) (h₁₄ ▸ h₆) h₇
      rw [← (Option.some.inj h₁₀)] at h₁₁
      cases entry with
      | standard sch =>
        simp only [
          SymEntityData.ofEntityType, SymEntityData.ofStandardEntityType,
          SymEntityData.ofStandardEntityType.attrsUUF,
          UnaryFunction.outType, TermType.ofType, EntitySchemaEntry.attrs,
          TermType.record.injEq,
        ] at h₁₁ hfind_schema
        have htyₐ_eq : tyₐ = tty_find := Option.some.inj (hfind_a.symm.trans (h₁₁ ▸ hfind_schema))
        exact p5b_chain_step_close_attr hty_ifsome hty_ga hshape hrg_ty hty_rel htyₐ_eq h₈
          (Or.inl ⟨_, rfl⟩)
      | enum eids =>
        simp only [EntitySchemaEntry.attrs] at h₁₄
        rw [← h₁₄] at h₆
        simp [Map.empty, Map.find?, Data.Map.find?] at h₆
  | cons_record_from_entity h₅ h₆ h₇ h₈ =>
    rename_i ety₂ _ _ _
    simp only [TermType.ofType] at h₁
    cases h₃ with
    | inl hrec => simp [h₁] at hrec
    | inr hent =>
      obtain ⟨ety', fₐ, h₉, h₁₀, h₁₁⟩ := hent
      simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at h₅
      obtain ⟨entry, h₁₅, h₁₆⟩ := h₅
      have h₁₂ := ofEnv_preserves_entity (εnv := SymEnv.ofEnv Γ) rfl h₁₅
      rw [← hεs] at h₁₂
      have ⟨tty_find, hfind_schema, hty_rel⟩ := p5b_ofRecordType_preserves_attr (rty := entry.attrs) (h₁₆ ▸ h₆) h₇
      have h₁₄ : ety' = ety₂ := by
        have h := h₉.symm.trans h₁; injection h with h; injection h
      simp only [SymEntities.attrs, h₁₄, h₁₂, bind, Option.bind] at h₁₀
      rw [← (Option.some.inj h₁₀)] at h₁₁
      cases entry with
      | standard sch =>
        simp only [
          SymEntityData.ofEntityType, SymEntityData.ofStandardEntityType,
          SymEntityData.ofStandardEntityType.attrsUUF,
          UnaryFunction.outType, TermType.ofType, EntitySchemaEntry.attrs,
          TermType.record.injEq,
        ] at h₁₁ hfind_schema
        have htyₐ_eq : tyₐ = tty_find := Option.some.inj (hfind_a.symm.trans (h₁₁ ▸ hfind_schema))
        exact p5b_chain_step_close_attr hty_ifsome hty_ga hshape hrg_ty hty_rel htyₐ_eq h₈
          (Or.inr ⟨_, rfl⟩)
      | enum eids =>
        simp only [EntitySchemaEntry.attrs] at h₁₆
        rw [← h₁₆] at h₆
        simp [Map.empty, Map.find?, Data.Map.find?] at h₆
  | cons_entity_from_record h₅ h₆ h₇ =>
    have ⟨tty_find, hfind_schema, hty_rel⟩ := p5b_ofRecordType_preserves_attr h₅ h₆
    cases h₃ with
    | inl hrec =>
      simp only [TermType.ofType] at h₁
      have h₉ : rty = Map.mk (TermType.ofRecordType _) := TermType.record.inj (hrec.symm.trans h₁)
      have htyₐ_eq : tyₐ = tty_find := Option.some.inj (hfind_a.symm.trans (h₉ ▸ hfind_schema))
      exact p5b_chain_step_close_attr hty_ifsome hty_ga hshape hrg_ty hty_rel htyₐ_eq h₇
        (Or.inl ⟨_, rfl⟩)
    | inr h₉ =>
      obtain ⟨_, _, h₁₀, _, _⟩ := h₉
      simp [TermType.ofType, h₁₀] at h₁
  | cons_record_from_record h₅ h₆ h₇ =>
    have ⟨tty_find, hfind_schema, hty_rel⟩ := p5b_ofRecordType_preserves_attr h₅ h₆
    cases h₃ with
    | inl hrec =>
      simp only [TermType.ofType] at h₁
      have h₉ : rty = Map.mk (TermType.ofRecordType _) := TermType.record.inj (hrec.symm.trans h₁)
      have htyₐ_eq : tyₐ = tty_find := Option.some.inj (hfind_a.symm.trans (h₉ ▸ hfind_schema))
      exact p5b_chain_step_close_attr hty_ifsome hty_ga hshape hrg_ty hty_rel htyₐ_eq h₇
        (Or.inr ⟨_, rfl⟩)
    | inr h₉ =>
      obtain ⟨_, _, h₁₀, _, _⟩ := h₉
      simp [TermType.ofType, h₁₀] at h₁
  | cons_not_in_schema_entity hmissing =>
    rename_i ety
    simp only [TermType.ofType] at h₁
    cases h₃ with
    | inl hrecord => simp [h₁] at hrecord
    | inr hentity =>
      obtain ⟨ety', attrs, hty, hattrs, hout⟩ := hentity
      have hety : ety' = ety := by
        have h := hty.symm.trans h₁
        injection h with h
        injection h
      subst ety'
      cases hentry : Γ.ets.find? ety with
      | none =>
        rw [hεs] at hattrs
        simp only [SymEntities.attrs] at hattrs
        generalize hfind : (SymEnv.ofEnv Γ).entities.find? ety = o at hattrs
        cases o with
        | none => simp [] at hattrs
        | some data =>
          simp only [bind, Option.bind, Option.some.injEq] at hattrs
          simp only [SymEnv.ofEnv, SymEntities.ofSchema] at hfind
          rw [Map.make_find?_eq_list_find?, List.find?_append] at hfind
          have hfind_ets :
            List.find? (fun x => x.fst == ety)
              (List.map (fun x => (x.fst, SymEntityData.ofEntityType x.fst x.snd))
                (Map.toList Γ.ets)) = .none := by
            simp only [List.find?_map]
            simp only [Map.find?] at hentry
            generalize hfind_entry :
              List.find? (fun x => x.fst == ety) (Map.toList Γ.ets) = o at hentry ⊢
            cases o with
            | none =>
              simpa using
                congrArg (Option.map (fun x =>
                  (x.fst, SymEntityData.ofEntityType x.fst x.snd))) hfind_entry
            | some kv => simp at hentry
          simp only [hfind_ets, Option.none_or] at hfind
          simp only [List.find?_map, Option.map_eq_some_iff] at hfind
          obtain ⟨pair, ⟨actTy, hactfind, hpair⟩, hdata⟩ := hfind
          subst pair
          simp only at hdata
          subst data
          subst attrs
          simp only [SymEntityData.ofActionType, SymEntityData.emptyAttrs,
            UnaryFunction.outType, TermType.record.injEq] at hout
          rw [← hout] at hfind_a
          simp [Map.empty, Map.find?, Data.Map.find?] at hfind_a
      | some entry =>
        have hpres := ofEnv_preserves_entity (εnv := SymEnv.ofEnv Γ) rfl hentry
        rw [← hεs] at hpres
        simp only [SymEntities.attrs, hpres, bind, Option.bind, Option.some.injEq] at hattrs
        have hschema : Γ.ets.attrs? ety = .some entry.attrs := by
          simp [EntitySchema.attrs?, hentry]
        have hmiss : entry.attrs.find? a = .none := by
          rcases hmissing with hnone | hall
          · rw [hschema] at hnone
            contradiction
          · exact hall entry.attrs hschema
        cases entry with
        | standard sch =>
          subst attrs
          simp only [SymEntityData.ofEntityType, SymEntityData.ofStandardEntityType,
            SymEntityData.ofStandardEntityType.attrsUUF, UnaryFunction.outType,
            TermType.ofType, TermType.record.injEq] at hout
          simp only [EntitySchemaEntry.attrs] at hmiss
          have hnone : (Map.mk (TermType.ofRecordType sch.2.1)).find? a = .none := by
            rw [ofRecordType_as_map]
            exact (Data.Map.find?_mapOnValues_none TermType.ofQualifiedType).mpr hmiss
          rw [← hout, hnone] at hfind_a
          cases hfind_a
        | enum eids =>
          subst attrs
          simp only [SymEntityData.ofEntityType, SymEntityData.ofEnumEntityType,
            SymEntityData.emptyAttrs, UnaryFunction.outType, TermType.record.injEq] at hout
          rw [← hout] at hfind_a
          simp [Map.empty, Map.find?, Data.Map.find?] at hfind_a
  | cons_not_in_record hmissing =>
    rename_i recRty
    cases h₃ with
    | inl hrecord =>
      have hrty : rty = Map.mk (TermType.ofRecordType recRty.1) :=
        TermType.record.inj (hrecord.symm.trans h₁)
      have hnone : (Map.mk (TermType.ofRecordType recRty.1)).find? a = .none := by
        rw [ofRecordType_as_map]
        exact (Data.Map.find?_mapOnValues_none TermType.ofQualifiedType).mpr hmissing
      simp only [hrty, hnone] at hfind_a
      cases hfind_a
    | inr hentity => simp [TermType.ofType, h₁] at hentity

-- twin of Cedar/Thm/SymCC/Compiler/WellTyped.lean:compileExtHasAttrRec_ne_error
private theorem p5b_compileExtHasAttrRec_ne_error {t₁ : Term} {attrs : List Attr} {εs : SymEntities} {e : SymCC.Error}
  {Γ : TypeEnv} {cty : CedarType}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs)
  (hty₁ : (∃ ety, t₁.typeOf = .option (.entity ety)) ∨ (∃ rty, t₁.typeOf = .option (.record rty)))
  (hchain : ExtHasAttrChainValid Γ.ets cty attrs)
  (hεs : εs = (SymEnv.ofEnv Γ).entities)
  (hty_cty : t₁.typeOf = .option (TermType.ofType cty))
  : compileExtHasAttrRec t₁ attrs εs ≠ .error e := by
  induction attrs generalizing t₁ cty e with
  | nil => simp [compileExtHasAttrRec, pure, Except.pure]
  | cons a rest ih =>
    have hwo_and_type : (Factory.option.get t₁).WellFormed εs ∧
      ((∃ ety, (Factory.option.get t₁).typeOf = .entity ety) ∨
       (∃ rty, (Factory.option.get t₁).typeOf = .record rty)) := by
      cases hty₁ with
      | inl h =>
        obtain ⟨ety, hety⟩ := h
        have hwo := wf_option_get hw₁ hety
        exact ⟨hwo.left, .inl ⟨ety, hwo.right⟩⟩
      | inr h =>
        obtain ⟨rty, hrty⟩ := h
        have hwo := wf_option_get hw₁ hrty
        exact ⟨hwo.left, .inr ⟨rty, hwo.right⟩⟩
    have hwo := hwo_and_type.left
    have hty_ent_or_rec := hwo_and_type.right
    intro hcontra
    cases rest with
    | nil =>
      have ⟨t_ha, hok_ha⟩ := p5b_compileHasAttr_always_ok hwε hwo hty_ent_or_rec (a := a)
      simp only [compileExtHasAttrRec, bind, Except.bind, hok_ha, reduceCtorEq] at hcontra
    | cons b rest' =>
      have ⟨t_ha, hok_ha⟩ := p5b_compileHasAttr_always_ok hwε hwo hty_ent_or_rec (a := a)
      simp only [compileExtHasAttrRec, hok_ha, Except.bind_ok] at hcontra
      split at hcontra
      case h_1 => simp only [pure, Except.pure, reduceCtorEq] at hcontra
      case h_2 =>
        generalize hga : compileGetAttr (Factory.option.get t₁) a εs = rga at hcontra
        cases rga with
        | error e' =>
          have heq := p5b_compileGetAttr_error_eq_noSuchAttribute_of_compileHasAttr_ok hok_ha hga
          subst e'
          simp only [pure, Except.pure, reduceCtorEq] at hcontra
        | ok t_ga =>
          simp only at hcontra
          have hwf_ga := compileGetAttr_wf hwε hwo hga
          have hwf_ifsome_ga := wf_ifSome_option hw₁ hwf_ga.left hwf_ga.right.choose_spec
          have ⟨cty', hchain', hty_cty', hty₁'⟩ :=
            p5b_compileGetAttr_chain_step hwε hw₁ hεs hty_cty hchain hga
          generalize heq_rest : compileExtHasAttrRec (Factory.ifSome t₁ t_ga) (b :: rest') εs = r_rest at hcontra
          cases r_rest with
          | error e' =>
            exact absurd heq_rest (ih hwf_ifsome_ga.left hty₁' hchain' hty_cty')
          | ok t_rest =>
            have hwf_ha := compileHasAttr_wf hwε hwo hok_ha
            have hty_tHas := (wf_ifSome_option hw₁ hwf_ha.left hwf_ha.right).right
            have hty_rest := (compileExtHasAttrRec_wf hwε hwf_ifsome_ga.left
              ⟨TermType.ofType cty', hty_cty'⟩ heq_rest).right
            simp only [Except.bind_ok] at hcontra
            exact (p5b_compileAnd_ne_error hty_tHas ⟨t_rest, rfl, hty_rest⟩) hcontra

/-! ## The arm lemma. -/

/--
D-72 step (3), `.extHasAttr` arm (fork-independent — `typeOfExtHasAttr` does not
short-circuit on constant receiver types; a non-empty attribute chain forces the
receiver to be entity/record-typed). `compileExtHasAttr` always yields a
`.option .bool` term; from the sub-result type we get the receiver's
entity/record-ness and derive `ExtHasAttrChainValid` from `typeOfExtHasAttr`
success, so `compileExtHasAttrRec_ne_error` gives compile success and
`compileExtHasAttrRec_wf` gives the `.option .bool` type. Mirrors the scalar
`compile_well_typed_extHasAttr`.
-/
theorem compilePred_well_typed_extHasAttr
    {a : Attr} {attrs : List Attr} {x₁ : Cedar.Spec.PredExpr} {ty₁ : TypedExpr} {e₁ : Cedar.Spec.Expr} {bty : BoolType}
    {c c' : Capabilities} {Γ : TypeEnv} {it t₁ : Term}
    (hwε : (SymEnv.ofEnv Γ).WellFormed)
    (hitw : it.WellFormed (SymEnv.ofEnv Γ).entities)
    (hitty : it.typeOf = .option (TermType.ofType ty₁.typeOf))
    (hok₁ : compilePred x₁ it (SymEnv.ofEnv Γ) = .ok t₁)
    (hty₁ : t₁.typeOf = .option (TermType.ofType ty₁.typeOf))
    (htp : typeOfExtHasAttr ty₁ e₁ (a :: attrs) c Γ = .ok (bty, c')) :
    ∃ t, compilePred (.extHasAttr x₁ a attrs) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType (TypedExpr.extHasAttr ty₁ a attrs (.bool bty)).typeOf) := by
  have ⟨hwf_comp_x, _, _⟩ := compilePred_wf hwε hitw hitty hok₁
  have hεs : (SymEnv.ofEnv Γ).entities = (SymEnv.ofEnv Γ).entities := rfl
  -- The result type is always `.bool`.
  have htyp_ty : (TypedExpr.extHasAttr ty₁ a attrs (.bool bty)).typeOf = .bool bty := by
    simp only [TypedExpr.typeOf]
  -- Receiver is entity- or record-typed (chain is non-empty).
  have hbool_rec :
      (∃ ety, ty₁.typeOf = .entity ety) ∨ (∃ rty, ty₁.typeOf = .record rty) :=
    p5b_typeOfExtHasAttr_ok_implies_entity_or_record htp
  -- Derive the chain-valid fact from the typing success.
  have hchain_both := p5b_typeOfExtHasAttr_implies_chain_valid htp
  -- Package `t₁`'s `.option (entity/record)` type and the chain-valid relation at `ty₁.typeOf`.
  have hty' :
      (∃ ety, t₁.typeOf = .option (.entity ety)) ∨
      (∃ rty, t₁.typeOf = .option (.record rty)) := by
    rcases hbool_rec with ⟨ety, h⟩ | ⟨rty, h⟩
    · exact Or.inl ⟨ety, by simp only [hty₁, h, TermType.ofType]⟩
    · cases rty with | mk rl =>
      exact Or.inr ⟨Data.Map.mk (TermType.ofRecordType rl),
        by simp only [hty₁, h, TermType.ofType]⟩
  have hchain : ExtHasAttrChainValid Γ.ets ty₁.typeOf (a :: attrs) := by
    rcases hbool_rec with ⟨ety, h⟩ | ⟨rty, h⟩
    · rw [h]; exact hchain_both.left ety h
    · rw [h]; exact hchain_both.right rty h
  -- Reduce `compilePred (.extHasAttr ..)` to `compileExtHasAttr t₁ (a :: attrs) …`,
  -- rewrite to the recursive form, and discharge the error case via `_ne_error`.
  simp only [compilePred, hok₁, Except.bind_ok]
  rw [compileExtHasAttr_eq_compileExtHasAttrRec]
  cases hext : compileExtHasAttrRec t₁ (a :: attrs) (SymEnv.ofEnv Γ).entities with
  | error =>
    exact absurd hext
      (p5b_compileExtHasAttrRec_ne_error hwε.right hwf_comp_x hty' hchain hεs hty₁)
  | ok t_ext =>
    refine ⟨t_ext, rfl, ?_⟩
    rw [htyp_ty]
    have hwf := compileExtHasAttrRec_wf hwε.right hwf_comp_x ⟨_, hty₁⟩ hext
    rw [hwf.right]
    simp only [TermType.ofType]

end Cedar.Thm
