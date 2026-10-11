/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.ExtHasAttr

/-!
# Predicate type soundness — `.extHasAttr` arm (Phase 9c), WEAK form (D-94)

Mirror of `type_of_extHasAttr_is_sound` (`Typechecker/ExtHasAttr.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the WEAK form (D-94): no guarded
capabilities, no capability invariant, and the error side admits any error.

`typeOfPred (.extHasAttr x₁ a as)` peels to `typeOfPred x₁` then the SAME
`typeOfExtHasAttr ty₁ x₁.toExpr (a :: as)` helper the expression typechecker uses,
wrapping the result into `.bool bty`. `evaluatePred (.extHasAttr x₁ a l)` is
`evaluatePred x₁ >>= hasAttrs · a l es`, whose result (`hasAttrs`) is ALWAYS a
boolean or a (type) error. So on the error side we admit the error; on the ok
side we have a boolean `b`, which is an instance of `.bool bty`.

The `BoolType` returned by `typeOfExtHasAttr` can be `.anyBool`, `.ff`, or `.tt`:

* `.anyBool` closes directly (`bool_is_instance_of_anyBool`);
* `.ff` is ruled out from runtime `b = true` by `typeOfHasAttr`'s schema
  reasoning (local `typeOfHasAttr_ff_contradicts_find_wk`), which needs only the
  well-formed-environment hypothesis — NO capability invariant;
* `.tt` is the precise-positive case. It arises either from a *required* record
  attribute (schema-provable, capability-free) or from a *capability*
  `(x₁.toExpr, .attr a) ∈ c`. The Expr twin discharges the latter via a
  capability invariant (`typeOfExtHasAttr_bool_type_sound`), which the WEAK
  predicate form does not carry (D-95 / Basic.lean note). The capability `.tt`
  sub-case is therefore the sole remaining gap in this WEAK draft.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- `hasAttrs.loop` only ever yields a boolean on the ok side (local, capability-free). -/
private theorem hasAttrs_loop_ok_is_bool_wk {v₁ : Value} {attrs : List Attr} {es : Entities} {r : Value}
    (h₁ : hasAttrs.loop v₁ attrs es = .ok r) :
    ∃ b, r = Value.prim (.bool b) := by
  induction attrs generalizing v₁ with
  | nil =>
    simp only [hasAttrs.loop, Except.ok.injEq] at h₁
    exact ⟨true, h₁.symm⟩
  | cons attr rest ih =>
    simp only [hasAttrs.loop] at h₁
    repeat split at h₁
    all_goals first
      | exact ih h₁
      | simp only [Except.ok.injEq] at h₁; exact ⟨_, h₁.symm⟩
      | simp at h₁

/-- `hasAttrs` only ever yields a boolean on the ok side (local, capability-free). -/
private theorem hasAttrs_ok_is_bool_wk {v₁ : Value} {attr : Attr} {attrs : List Attr}
    {es : Entities} {r : Value}
    (hok : hasAttrs v₁ attr attrs es = .ok r) :
    ∃ b, r = Value.prim (.bool b) := by
  simp only [hasAttrs] at hok
  exact hasAttrs_loop_ok_is_bool_wk hok

/--
Local, capability-free copy of `instance_of_getAttr_type` (the Expr twin's helper is
`private`). The `heval` hypothesis of the twin is unused in its body, so it is dropped.
-/
private theorem instance_of_getAttr_type_wk
  {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr} {c : Capabilities} {env : TypeEnv}
  {tyNext : TypedExpr} {cga : Capabilities}
  {v : Value} {m : Map Attr Value} {next : Value}
  {request : Request} {entities : Entities}
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (hga : typeOfGetAttr ty₁ x₁ a c env = .ok (tyNext, cga))
  (hio : InstanceOfType env v ty₁.typeOf)
  (hattrs : attrsOf v (fun uid => .ok (entities.attrsOrEmpty uid)) = .ok m)
  (hfind : m.find? a = .some next) :
  InstanceOfType env next tyNext.typeOf := by
  simp only [typeOfGetAttr, bind, Except.bind] at hga
  split at hga
  case h_1 rty hrty =>
    rw [hrty] at hio
    have ⟨avs, hv⟩ := instance_of_record_type_is_record hio
    subst hv
    simp only [attrsOf, Except.ok.injEq] at hattrs; subst hattrs
    split at hga
    case h_1 => simp at hga
    case h_2 val_gir hgir =>
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hga
      obtain ⟨hty_eq, _⟩ := hga
      have htyof : tyNext.typeOf = val_gir.1 := by
        rw [← hty_eq]; simp [TypedExpr.typeOf]
      rw [htyof]
      simp only [getAttrInRecord] at hgir
      split at hgir
      case h_1 aty hfind_rty =>
        have hval : val_gir = (aty, ∅) := by unfold ok at hgir; simp at hgir; exact hgir.symm
        rw [hval]
        exact instance_of_attribute_type hio hfind_rty rfl hfind
      case h_2 aty hfind_rty =>
        split at hgir
        · have hval : val_gir = (aty, ∅) := by unfold ok at hgir; simp at hgir; exact hgir.symm
          rw [hval]
          exact instance_of_attribute_type hio hfind_rty rfl hfind
        · simp [err] at hgir
      case h_3 => simp [err] at hgir
  case h_2 ety hety =>
    rw [hety] at hio
    have ⟨uid, huid_ty, hv⟩ := instance_of_entity_type_is_entity hio
    subst hv
    simp only [attrsOf, Except.ok.injEq] at hattrs; subst hattrs
    split at hga
    case h_1 rty hschema =>
      split at hga
      case h_1 => simp at hga
      case h_2 val_gir hgir =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hga
        obtain ⟨hty_eq, _⟩ := hga
        have htyof : tyNext.typeOf = val_gir.1 := by
          rw [← hty_eq]; simp [TypedExpr.typeOf]
        rw [htyof]
        simp only [getAttrInRecord] at hgir
        split at hgir
        case h_1 aty hfind_rty =>
          have hval : val_gir = (aty, ∅) := by unfold ok at hgir; simp at hgir; exact hgir.symm
          rw [hval]
          subst huid_ty
          simp only [EntitySchema.attrs?] at hschema
          cases hfind_ent : entities.find? uid with
          | none =>
            exact absurd hfind (by simp [Entities.attrsOrEmpty, hfind_ent])
          | some d =>
            simp [Entities.attrsOrEmpty, hfind_ent] at hfind
            have hio_attrs := well_typed_entity_attributes h₂ hfind_ent hschema
            exact instance_of_attribute_type hio_attrs hfind_rty rfl hfind
        case h_2 aty hfind_rty =>
          split at hgir
          · have hval : val_gir = (aty, ∅) := by unfold ok at hgir; simp at hgir; exact hgir.symm
            rw [hval]
            subst huid_ty
            simp only [EntitySchema.attrs?] at hschema
            cases hfind_ent : entities.find? uid with
            | none =>
              exact absurd hfind (by simp [Entities.attrsOrEmpty, hfind_ent])
            | some d =>
              simp [Entities.attrsOrEmpty, hfind_ent] at hfind
              have hio_attrs := well_typed_entity_attributes h₂ hfind_ent hschema
              exact instance_of_attribute_type hio_attrs hfind_rty rfl hfind
          · simp [err] at hgir
        case h_3 => simp [err] at hgir
    case h_2 => simp [err] at hga
  case h_3 => simp [err] at hga

/--
Local, capability-free copy of `typeOfHasAttr_ff_contradicts_find` (the Expr twin's
helper is `private`). Uses only the well-formed-environment hypothesis.
-/
private theorem typeOfHasAttr_ff_contradicts_find_wk
  {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr} {c : Capabilities} {env : TypeEnv}
  {tyHas : TypedExpr} {ci : Capabilities}
  {v : Value} {m : Map Attr Value} {next : Value}
  {request : Request} {entities : Entities}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hha : typeOfHasAttr ty₁ x₁ a c env = .ok (tyHas, ci))
  (hff : tyHas.typeOf = .bool .ff)
  (hio : InstanceOfType env v ty₁.typeOf)
  (hattrs : (attrsOf v fun uid => .ok (entities.attrsOrEmpty uid)) = .ok m)
  (hfind : m.find? a = .some next) : False := by
  simp only [typeOfHasAttr, bind, Except.bind] at hha
  split at hha
  case h_1 rty heq =>
    simp only [hasAttrInRecord] at hha
    split at hha
    · simp at hha
    · rename_i v₁ heq₂
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hha
      obtain ⟨hty_eq, _⟩ := hha
      split at heq₂
      case h_1 qty hfind_rty =>
        split at heq₂ <;> {
          simp only [ok, Except.ok.injEq] at heq₂
          subst heq₂; simp [TypedExpr.typeOf, ← hty_eq] at hff
        }
      case h_2 hfind_rty_none =>
        rw [heq] at hio
        cases hio with
        | instance_of_record r h₁_contains _ _ =>
          have heq_rm : r = m := by simpa [attrsOf] using hattrs
          subst heq_rm
          rename_i h_closed _ _
          have hrc := h_closed a (Map.contains_iff_some_find?.mpr ⟨next, hfind⟩)
          rw [Map.contains_iff_some_find?] at hrc
          obtain ⟨_, habs⟩ := hrc
          simp [hfind_rty_none] at habs
  case h_2 ety heq =>
    rw [heq] at hio
    have ⟨uid, _, hv_eq⟩ := instance_of_entity_type_is_entity hio
    subst hv_eq
    simp [attrsOf] at hattrs
    subst hattrs
    split at hha
    case h_1 rty hety_schema =>
      simp only [hasAttrInRecord] at hha
      split at hha
      · simp at hha
      · rename_i v₁ heq₂
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hha
        obtain ⟨hty_eq, _⟩ := hha
        split at heq₂
        case h_1 qty hfind_schema =>
          split at heq₂ <;> {
            simp only [ok, Except.ok.injEq] at heq₂
            subst heq₂; simp [TypedExpr.typeOf, ← hty_eq] at hff
          }
        case h_2 hfind_schema_none =>
          have hent : ∃ data, entities.find? uid = some data := by
            cases hf : entities.find? uid with
            | some d => exact ⟨d, rfl⟩
            | none => simp [Entities.attrsOrEmpty, hf] at hfind
          obtain ⟨data, hent⟩ := hent
          have hattrs_eq : entities.attrsOrEmpty uid = data.attrs := by
            simp [Entities.attrsOrEmpty, hent]
          rw [hattrs_eq] at hfind
          have hschema := hwf.2.2.1 uid data hent
          rcases hschema with ⟨entry, hets_find, _, hinst_attrs, _, _⟩ | ⟨_, _, _⟩
          · have huid_ety : uid.ty = ety := by assumption
            have hfind_ety : env.ets.find? ety = some entry := huid_ety ▸ hets_find
            have hrty_eq : entry.attrs = rty := by
              have h : env.ets.attrs? ety = some entry.attrs := by
                simp [EntitySchema.attrs?, hfind_ety]
              simp [h] at hety_schema; exact hety_schema
            have habsent := absent_attribute_is_absent hinst_attrs (hrty_eq ▸ hfind_schema_none)
            rw [hfind] at habsent
            contradiction
          · rename_i hempty _ _
            rw [hempty] at hfind
            simp [Map.find?, Map.empty] at hfind
    case h_2 hety_none =>
      split at hha
      · have hent : ∃ data, entities.find? uid = some data := by
          cases hf : entities.find? uid with
          | some d => exact ⟨d, rfl⟩
          | none => simp [Entities.attrsOrEmpty, hf] at hfind
        obtain ⟨data, hent⟩ := hent
        have hschema := hwf.2.2.1 uid data hent
        rcases hschema with ⟨entry, hets_find, _, _, _, _⟩ | ⟨hempty, _, _⟩
        · have huid_ety : uid.ty = ety := by assumption
          have : env.ets.find? ety = none := by
            simp [EntitySchema.attrs?] at hety_none
            exact hety_none
          rw [huid_ety] at hets_find
          simp [this] at hets_find
        · simp [Entities.attrsOrEmpty, hent, hempty] at hfind
      · simp [err] at hha
  case h_3 =>
    simp [err] at hha

/--
WEAK copy of `typeOfHasAttr_tt_contradicts_find_none`. The schema sub-cases close
capability-free. The two CAPABILITY sub-cases — where `typeOfHasAttr` returns `.tt`
solely because `(x₁, .attr a) ∈ c` — are the WEAK gap (D-95): the Expr twin closes
them with a capability invariant that the predicate soundness statement does not
carry, so here those two `False` goals are left OPEN (red, never `sorry`).
-/
private theorem typeOfHasAttr_tt_contradicts_find_none_wk
  {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr}
  {c : Capabilities} {env : TypeEnv}
  {v : Value} {request : Request} {entities : Entities}
  {val_ha : TypedExpr × Capabilities}
  {r : Map Attr Value}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hha : typeOfHasAttr ty₁ x₁ a c env = .ok val_ha)
  (heq_tt : val_ha.fst.typeOf = .bool .tt)
  (hio : InstanceOfType env v ty₁.typeOf)
  (hattrs : (attrsOf v (fun uid => .ok (entities.attrsOrEmpty uid))) = .ok r)
  (hfind_none : r.find? a = none) :
  False := by
  unfold typeOfHasAttr at hha
  split at hha
  case h_1 rty hrty =>
    simp only [ok, bind, Except.bind] at hha
    generalize hattr_rec : hasAttrInRecord rty x₁ a c true = res_rec at hha
    cases res_rec with
    | error => simp at hha
    | ok val =>
      simp only [Except.ok.injEq] at hha
      unfold hasAttrInRecord at hattr_rec
      split at hattr_rec
      case h_1 qty hqty_find =>
        simp only [ok] at hattr_rec
        split at hattr_rec
        case isTrue h_cond =>
          simp only [Except.ok.injEq] at hattr_rec
          have hio_rec : InstanceOfType env v (.record rty) := by rwa [hrty] at hio
          simp [Bool.or_eq_true, decide_eq_true_eq] at h_cond
          cases h_cond with
          | inl h_cap =>
            -- WEAK GAP: .tt established by capability `(x₁, .attr a) ∈ c`. No capability
            -- invariant in the predicate soundness statement, so this `False` is unprovable.
            -- OPEN (WEAK gap): `False` from a record capability `.tt`. No sorry; goal left unsolved.
            clear hha hattr_rec
          | inr h_req =>
            cases qty with
            | required aty =>
              have ⟨m, hm⟩ := instance_of_record_type_is_record hio_rec
              subst hm; simp [attrsOf] at hattrs; subst hattrs
              have h_present := required_attribute_is_present hio_rec hqty_find
              obtain ⟨_, h_some⟩ := h_present
              simp [hfind_none] at h_some
            | optional _ => simp [Qualified.isRequired] at h_req
        case isFalse =>
          simp only [Except.ok.injEq] at hattr_rec
          rw [← hattr_rec] at hha
          rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
      case h_2 =>
        simp only [ok, Except.ok.injEq] at hattr_rec
        rw [← hattr_rec] at hha
        rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
  case h_2 ety hety =>
    split at hha
    case h_1 rty' hattrs_schema =>
      simp only [ok, bind, Except.bind] at hha
      generalize hattr_rec : hasAttrInRecord rty' x₁ a c false = res_rec at hha
      cases res_rec with
      | error => simp at hha
      | ok val =>
        simp only [Except.ok.injEq] at hha
        unfold hasAttrInRecord at hattr_rec
        split at hattr_rec
        case h_1 qty hqty =>
          simp only [ok] at hattr_rec
          split at hattr_rec
          case isTrue h_cond =>
            simp only [Except.ok.injEq] at hattr_rec
            -- WEAK GAP: entity knownToExist=false ⇒ .tt only via capability `(x₁,.attr a) ∈ c`.
            simp at h_cond
            -- OPEN (WEAK gap): `False` from an entity capability `.tt`. No sorry; goal left unsolved.
            clear hha hattr_rec
          case isFalse =>
            simp only [Except.ok.injEq] at hattr_rec
            rw [← hattr_rec] at hha
            rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
        case h_2 =>
          simp only [ok, Except.ok.injEq] at hattr_rec
          rw [← hattr_rec] at hha
          rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
    case h_2 =>
      split at hha
      · simp only [ok, Except.ok.injEq] at hha
        rw [← hha] at heq_tt; simp [TypedExpr.typeOf] at heq_tt
      · simp [err] at hha
  case h_3 => simp [err] at hha

/--
WEAK bool-type soundness for `typeOfExtHasAttr`, with NO capability invariant and
NO Expr-level evaluation hypothesis (only `InstanceOfType env v ty₁.typeOf` and the
runtime `hasAttrs.loop` result over the SAME value `v`). This is the pred-world
analogue of the Expr twin's `typeOfExtHasAttr_bool_type_sound`; the `.anyBool` and
`.ff` cases are capability-free, and the `.tt`-via-capability case is the WEAK gap.
-/
private theorem typeOfExtHasAttr_bool_type_sound_wk
    {ty₁ : TypedExpr} {x₁ : Expr} {attrs : List Attr}
    {c : Capabilities} {env : TypeEnv}
    {v : Value} {request : Request} {entities : Entities}
    {bty : BoolType} {caps : Capabilities} {b : Bool}
    (hwf : InstanceOfWellFormedEnvironment request entities env)
    (hext : typeOfExtHasAttr ty₁ x₁ attrs c env = .ok (bty, caps))
    (hio : InstanceOfType env v ty₁.typeOf)
    (hloop : hasAttrs.loop v attrs entities = .ok (.prim (.bool b))) :
    InstanceOfBoolType b bty := by
  induction attrs generalizing ty₁ x₁ v c bty caps with
  | nil =>
    -- typeOfExtHasAttr _ _ [] = ok (.anyBool, ∅)
    simp only [typeOfExtHasAttr, Except.ok.injEq, Prod.mk.injEq] at hext
    rw [← hext.1]; simp [InstanceOfBoolType]
  | cons a rest ih =>
    cases rest with
    | nil =>
      -- single remaining attribute: result is typeOfHasAttr's precise bool type
      simp only [typeOfExtHasAttr, bind, Except.bind] at hext
      cases hha : typeOfHasAttr ty₁ x₁ a c env with
      | error => simp [hha] at hext
      | ok val_ha =>
        simp only [hha] at hext
        split at hext
        case h_1 bty' heq =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hext
          obtain ⟨hbty_eq, _⟩ := hext
          rw [← hbty_eq]
          -- hasAttrs.loop v [a] = attrsOf v; find? a => recurse([]) | none => false
          simp only [hasAttrs.loop] at hloop
          split at hloop
          case h_2 => simp at hloop
          rename_i r hattrs
          split at hloop
          case h_1 next hfind =>
            -- attr PRESENT ⇒ loop [] = true ⇒ b = true
            simp only [hasAttrs.loop, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hloop
            subst hloop
            cases bty' with
            | anyBool => simp [InstanceOfBoolType]
            | tt => simp [InstanceOfBoolType]
            | ff =>
              -- .ff but attr present: schema contradiction (capability-free)
              exfalso
              exact typeOfHasAttr_ff_contradicts_find_wk hwf hha heq hio hattrs hfind
          case h_2 hfind =>
            -- attr ABSENT ⇒ loop = false ⇒ b = false
            simp only [Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hloop
            subst hloop
            cases bty' with
            | anyBool => simp [InstanceOfBoolType]
            | ff => simp [InstanceOfBoolType]
            | tt =>
              -- .tt but attr absent: schema OR capability. Capability sub-case is the WEAK gap.
              exfalso
              exact typeOfHasAttr_tt_contradicts_find_none_wk hwf hha heq hio hattrs hfind
        case h_2 =>
          -- typeOfHasAttr's type is not .bool ⇒ bty = .anyBool
          simp only [Except.ok.injEq, Prod.mk.injEq] at hext
          rw [← hext.1]; simp [InstanceOfBoolType]
    | cons nextAttr more =>
      -- recursive chain. Mirror the Expr twin, but the IH carries no capability.
      simp only [typeOfExtHasAttr, bind, Except.bind] at hext
      cases hha_step : typeOfHasAttr ty₁ x₁ a c env with
      | error => simp [hha_step] at hext
      | ok val_ha =>
        simp only [hha_step] at hext
        obtain ⟨tyHas, ci_ha⟩ := val_ha
        simp only at hext
        simp only [hasAttrs.loop] at hloop
        split at hloop
        case h_2 => simp at hloop
        rename_i r hattrs
        split at hloop
        case h_2 hfind_none =>
          -- find? a = none ⇒ loop short-circuits false ⇒ b = false
          simp only [Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hloop
          subst hloop
          split at hext
          case h_1 hff =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hext
            rw [← hext.1]; simp [InstanceOfBoolType]
          case h_2 hnotff =>
            cases hga : typeOfGetAttr ty₁ x₁ a (c ∪ ci_ha) env with
            | error => simp [hga] at hext
            | ok val_ga =>
              simp only [hga] at hext
              cases h_rec : typeOfExtHasAttr val_ga.1 (Expr.getAttr x₁ a) (nextAttr :: more) (c ∪ ci_ha) env with
              | error => simp [h_rec] at hext
              | ok val_rec =>
                simp only [h_rec] at hext
                split at hext
                · simp only [List.empty_eq, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hext
                  rw [← hext.1]; simp [InstanceOfBoolType]
                · rename_i heq_tt
                  split at hext
                  all_goals simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                  all_goals rw [← hext.1]
                  case h_1 hasBty hhas =>
                    cases hasBty
                    case anyBool => simp [InstanceOfBoolType]
                    case ff => simp [InstanceOfBoolType]
                    case tt =>
                      exfalso
                      exact typeOfHasAttr_tt_contradicts_find_none_wk hwf hha_step hhas hio hattrs hfind_none
                  case h_2 => simp [InstanceOfBoolType]
                · simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                  rw [← hext.1]; simp [InstanceOfBoolType]
        case h_1 next hfind =>
          -- attr present ⇒ recurse into getAttr value
          split at hext
          case h_1 hff =>
            exfalso
            exact typeOfHasAttr_ff_contradicts_find_wk hwf hha_step hff hio hattrs hfind
          case h_2 hnotff =>
            cases hga : typeOfGetAttr ty₁ x₁ a (c ∪ ci_ha) env with
            | error => simp [hga] at hext
            | ok val_ga =>
              simp only [hga] at hext
              obtain ⟨tyNext, _⟩ := val_ga
              cases h_rec : typeOfExtHasAttr tyNext (Expr.getAttr x₁ a) (nextAttr :: more) (c ∪ ci_ha) env with
              | error => simp [h_rec] at hext
              | ok val_rec =>
                simp only [h_rec] at hext
                have hio_next : InstanceOfType env next tyNext.typeOf :=
                  instance_of_getAttr_type_wk hwf hga hio hattrs hfind
                have hloop_next : hasAttrs.loop next (nextAttr :: more) entities = .ok (.prim (.bool b)) := hloop
                have hih := ih h_rec hio_next hloop_next
                split at hext
                · -- recursive = .ff ⇒ result .ff
                  rename_i heq_ff
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                  rw [← hext.1]
                  rw [heq_ff] at hih
                  exact hih
                · rename_i heq_tt
                  rw [heq_tt] at hih
                  simp only [InstanceOfBoolType] at hih
                  cases b
                  case false => simp at hih
                  case true =>
                    split at hext
                    all_goals simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                    all_goals rw [← hext.1]
                    all_goals simp [InstanceOfBoolType]
                    case h_1 hasBty hhas =>
                      cases hasBty <;> simp
                      case ff =>
                        exfalso
                        exact hnotff hhas
                · simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                  rw [← hext.1]; simp [InstanceOfBoolType]

/--
Inversion of `typeOfPred (.extHasAttr x₁ a as)` (pred twin of the `.extHasAttr`
peel in `type_of_extHasAttr_is_sound`).
-/
theorem type_of_pred_extHasAttr_inversion {x₁ : PredExpr} {a : Attr} {as' : List Attr}
    {itTy : CedarType} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (h₃ : typeOfPred (.extHasAttr x₁ a as') itTy c₁ env = Except.ok (ty, c₂)) :
    ∃ ty₁ c₁' bty c',
      typeOfPred x₁ itTy c₁ env = .ok (ty₁, c₁') ∧
      typeOfExtHasAttr ty₁ x₁.toExpr (a :: as') c₁ env = .ok (bty, c') ∧
      ty = .extHasAttr ty₁ a as' (.bool bty) ∧
      ty.typeOf = .bool bty ∧
      c₂ = c' := by
  simp only [typeOfPred] at h₃
  cases hpred : typeOfPred x₁ itTy c₁ env with
  | error e => simp [hpred] at h₃
  | ok res₁ =>
    obtain ⟨ty₁, c₁'⟩ := res₁
    simp only [hpred, Except.bind_ok] at h₃
    cases hext : typeOfExtHasAttr ty₁ x₁.toExpr (a :: as') c₁ env with
    | error e => simp [hext] at h₃
    | ok resE =>
      obtain ⟨bty, c'⟩ := resE
      simp only [hext, Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h₃
      obtain ⟨hty, hc⟩ := h₃
      refine ⟨ty₁, c₁', bty, c', rfl, hext, hty.symm, ?_, hc.symm⟩
      rw [← hty]; simp [TypedExpr.typeOf]

/--
`.extHasAttr` predicate soundness (pred twin of `type_of_extHasAttr_is_sound`),
WEAK form (D-94).
-/
theorem type_of_pred_extHasAttr_is_sound {x₁ : PredExpr} {a : Attr} {as' : List Attr}
    {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    {request : Request} {entities : Entities}
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.extHasAttr x₁ a as') itTy c₁ env = Except.ok (ty, c₂))
    (ih : TypeOfPredIsSound x₁) :
    ∃ v, EvaluatesToPred (.extHasAttr x₁ a as') it request entities v ∧ InstanceOfType env v ty.typeOf := by
  obtain ⟨ty₁, c₁', bty, c', hpred, hext, hty, htyof, hc⟩ := type_of_pred_extHasAttr_inversion h₃
  have ⟨v₁, hev₁, hio₁⟩ := ih h₂ hit hpred
  have heval_ext : evaluatePred (.extHasAttr x₁ a as') it request entities =
      (evaluatePred x₁ it request entities >>= fun v => hasAttrs v a as' entities) := by
    simp [evaluatePred]
  rw [htyof]
  simp only [EvaluatesToPred] at hev₁
  rcases hev₁ with ⟨err, hev₁⟩ | hev₁
  · obtain ⟨w, hw⟩ := type_is_inhabited_bool (env := env) (bty := bty)
    exact ⟨w, Or.inl ⟨err, by simp [heval_ext, hev₁]⟩, hw⟩
  · cases hha : hasAttrs v₁ a as' entities with
    | error e =>
      obtain ⟨w, hw⟩ := type_is_inhabited_bool (env := env) (bty := bty)
      exact ⟨w, Or.inl ⟨e, by simp [heval_ext, hev₁, hha]⟩, hw⟩
    | ok r =>
      have ⟨b, hb⟩ := hasAttrs_ok_is_bool_wk hha
      subst hb
      refine ⟨.prim (.bool b), ?_, ?_⟩
      · exact Or.inr (by simp [heval_ext, hev₁, hha])
      · apply InstanceOfType.instance_of_bool
        have hloop : hasAttrs.loop v₁ (a :: as') entities = .ok (.prim (.bool b)) := by
          simpa [hasAttrs] using hha
        exact typeOfExtHasAttr_bool_type_sound_wk h₂ hext hio₁ hloop

end Cedar.Thm
