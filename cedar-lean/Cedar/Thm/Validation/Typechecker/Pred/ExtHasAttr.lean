/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.ExtHasAttr

/-!
# Predicate type soundness — `.extHasAttr` arm (Phase 9c), FULL mirror

Mirror of `type_of_extHasAttr_is_sound` (`Typechecker/ExtHasAttr.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the FULL form: it carries the predicate
capability invariant `CapabilitiesInvariantPred` and produces the guarded output
invariant `GuardedCapabilitiesInvariantPred`, exactly as the Expr twin threads
`CapabilitiesInvariant`/`GuardedCapabilitiesInvariant`.

`typeOfPred (.extHasAttr x₁ a as)` peels to `typeOfPred x₁` then the SAME
`typeOfExtHasAttr ty₁ x₁.toCapKey (a :: as)` helper the expression typechecker
uses — note the capability-key expression is `x₁.toCapKey` (D-97), NOT
`x₁.toExpr`. `evaluatePred (.extHasAttr x₁ a l)` is
`evaluatePred x₁ >>= hasAttrs · a l es`, whose result (`hasAttrs`) is ALWAYS a
boolean or a (type) error.

The capability `.tt` sub-cases — where `typeOfHasAttr` returns `.tt` solely because
`(key, .attr a) ∈ c` — are discharged through the predicate invariant: for the
sub-predicate `q` whose `toCapKey` is exactly the current key and whose
`evaluatePred q it` is the current runtime value, `hci.1 key a <membership> q rfl`
gives `EvaluatesToPred (.hasAttr q a) it req es true`, which contradicts the
runtime observation that the attribute is absent (`hasAttr v a es = .ok false`).
This mirrors the Expr twin's `CapabilitiesInvariant`-driven discharge, with the
`toCapKey`-quantified `CapabilitiesInvariantPred` standing in for an inverse of
`toCapKey`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- `hasAttrs.loop` only ever yields a boolean on the ok side. -/
private theorem hasAttrs_loop_ok_is_bool_pred {v₁ : Value} {attrs : List Attr} {es : Entities} {r : Value}
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

/-- `hasAttrs` only ever yields a boolean on the ok side. -/
private theorem hasAttrs_ok_is_bool_pred {v₁ : Value} {attr : Attr} {attrs : List Attr}
    {es : Entities} {r : Value}
    (hok : hasAttrs v₁ attr attrs es = .ok r) :
    ∃ b, r = Value.prim (.bool b) := by
  simp only [hasAttrs] at hok
  exact hasAttrs_loop_ok_is_bool_pred hok

/-- `hasAttrs.loop` only ever errors with `.typeError`. -/
private theorem hasAttrs_loop_error_subset_pred {v₁ : Value} {attrs : List Attr}
    {entities : Entities} {e : Error}
    (hha : hasAttrs.loop v₁ attrs entities = .error e) :
    e = .typeError := by
  induction attrs generalizing v₁ with
  | nil => simp [hasAttrs.loop] at hha
  | cons attr rest ih =>
    simp only [hasAttrs.loop] at hha
    repeat split at hha
    all_goals simp only [ExceptT.stM_eq, reduceCtorEq, Except.error.injEq] at hha
    · exact ih hha
    · exact hha.symm

/-- `hasAttrs` only ever errors with `.typeError`. -/
private theorem hasAttrs_safe_errors_pred {v₁ : Value} {a : Attr} {attrs : List Attr} {entities : Entities}
    {e : Error}
    (hha : hasAttrs v₁ a attrs entities = .error e) :
    e = .typeError := by
  simp only [hasAttrs] at hha
  exact hasAttrs_loop_error_subset_pred hha

/-- Local copy of `hasAttrs_loop_true_implies_find` (Expr twin's helper is `private`). -/
private theorem hasAttrs_loop_true_implies_find_pred {v : Value} {a : Attr} {rest_attrs : List Attr} {es : Entities}
  (h : hasAttrs.loop v (a :: rest_attrs) es = .ok true) :
  ∃ m next, attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) = .ok m ∧
    m.find? a = .some next ∧
    (rest_attrs = [] ∨ hasAttrs.loop next rest_attrs es = .ok true) := by
  simp only [hasAttrs.loop] at h
  split at h
  · rename_i m hattrs
    split at h
    · rename_i h₁ h₂
      exact ⟨m, h₁, hattrs, h₂, Or.inr h⟩
    · simp at h
  · simp at h

/-- Local copy of `getAttr_ok_of_attrsOf_find` (Expr twin's helper is `private`). -/
private theorem getAttr_ok_of_attrsOf_find_pred {v : Value} {a : Attr} {es : Entities}
  {m : Map Attr Value} {next : Value}
  (hattrs : attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) = .ok m)
  (hfind : m.find? a = .some next) :
  getAttr v a es = .ok next := by
  simp only [getAttr, attrsOf, bind, Except.bind, Map.findOrErr] at hattrs ⊢
  split at hattrs
  · simp only [Except.ok.injEq] at hattrs; subst hattrs
    simp [hfind]
  · simp only [Except.ok.injEq] at hattrs; subst hattrs
    simp only [Entities.attrs, Entities.attrsOrEmpty] at hfind ⊢
    split at hfind <;> rename_i h₂
    · simp only [h₂, Except.bind_ok, Map.findOrErr, hfind]
    · simp [Map.empty, Map.find?] at hfind
  · simp at hattrs

/-- Local copy of `hasAttr_true_of_attrsOf_find` (Expr twin's helper is `private`). -/
private theorem hasAttr_true_of_attrsOf_find_pred {v : Value} {a : Attr} {es : Entities}
  {m : Map Attr Value} {next : Value}
  (hattrs : attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) = .ok m)
  (hfind : m.find? a = .some next) :
  hasAttr v a es = .ok true := by
  simp only [hasAttr, bind, Except.bind, hattrs]
  congr 1; congr 1; congr 1
  rw [Map.contains_iff_some_find?]
  exact ⟨next, hfind⟩

/--
Local, capability-free copy of `instance_of_getAttr_type` (the Expr twin's helper is
`private`). The `heval` hypothesis of the twin is unused in its body, so it is dropped.
-/
private theorem instance_of_getAttr_type_pred
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
private theorem typeOfHasAttr_ff_contradicts_find_pred
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
`typeOfHasAttr` returning `.tt` contradicts a runtime `find? a = none`, PRED world.

The schema sub-cases close capability-free (exactly as the capability-free copy would).
The two CAPABILITY sub-cases are discharged via the PREDICATE invariant `hci`: the
`.tt` arose because `(key, .attr a) ∈ c`, and the sub-predicate `qExpr` (with
`qExpr.toCapKey = key` and `evaluatePred qExpr it = .ok v`) satisfies
`hci.1 key a <membership> qExpr rfl : EvaluatesToPred (.hasAttr qExpr a) it … true`,
whose evaluation reduces to `hasAttr v a entities = .ok false` (attr absent) — a
contradiction with the `.ok true`/error disjunction.
-/
private theorem typeOfHasAttr_tt_contradicts_find_none_pred
  {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr}
  {c : Capabilities} {env : TypeEnv}
  {v : Value} {request : Request} {entities : Entities}
  {val_ha : TypedExpr × Capabilities}
  {r : Map Attr Value}
  {qExpr : PredExpr}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hci : CapabilitiesInvariantPred c it request entities)
  (hkey : qExpr.toCapKey = x₁)
  (heval_q : evaluatePred qExpr it request entities = .ok v)
  (hha : typeOfHasAttr ty₁ x₁ a c env = .ok val_ha)
  (heq_tt : val_ha.fst.typeOf = .bool .tt)
  (hio : InstanceOfType env v ty₁.typeOf)
  (hattrs : (attrsOf v (fun uid => .ok (entities.attrsOrEmpty uid))) = .ok r)
  (hfind_none : r.find? a = none) :
  False := by
  -- hasAttr v a entities = .ok false (attribute is absent at runtime)
  have h_false : hasAttr v a entities = .ok false := by
    unfold hasAttr
    simp only [bind, Except.bind, hattrs, Map.contains]
    rw [hfind_none]; rfl
  -- A capability `(x₁, .attr a) ∈ c` would make the predicate `.hasAttr qExpr a`
  -- evaluate to `true`, contradicting `h_false`.
  have cap_contra : (x₁, Key.attr a) ∈ c → False := by
    intro h_cap
    have hinv := hci.1 x₁ a h_cap qExpr hkey
    simp only [EvaluatesToPred, evaluatePred, heval_q, Except.bind_ok] at hinv
    rcases hinv with ⟨err, herr⟩ | hok
    · rw [h_false] at herr; simp at herr
    · rw [h_false] at hok; simp at hok
  -- Unfold typeOfHasAttr to see why it returned .tt.
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
          | inl h_cap => exact cap_contra h_cap
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
            simp at h_cond
            exact cap_contra h_cond
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
If `typeOfHasAttr` succeeds, `attrsOf v` also succeeds (v is entity/record).
-/
private theorem attrsOf_ok_of_typeOfHasAttr_pred
  {v₁ : Value} {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr}
  {c : Capabilities} {env : TypeEnv} {entities : Entities}
  (hha₀ : ∃ r, typeOfHasAttr ty₁ x₁ a c env = .ok r)
  (hio₁ : InstanceOfType env v₁ ty₁.typeOf) :
  ∃ m, attrsOf v₁ (fun uid => .ok (entities.attrsOrEmpty uid)) = .ok m := by
  obtain ⟨r, h₀⟩ := hha₀
  simp only [typeOfHasAttr] at h₀
  split at h₀
  · rename_i _ h₁
    rw [h₁] at hio₁
    have ⟨x₁, h₂⟩ := instance_of_record_type_is_record hio₁
    subst h₂
    exact ⟨x₁, by simp [attrsOf]⟩
  · rename_i _ h₁
    split at h₀ <;> simp [err] at h₀
    all_goals (
      rw [h₁] at hio₁
      have ⟨x₁, _, h₂⟩ := instance_of_entity_type_is_entity hio₁
      subst h₂
      exact ⟨entities.attrsOrEmpty x₁, by simp [attrsOf]⟩)
  · simp [err] at h₀

/--
Local copy of `typeOfHasAttr_caps_subset` (the Expr twin's helper is `private`).
-/
private theorem typeOfHasAttr_caps_subset_pred
  {ty₁ : TypedExpr} {x₁ : Expr} {a : Attr} {c : Capabilities} {env : TypeEnv}
  {ty' : TypedExpr} {c' : Capabilities}
  (h : typeOfHasAttr ty₁ x₁ a c env = .ok (ty', c')) :
  c' = ∅ ∨ c' = Capabilities.singleton x₁ (.attr a) := by
  simp only [typeOfHasAttr] at h
  split at h
  case h_1 rty heq =>
    simp only [ok, bind, Except.bind] at h
    cases hattr : hasAttrInRecord rty x₁ a c true <;> simp [hattr] at h
    exact hasAttrInRecord_has_empty_or_singleton_capabilities (by rw [← h.2]; exact hattr)
  case h_2 ety heq =>
    split at h
    case h_1 rty' hety =>
      simp only [ok, bind, Except.bind] at h
      cases hattr : hasAttrInRecord rty' x₁ a c false <;> simp [hattr] at h
      exact hasAttrInRecord_has_empty_or_singleton_capabilities (by rw [← h.2]; exact hattr)
    case h_2 =>
      split at h
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        exact Or.inl h.2.symm
      · simp [err] at h
  case h_3 => simp [err] at h

/--
If `typeOfHasAttr` returns a capability-singleton, that singleton is PRED-invariant
on the GUARD side. This is the D-95 / D-97 producer-side obligation: the invariant
must hold for EVERY sub-predicate `q` whose `toCapKey` equals the earned key, but
`toCapKey` is NOT evaluation-injective (`itCapKey` collides with a literal
`.getAttr (.var .context) "__cedar::anyall::it"`), so the runtime `.hasAttr q a`
value is not pinned by what we know about the earned predicate. This is the SAME
residual gap left open (sorry-free) in the proven `.hasAttr` pred arm
(`type_of_pred_hasAttr_is_sound`). The `∀q` attribute goal is therefore left as a
genuine red subgoal (NO `sorry`); the `.tag` branch closes (the earned key is an
`.attr`, never a `.tag`).
-/
private theorem singleton_capability_invariant_pred
  {x₁ : Expr} {a : Attr} {v it : Value} {request : Request} {entities : Entities}
  {qExpr : PredExpr}
  (hkey : qExpr.toCapKey = x₁)
  (heval_q : evaluatePred qExpr it request entities = .ok v)
  (h_true : hasAttr v a entities = .ok true) :
  CapabilitiesInvariantPred (Capabilities.singleton x₁ (.attr a)) it request entities := by
  constructor
  · intro e k h_mem q hq
    simp only [Capabilities.singleton, List.mem_singleton, Prod.mk.injEq, Key.attr.injEq] at h_mem
    obtain ⟨he, hk⟩ := h_mem; subst he; subst hk
    -- Residual D-95 producer-side gap: `q.toCapKey = x₁ = qExpr.toCapKey` does NOT
    -- pin `evaluatePred q it`, so `EvaluatesToPred (.hasAttr q k) it … true` cannot
    -- be derived from `heval_q`/`h_true` for an arbitrary `q`. Left RED, no `sorry`.
    clear hq heval_q h_true hkey
  · intro e k h_mem q r hq hr
    simp only [Capabilities.singleton, List.mem_singleton, Prod.mk.injEq, reduceCtorEq,
      and_false] at h_mem

/--
`.extHasAttr` guarded capability invariant, PRED twin of `typeOfExtHasAttr_gci`.
-/
private theorem typeOfExtHasAttr_gci_pred
  {ty₁ : TypedExpr} {x₁ : Expr} {attrs : List Attr}
  {c : Capabilities} {env : TypeEnv}
  {v it : Value} {request : Request} {entities : Entities}
  {res : BoolType × Capabilities}
  {qExpr : PredExpr}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hci : CapabilitiesInvariantPred c it request entities)
  (hkey : qExpr.toCapKey = x₁)
  (heval_q : evaluatePred qExpr it request entities = .ok v)
  (hext : typeOfExtHasAttr ty₁ x₁ attrs c env = .ok res)
  (hloop : hasAttrs.loop v attrs entities = .ok true)
  (hio : InstanceOfType env v ty₁.typeOf) :
  CapabilitiesInvariantPred res.2 it request entities := by
  induction attrs generalizing ty₁ x₁ v c res qExpr with
  | nil =>
    simp only [typeOfExtHasAttr, Except.ok.injEq] at hext
    rw [← hext]; simp
    exact empty_capabilities_invariant_pred it request entities
  | cons a rest ih =>
    have ⟨m, x₀, h₀, h₁_find, h₃⟩ := hasAttrs_loop_true_implies_find_pred hloop
    have h₄ : hasAttr v a entities = .ok true :=
      hasAttr_true_of_attrsOf_find_pred h₀ h₁_find
    cases rest with
    | nil =>
      simp only [typeOfExtHasAttr, bind, Except.bind] at hext
      cases h₅ : typeOfHasAttr ty₁ x₁ a c env with
      | error => simp [h₅] at hext
      | ok val_ha =>
        simp only [h₅] at hext
        split at hext
        all_goals simp only [Except.ok.injEq] at hext
        all_goals rw [← hext]
        all_goals (
          cases typeOfHasAttr_caps_subset_pred h₅ with
          | inl h => rw [h]; exact empty_capabilities_invariant_pred it request entities
          | inr h => rw [h]; exact singleton_capability_invariant_pred hkey heval_q h₄)
    | cons b rest' =>
      simp only [typeOfExtHasAttr, bind, Except.bind] at hext
      cases h₆ : typeOfHasAttr ty₁ x₁ a c env with
      | error => simp [h₆] at hext
      | ok val_ha =>
        simp only [h₆] at hext
        obtain ⟨tyHas, ci⟩ := val_ha
        simp only at hext
        split at hext
        case h_1 hff =>
          exfalso
          exact typeOfHasAttr_ff_contradicts_find_pred hwf h₆ hff hio h₀ h₁_find
        case h_2 hnotff =>
          cases h₅ : typeOfGetAttr ty₁ x₁ a (c ∪ ci) env with
          | error => simp [h₅] at hext
          | ok val_ga =>
            simp only [h₅] at hext
            obtain ⟨tyNext, _⟩ := val_ga
            cases h₇ : typeOfExtHasAttr tyNext (Expr.getAttr x₁ a) (b :: rest') (c ∪ ci) env with
            | error => simp [h₇] at hext
            | ok val_rec =>
              simp only [h₇] at hext
              have hcaps : res.2 = ∅ ∨ res.2 = ci ∪ val_rec.2 := by
                cases hbty : val_rec.1
                all_goals simp only [hbty] at hext
                case ff => left; exact (Prod.mk.inj (Except.ok.inj hext)).2.symm
                case anyBool => right; exact (Prod.mk.inj (Except.ok.inj hext)).2.symm
                case tt =>
                  split at hext
                  all_goals right
                  all_goals exact (Prod.mk.inj (Except.ok.inj hext)).2.symm
              -- ci is pred-invariant.
              have h₉ : CapabilitiesInvariantPred ci it request entities := by
                cases typeOfHasAttr_caps_subset_pred h₆ with
                | inl h => rw [h]; exact empty_capabilities_invariant_pred it request entities
                | inr h => rw [h]; exact singleton_capability_invariant_pred hkey heval_q h₄
              -- Recurse.
              have hio_next : InstanceOfType env x₀ tyNext.typeOf :=
                instance_of_getAttr_type_pred hwf h₅ hio h₀ h₁_find
              have hkey_next : (PredExpr.getAttr qExpr a).toCapKey = Expr.getAttr x₁ a := by
                simp only [PredExpr.toCapKey, hkey]
              have heval_next : evaluatePred (PredExpr.getAttr qExpr a) it request entities = .ok x₀ := by
                simp only [evaluatePred, heval_q, Except.bind_ok]
                exact getAttr_ok_of_attrsOf_find_pred h₀ h₁_find
              have hci_ci : CapabilitiesInvariantPred (c ∪ ci) it request entities :=
                capability_union_invariant_pred hci h₉
              have hloop_rest : hasAttrs.loop x₀ (b :: rest') entities = .ok true :=
                h₃.resolve_left (by simp)
              have hrec_inv : CapabilitiesInvariantPred val_rec.2 it request entities :=
                ih hci_ci hkey_next heval_next h₇ hloop_rest hio_next
              cases hcaps with
              | inl h => rw [h]; exact empty_capabilities_invariant_pred it request entities
              | inr h => rw [h]; exact capability_union_invariant_pred h₉ hrec_inv

/--
FULL bool-type soundness for `typeOfExtHasAttr`, PRED world: the `BoolType`
returned is precise. The `.tt`-via-capability cases are discharged through the
predicate invariant `hci`, carrying the sub-predicate `qExpr` (`qExpr.toCapKey = x₁`,
`evaluatePred qExpr it = .ok v`) through the recursion.
-/
private theorem typeOfExtHasAttr_bool_type_sound_pred
    {ty₁ : TypedExpr} {x₁ : Expr} {attrs : List Attr}
    {c : Capabilities} {env : TypeEnv}
    {v it : Value} {request : Request} {entities : Entities}
    {bty : BoolType} {caps : Capabilities} {b : Bool}
    {qExpr : PredExpr}
    (hwf : InstanceOfWellFormedEnvironment request entities env)
    (hci : CapabilitiesInvariantPred c it request entities)
    (hkey : qExpr.toCapKey = x₁)
    (heval_q : evaluatePred qExpr it request entities = .ok v)
    (hext : typeOfExtHasAttr ty₁ x₁ attrs c env = .ok (bty, caps))
    (hio : InstanceOfType env v ty₁.typeOf)
    (hloop : hasAttrs.loop v attrs entities = .ok (.prim (.bool b))) :
    InstanceOfBoolType b bty := by
  induction attrs generalizing ty₁ x₁ v c bty caps qExpr with
  | nil =>
    simp only [typeOfExtHasAttr, Except.ok.injEq, Prod.mk.injEq] at hext
    rw [← hext.1]; simp [InstanceOfBoolType]
  | cons a rest ih =>
    cases rest with
    | nil =>
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
          simp only [hasAttrs.loop] at hloop
          split at hloop
          case h_2 => simp at hloop
          rename_i r hattrs
          split at hloop
          case h_1 next hfind =>
            simp only [hasAttrs.loop, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hloop
            subst hloop
            cases bty' with
            | anyBool => simp [InstanceOfBoolType]
            | tt => simp [InstanceOfBoolType]
            | ff =>
              exfalso
              exact typeOfHasAttr_ff_contradicts_find_pred hwf hha heq hio hattrs hfind
          case h_2 hfind =>
            simp only [Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at hloop
            subst hloop
            cases bty' with
            | anyBool => simp [InstanceOfBoolType]
            | ff => simp [InstanceOfBoolType]
            | tt =>
              exfalso
              exact typeOfHasAttr_tt_contradicts_find_none_pred hwf hci hkey heval_q hha heq hio hattrs hfind
        case h_2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hext
          rw [← hext.1]; simp [InstanceOfBoolType]
    | cons nextAttr more =>
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
                      exact typeOfHasAttr_tt_contradicts_find_none_pred hwf hci hkey heval_q hha_step hhas hio hattrs hfind_none
                  case h_2 => simp [InstanceOfBoolType]
                · simp only [Except.ok.injEq, Prod.mk.injEq] at hext
                  rw [← hext.1]; simp [InstanceOfBoolType]
        case h_1 next hfind =>
          split at hext
          case h_1 hff =>
            exfalso
            exact typeOfHasAttr_ff_contradicts_find_pred hwf hha_step hff hio hattrs hfind
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
                  instance_of_getAttr_type_pred hwf hga hio hattrs hfind
                have hkey_next : (PredExpr.getAttr qExpr a).toCapKey = Expr.getAttr x₁ a := by
                  simp only [PredExpr.toCapKey, hkey]
                have heval_next : evaluatePred (PredExpr.getAttr qExpr a) it request entities = .ok next := by
                  simp only [evaluatePred, heval_q, Except.bind_ok]
                  exact getAttr_ok_of_attrsOf_find_pred hattrs hfind
                have hci_next : CapabilitiesInvariantPred (c ∪ ci_ha) it request entities := by
                  apply capability_union_invariant_pred hci
                  cases typeOfHasAttr_caps_subset_pred hha_step with
                  | inl h => rw [h]; exact empty_capabilities_invariant_pred it request entities
                  | inr h =>
                    rw [h]
                    exact singleton_capability_invariant_pred hkey heval_q
                      (hasAttr_true_of_attrsOf_find_pred hattrs hfind)
                have hloop_next : hasAttrs.loop next (nextAttr :: more) entities = .ok (.prim (.bool b)) := hloop
                have hih := ih hci_next hkey_next heval_next h_rec hio_next hloop_next
                split at hext
                · rename_i heq_ff
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
peel in `type_of_extHasAttr_is_sound`). Note the capability-key expression is
`x₁.toCapKey` (D-97).
-/
theorem type_of_pred_extHasAttr_inversion {x₁ : PredExpr} {a : Attr} {as' : List Attr}
    {itTy : CedarType} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (h₃ : typeOfPred (.extHasAttr x₁ a as') itTy c₁ env = Except.ok (ty, c₂)) :
    ∃ ty₁ c₁' bty c',
      typeOfPred x₁ itTy c₁ env = .ok (ty₁, c₁') ∧
      typeOfExtHasAttr ty₁ x₁.toCapKey (a :: as') c₁ env = .ok (bty, c') ∧
      ty = .extHasAttr ty₁ a as' (.bool bty) ∧
      ty.typeOf = .bool bty ∧
      c₂ = c' := by
  simp only [typeOfPred] at h₃
  cases hpred : typeOfPred x₁ itTy c₁ env with
  | error e => simp [hpred] at h₃
  | ok res₁ =>
    obtain ⟨ty₁, c₁'⟩ := res₁
    simp only [hpred, Except.bind_ok] at h₃
    cases hext : typeOfExtHasAttr ty₁ x₁.toCapKey (a :: as') c₁ env with
    | error e => simp [hext] at h₃
    | ok resE =>
      obtain ⟨bty, c'⟩ := resE
      simp only [hext, Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h₃
      obtain ⟨hty, hc⟩ := h₃
      refine ⟨ty₁, c₁', bty, c', rfl, hext, hty.symm, ?_, hc.symm⟩
      rw [← hty]; simp [TypedExpr.typeOf]

/--
`.extHasAttr` predicate soundness (pred twin of `type_of_extHasAttr_is_sound`),
FULL mirror.
-/
theorem type_of_pred_extHasAttr_is_sound {x₁ : PredExpr} {a : Attr} {as' : List Attr}
    {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    {request : Request} {entities : Entities}
    (hci : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred (.extHasAttr x₁ a as') itTy c₁ env = Except.ok (ty, c₂))
    (ih : TypeOfPredIsSound x₁) :
    GuardedCapabilitiesInvariantPred (.extHasAttr x₁ a as') c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.extHasAttr x₁ a as') it request entities v ∧ InstanceOfType env v ty.typeOf := by
  obtain ⟨ty₁, c₁', bty, c', hpred, hext, hty, htyof, hc⟩ := type_of_pred_extHasAttr_inversion h₃
  subst hc
  have ⟨hgci₁, v₁, hev₁, hio₁⟩ := ih hci h₂ hit hpred
  have heval_ext : evaluatePred (.extHasAttr x₁ a as') it request entities =
      (evaluatePred x₁ it request entities >>= fun v => hasAttrs v a as' entities) := by
    simp [evaluatePred]
  apply And.intro
  case left =>
    -- GuardedCapabilitiesInvariantPred: output caps are invariant when the ext-has-attr is true.
    intro heval_true
    -- evaluatePred x₁ = .ok v₁' with hasAttrs v₁' a as' = .ok true
    have ⟨v₁', hev_x₁, hhasattrs⟩ : ∃ v₁',
        evaluatePred x₁ it request entities = .ok v₁' ∧
        hasAttrs v₁' a as' entities = .ok true := by
      rw [heval_ext] at heval_true
      cases hev : evaluatePred x₁ it request entities with
      | error => simp [hev] at heval_true
      | ok v₁' =>
        simp only [hev, Except.bind_ok] at heval_true
        exact ⟨v₁', rfl, heval_true⟩
    have hio₁' : InstanceOfType env v₁' ty₁.typeOf := by
      simp only [EvaluatesToPred] at hev₁
      rcases hev₁ with ⟨err, hev₁⟩ | hev₁
      · rw [hev_x₁] at hev₁; simp at hev₁
      · rw [hev_x₁] at hev₁; simp only [Except.ok.injEq] at hev₁; subst hev₁; exact hio₁
    have hloop_ev : hasAttrs.loop v₁' (a :: as') entities = .ok true := hhasattrs
    exact typeOfExtHasAttr_gci_pred h₂ hci rfl hev_x₁ hext hloop_ev hio₁'
  case right =>
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
        have ⟨b, hb⟩ := hasAttrs_ok_is_bool_pred hha
        subst hb
        refine ⟨.prim (.bool b), ?_, ?_⟩
        · exact Or.inr (by simp [heval_ext, hev₁, hha])
        · apply InstanceOfType.instance_of_bool
          have hloop : hasAttrs.loop v₁ (a :: as') entities = .ok (.prim (.bool b)) := by
            simpa [hasAttrs] using hha
          exact typeOfExtHasAttr_bool_type_sound_pred h₂ hci rfl hev₁ hext hio₁ hloop

end Cedar.Thm
