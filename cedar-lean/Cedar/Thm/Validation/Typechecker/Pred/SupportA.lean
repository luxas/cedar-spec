/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.Pred.Record
import Cedar.Thm.Validation.Typechecker.Pred.HasAttr

/-!
# Predicate output-type well-formedness (Phase 9c, arm A, D-P9c-8)

Support lemma for the `.getAttr` predicate-soundness arm: a well-typed predicate
produces a well-formed result type, GIVEN that both the environment and the
element type `itTy` are well formed.

The expression-side `typechecked_has_well_formed_type` routes through
`TypedExpr.WellTyped` after lifting, but that route is unavailable for predicates:
`.item` types to `.var .principal itTy`, which is `WellTyped` only when `itTy` is
the request's principal type — an assumption a general predicate cannot carry.
Instead we induct structurally on `typeOfPred` directly, mirroring
`well_typed_implies_wf_type` arm-for-arm. The `.item` arm is exactly where the
`itTy.WellFormed env` hypothesis (D-P9c-8) is discharged; every compound arm
reuses the per-operator helper's output type and the operand WF from the IH.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- `lubRecordType` keeps the left list's key sequence (it zips position-by-position,
requiring equal keys), so the output's key list equals the left input's. -/
theorem lubRecordType_keys_eq_left {rty₁ rty₂ rty : List (Attr × QualifiedType)}
    (h : lubRecordType rty₁ rty₂ = some rty) :
    rty.map Prod.fst = rty₁.map Prod.fst := by
  induction rty₁ generalizing rty₂ rty with
  | nil =>
    cases rty₂ <;> simp only [lubRecordType, Option.some.injEq, reduceCtorEq] at h
    simp only [← h, List.map_nil]
  | cons hd₁ tl₁ ih =>
    cases rty₂ with
    | nil => simp only [lubRecordType, reduceCtorEq] at h
    | cons hd₂ tl₂ =>
      simp only [lubRecordType, bne_iff_ne, ne_eq, Option.bind_eq_bind, ite_not,
        Option.ite_none_right_eq_some, Option.bind_eq_some_iff] at h
      obtain ⟨hk, qty, _, tys, htys, heq⟩ := h
      simp only [Option.some.injEq] at heq
      subst heq
      simp only [List.map_cons, List.cons.injEq, true_and]
      exact ih htys

/--
`lub?` preserves well-formedness: the LUB of two well-formed types is well
formed. Needed for the `.ite .anyBool` arm, whose result is `ty₂ ⊔ ty₃`. Mutual
with the record version, mirroring the structure of `lub?`.
-/
mutual
theorem lub_wf {env : TypeEnv} {ty₁ ty₂ ty : CedarType}
    (hwf₁ : ty₁.WellFormed env)
    (h : (ty₁ ⊔ ty₂) = some ty) :
    ty.WellFormed env := by
  match ty₁, ty₂ with
  | .bool _, .bool _ =>
    simp only [lub?, Option.some.injEq] at h
    subst h
    exact CedarType.WellFormed.bool_wf
  | .set s₁, .set s₂ =>
    simp only [lub?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨sty, h₂, heq⟩ := h
    subst heq
    cases hwf₁ with
    | set_wf hwf_elt =>
      exact CedarType.WellFormed.set_wf (lub_wf hwf_elt h₂)
  | .record (.mk r₁), .record (.mk r₂) =>
    simp only [lub?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨rty, h₂, heq⟩ := h
    subst heq
    cases hwf₁ with
    | record_wf hwf_map hwf_attrs =>
      -- `Map.mk rty` is WF (keys unchanged from `r₁`); each attr type WF via `lubRecordType_attrs_wf`.
      have hkeys := lubRecordType_keys_eq_left h₂
      have hsorted₁ : (Map.mk r₁).toList.SortedBy Prod.fst := (Map.wf_iff_sorted).mp hwf_map
      simp only [Map.toList] at hsorted₁
      have hwf_map' : (Map.mk rty).WellFormed :=
        Map.mk_wf ((List.map_eq_implies_sortedBy hkeys).mpr hsorted₁)
      have hlist : ∀ qty, qty ∈ r₁.map Prod.snd → QualifiedType.WellFormed env qty := by
        intro q hq
        simp only [List.mem_map] at hq
        obtain ⟨⟨a, q'⟩, hmem, heqq⟩ := hq
        subst heqq
        exact hwf_attrs a q' ((Map.in_list_iff_find?_some hwf_map).mp hmem)
      have hattrs := lubRecordType_attrs_wf hlist h₂
      apply CedarType.WellFormed.record_wf hwf_map'
      intro attr qty hfind
      apply hattrs
      simp only [List.mem_map]
      exact ⟨(attr, qty), (Map.in_list_iff_find?_some hwf_map').mpr hfind, rfl⟩
  | .bool _, .int | .bool _, .string | .bool _, .entity _ | .bool _, .set _
  | .bool _, .record _ | .bool _, .ext _
  | .int, _ | .string, _ | .entity _, _ | .ext _, _
  | .set _, .bool _ | .set _, .int | .set _, .string | .set _, .entity _
  | .set _, .record _ | .set _, .ext _
  | .record _, .bool _ | .record _, .int | .record _, .string | .record _, .entity _
  | .record _, .set _ | .record _, .ext _ =>
    -- the fall-through `if ty₁ = ty₂` arm of `lub?`
    simp only [lub?] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact hwf₁
    · simp only [reduceCtorEq] at h
termination_by sizeOf ty₁

/-- Each attribute type of a `lubRecordType` result is well formed, by structural
recursion on the left record type (so the cross-call to `lub_wf` is on a strictly
smaller element type). Returns per-attribute WF; the `Map` well-formedness of the
result is handled by the caller via `lubRecordType_keys_eq_left`. -/
theorem lubRecordType_attrs_wf {env : TypeEnv} {rty₁ rty₂ rty : List (Attr × QualifiedType)}
    (hwf_attrs : ∀ qty, qty ∈ rty₁.map Prod.snd → QualifiedType.WellFormed env qty)
    (h : lubRecordType rty₁ rty₂ = some rty) :
    ∀ qty, qty ∈ rty.map Prod.snd → QualifiedType.WellFormed env qty := by
  match rty₁, rty₂ with
  | [], [] =>
    simp only [lubRecordType, Option.some.injEq] at h
    simp only [← h, List.map_nil, List.not_mem_nil, false_implies, implies_true]
  | [], _ :: _ => simp only [lubRecordType, reduceCtorEq] at h
  | _ :: _, [] => simp only [lubRecordType, reduceCtorEq] at h
  | (ha₁, q₁) :: tl₁, hd₂ :: tl₂ =>
    simp only [lubRecordType, bne_iff_ne, ne_eq, Option.bind_eq_bind, ite_not,
      Option.ite_none_right_eq_some, Option.bind_eq_some_iff] at h
    obtain ⟨hk, qty, hq, tys, htys, heq⟩ := h
    simp only [Option.some.injEq] at heq
    subst heq
    have hhd₁ : QualifiedType.WellFormed env q₁ := by
      apply hwf_attrs; simp only [List.map_cons, List.mem_cons, true_or]
    have htl₁ : ∀ qty, qty ∈ tl₁.map Prod.snd → QualifiedType.WellFormed env qty := by
      intro q hq'; apply hwf_attrs; simp only [List.map_cons, List.mem_cons]; exact Or.inr hq'
    -- head: `qty = lubQualifiedType q₁ hd₂.snd`, WF from `hhd₁` + lub_wf
    have hqwf : QualifiedType.WellFormed env qty := lubQualifiedType_wf hhd₁ hq
    -- tail: recurse
    have htail := lubRecordType_attrs_wf htl₁ htys
    intro q hq'
    simp only [List.map_cons, List.mem_cons] at hq'
    rcases hq' with hq' | hq'
    · exact hq' ▸ hqwf
    · exact htail q hq'
termination_by sizeOf rty₁

/-- `lubQualifiedType` preserves well-formedness of the left operand. -/
theorem lubQualifiedType_wf {env : TypeEnv} {q₁ q₂ q : QualifiedType}
    (hwf₁ : QualifiedType.WellFormed env q₁)
    (h : lubQualifiedType q₁ q₂ = some q) :
    QualifiedType.WellFormed env q := by
  match q₁, q₂ with
  | .optional a₁, .optional a₂ =>
    simp only [lubQualifiedType, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨aty, haty, heqq⟩ := h; subst heqq
    cases hwf₁ with
    | optional_wf hwfa₁ => exact QualifiedType.WellFormed.optional_wf (lub_wf hwfa₁ haty)
  | .required a₁, .required a₂ =>
    simp only [lubQualifiedType, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨aty, haty, heqq⟩ := h; subst heqq
    cases hwf₁ with
    | required_wf hwfa₁ => exact QualifiedType.WellFormed.required_wf (lub_wf hwfa₁ haty)
  | .optional _, .required _ => simp only [lubQualifiedType, reduceCtorEq] at h
  | .required _, .optional _ => simp only [lubQualifiedType, reduceCtorEq] at h
termination_by sizeOf q₁
end

/-- Well-formedness of the `typeOfLit` result type. -/
theorem typeOfLit_wf {p : Prim} {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (hwf : env.WellFormed)
    (h : typeOfLit p env = Except.ok (tx, c')) :
    tx.typeOf.WellFormed env := by
  simp only [typeOfLit, Function.comp_apply] at h
  split at h
  case' h_5 uid =>
    -- entity: resolve the validity `if`
    split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    rename_i hvalid
    obtain ⟨htx, _⟩ := h; subst htx; simp only [TypedExpr.typeOf]
    apply CedarType.WellFormed.entity_wf
    simp only [EntityType.WellFormed]
    simp only [Bool.or_eq_true] at hvalid
    rcases hvalid with hets | hacts
    · apply Or.inl
      simp only [EntitySchema.isValidEntityUID] at hets
      simp only [EntitySchema.contains]
      split at hets
      · rename_i hsome; simp only [hsome, Option.isSome_some]
      · contradiction
    · apply Or.inr
      simp only [ActionSchema.IsActionEntityType]
      exact ⟨uid, hacts, rfl⟩
  all_goals (
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨htx, _⟩ := h; subst htx; simp only [TypedExpr.typeOf]
    first
    | exact CedarType.WellFormed.bool_wf
    | exact CedarType.WellFormed.int_wf
    | exact CedarType.WellFormed.string_wf)

/-- Well-formedness of the `typeOfVar` result type. -/
theorem typeOfVar_wf {v : Var} {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (hwf : env.WellFormed)
    (h : typeOfVar v env = Except.ok (tx, c')) :
    tx.typeOf.WellFormed env := by
  have ⟨hwf_principal, hwf_action, hwf_resource, hwf_context⟩ := wf_env_implies_wf_request hwf
  simp only [typeOfVar, Function.comp_apply] at h
  split at h <;> simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨htx, _⟩ := h <;> subst htx <;> simp only [TypedExpr.typeOf]
  · exact CedarType.WellFormed.entity_wf hwf_principal
  · apply CedarType.WellFormed.entity_wf
    simp only [EntityType.WellFormed]
    apply Or.inr
    simp only [ActionSchema.IsActionEntityType]
    exact ⟨env.reqty.action, hwf_action, rfl⟩
  · exact CedarType.WellFormed.entity_wf hwf_resource
  · exact hwf_context

/-- Well-formedness of the `typeOfUnaryApp` result type (always `.bool`/`.int`). -/
theorem typeOfUnaryApp_wf {op : UnaryOp} {ty₁ : TypedExpr} {tx : TypedExpr} {c' : Capabilities}
    {env : TypeEnv}
    (h : typeOfUnaryApp op ty₁ = Except.ok (tx, c')) :
    tx.typeOf.WellFormed env := by
  simp only [typeOfUnaryApp, Function.comp_apply] at h
  split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (obtain ⟨htx, _⟩ := h; subst htx; simp only [TypedExpr.typeOf]
     first | exact CedarType.WellFormed.bool_wf | exact CedarType.WellFormed.int_wf)

/-- `typeOfGetTag` returns the schema tag type, which is well formed. -/
theorem typeOfGetTag_wf {ety : EntityType} {x t : Expr} {c c' : Capabilities} {env : TypeEnv}
    {ty : CedarType}
    (hwf : env.WellFormed)
    (h : typeOfGetTag ety x t c env = Except.ok (ty, c')) :
    ty.WellFormed env := by
  simp only [typeOfGetTag] at h
  split at h
  · simp only [err, reduceCtorEq] at h
  · rename_i tty htags
    split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨hty, _⟩ := h; subst hty
    exact wf_env_implies_wf_tag_type hwf htags
  · simp only [err, reduceCtorEq] at h

/-- `typeOfHasTag` always returns a `.bool`. -/
theorem typeOfHasTag_wf {ety : EntityType} {x t : Expr} {c c' : Capabilities} {env : TypeEnv}
    {ty : CedarType}
    (h : typeOfHasTag ety x t c env = Except.ok (ty, c')) :
    ty.WellFormed env := by
  simp only [typeOfHasTag] at h
  repeat' split at h
  all_goals (
    first
    | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h; done)
    | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨hty, _⟩ := h; subst hty; exact CedarType.WellFormed.bool_wf))

/-- Well-formedness of the `typeOfBinaryApp` result type. The only non-`.bool`/`.int`
case is `.getTag`, whose result is the schema tag type (well formed by
`typeOfGetTag_wf`). -/
theorem typeOfBinaryApp_wf {op : BinaryOp} {ty₁ ty₂ : TypedExpr} {e₁ e₂ : Expr}
    {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (hwf : env.WellFormed)
    (h : typeOfBinaryApp op ty₁ ty₂ e₁ e₂ c env = Except.ok (tx, c')) :
    tx.typeOf.WellFormed env := by
  simp only [typeOfBinaryApp] at h
  split at h
  all_goals (
    first
    | (-- `.getTag`: result is the schema tag type
       simp only [bind, Except.bind] at h
       split at h <;> simp only [reduceCtorEq] at h
       rename_i v hgt
       obtain ⟨vt, vc⟩ := v
       simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨htx, hc⟩ := h; subst htx; simp only [TypedExpr.typeOf]
       exact typeOfGetTag_wf hwf hgt)
    | (-- `.hasTag`: result is `.bool`
       simp only [bind, Except.bind] at h
       split at h <;> simp only [reduceCtorEq] at h
       rename_i v hht
       obtain ⟨vt, vc⟩ := v
       simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨htx, hc⟩ := h; subst htx; simp only [TypedExpr.typeOf]
       exact typeOfHasTag_wf hht)
    | (-- `contains`/`containsAll`/`containsAny`: `ifLubThenBool` ⇒ `.bool`
       simp only [ifLubThenBool, bind, Except.bind] at h
       split at h <;> simp only [reduceCtorEq] at h
       rename_i v hlub
       obtain ⟨vt, vc⟩ := v
       simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨htx, hc⟩ := h; subst htx; simp only [TypedExpr.typeOf]
       -- `ifLubThenBool` only ever yields `.bool .anyBool`
       simp only [ifLubThenBool] at hlub
       split at hlub <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at hlub
       obtain ⟨hvt, _⟩ := hlub; subst hvt; exact CedarType.WellFormed.bool_wf)
    | (-- `.eq`: result `.bool`
       simp only [typeOfEq, Function.comp_apply] at h
       have hbool : ∃ bty, tx.typeOf = .bool bty := by
         repeat' split at h
         all_goals (
           first
           | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h; done)
           | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨htx, _⟩ := h; subst htx; exact ⟨_, rfl⟩))
       obtain ⟨bty, hbty⟩ := hbool; rw [hbty]; exact CedarType.WellFormed.bool_wf)
    | (-- direct arms `.mem` / `.less` / `.lessEq` ⇒ bool, `.add`/`.sub`/`.mul` ⇒ int
       simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
       obtain ⟨htx, _⟩ := h; subst htx; simp only [TypedExpr.typeOf]
       first | exact CedarType.WellFormed.bool_wf | exact CedarType.WellFormed.int_wf)
    | (simp only [err, reduceCtorEq] at h; done))

/-- Well-formedness of the `typeOfHasAttr` result type (always `.bool`). -/
theorem typeOfHasAttr_wf {ty₁ : TypedExpr} {e : Expr} {a : Attr} {c c' : Capabilities}
    {env : TypeEnv} {tx : TypedExpr}
    (h : typeOfHasAttr ty₁ e a c env = Except.ok (tx, c')) :
    tx.typeOf.WellFormed env := by
  -- `typeOfHasAttr` always wraps a `hasAttrInRecord`/`.bool .ff` result into a
  -- `.hasAttr _ _ ty'` whose `ty'` is a `.bool`.
  have hbool : ∃ bty, tx.typeOf = .bool bty := by
    simp only [typeOfHasAttr, Function.comp_apply, bind, Except.bind] at h
    split at h
    case h_1 rty hrty =>
      split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      rename_i heqr
      obtain ⟨htx, _⟩ := h; subst htx
      obtain ⟨bty, hbty⟩ := hasAttrInRecord_result_is_bool heqr
      exact ⟨bty, by simp only [TypedExpr.typeOf, hbty]⟩
    case h_2 ety hety =>
      split at h
      · split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
        rename_i heqr
        obtain ⟨htx, _⟩ := h; subst htx
        obtain ⟨bty, hbty⟩ := hasAttrInRecord_result_is_bool heqr
        exact ⟨bty, by simp only [TypedExpr.typeOf, hbty]⟩
      · split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
        obtain ⟨htx, _⟩ := h; subst htx
        exact ⟨.ff, by simp only [TypedExpr.typeOf]⟩
    case h_3 => simp only [err, reduceCtorEq] at h
  obtain ⟨bty, hbty⟩ := hbool
  rw [hbty]; exact CedarType.WellFormed.bool_wf

/-- `getAttrInRecord` returns an attribute type that is well formed when the record
type is well formed. -/
theorem getAttrInRecord_wf {ty : CedarType} {rty : RecordType} {e : Expr} {a : Attr}
    {c c' : Capabilities} {env : TypeEnv} {aty : CedarType}
    (hwfrty : CedarType.WellFormed env (.record rty))
    (h : getAttrInRecord ty rty e a c = Except.ok (aty, c')) :
    aty.WellFormed env := by
  simp only [getAttrInRecord] at h
  cases hfind : rty.find? a with
  | none => rw [hfind] at h; simp only [err, reduceCtorEq] at h
  | some q =>
    rw [hfind] at h
    cases q with
    | required aty' =>
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨heqa, _⟩ := h; subst heqa
      simpa only [Qualified.getType] using
        qty_wf_implies_type_of_wf (wf_record_implies_wf_attr hwfrty hfind)
    | optional aty' =>
      split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      obtain ⟨heqa, _⟩ := h; subst heqa
      simpa only [Qualified.getType] using
        qty_wf_implies_type_of_wf (wf_record_implies_wf_attr hwfrty hfind)

/-- Well-formedness of the `typeOfGetAttr` result type, given the receiver type is
well formed (record receiver) or from the schema (entity receiver). -/
theorem typeOfGetAttr_wf {ty₁ : TypedExpr} {e : Expr} {a : Attr} {c c' : Capabilities}
    {env : TypeEnv} {tx : TypedExpr}
    (hwf : env.WellFormed)
    (hty₁ : ty₁.typeOf.WellFormed env)
    (h : typeOfGetAttr ty₁ e a c env = Except.ok (tx, c')) :
    tx.typeOf.WellFormed env := by
  simp only [typeOfGetAttr, Function.comp_apply, bind, Except.bind] at h
  split at h
  · -- record receiver `.record rty`: WF from `hty₁`
    rename_i rty hrty
    rw [hrty] at hty₁
    split at h <;> simp only [reduceCtorEq] at h
    rename_i aty hgar
    obtain ⟨at', ac⟩ := aty
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨htx, _⟩ := h; subst htx; simp only [TypedExpr.typeOf]
    exact getAttrInRecord_wf hty₁ hgar
  · -- entity receiver `.entity ety`: WF of the schema attrs record
    rename_i ety hety
    split at h <;> try simp only [err, reduceCtorEq] at h
    rename_i rty hattrs
    have hwfrty : CedarType.WellFormed env (.record rty) := wf_env_implies_wf_attrs hwf hattrs
    split at h <;> simp only [reduceCtorEq] at h
    rename_i aty hgar
    obtain ⟨at', ac⟩ := aty
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨htx, _⟩ := h; subst htx; simp only [TypedExpr.typeOf]
    exact getAttrInRecord_wf hwfrty hgar
  · simp only [err, reduceCtorEq] at h
    · simp only [err, reduceCtorEq] at h
  · simp only [err, reduceCtorEq] at h

/-- Well-formedness of the `typeOfCall` result type (always a scalar/ext/bool
constructor type, no record/set/entity). -/
theorem typeOfCall_wf {f : ExtFun} {tys : List TypedExpr} {xs : List Expr}
    {c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h : typeOfCall f tys xs = Except.ok (tx, c')) :
    tx.typeOf.WellFormed env := by
  simp only [typeOfCall, typeOfConstructor, Function.comp_apply, bind, Except.bind] at h
  repeat' split at h
  all_goals (try simp only [Except.bind_ok, Except.bind_err] at h)
  all_goals (
    first
    | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h; done)
    | (simp only [ok, err, Except.ok.injEq, Prod.mk.injEq] at h
       (try obtain ⟨htx, _⟩ := h)
       subst htx; simp only [TypedExpr.typeOf]
       first
       | exact CedarType.WellFormed.bool_wf
       | exact CedarType.WellFormed.int_wf
       | exact CedarType.WellFormed.ext_wf))

/--
**D-P9c-8.** A well-typed predicate's result type is well formed, given the
environment is well formed AND the element type `itTy` is well formed. Structural
induction on `typeOfPred`.
-/
theorem type_of_pred_implies_wf_type {p : PredExpr} {itTy : CedarType}
    {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (hwf : env.WellFormed)
    (hitwf : itTy.WellFormed env)
    (h : typeOfPred p itTy c env = Except.ok (tx, c')) :
    tx.typeOf.WellFormed env := by
  match p with
  | .item =>
    simp only [typeOfPred, ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨htx, _⟩ := h; subst htx; simpa only [TypedExpr.typeOf] using hitwf
  | .lit l =>
    simp only [typeOfPred] at h
    exact typeOfLit_wf hwf h
  | .var v =>
    simp only [typeOfPred] at h
    exact typeOfVar_wf hwf h
  | .ite x₁ x₂ x₃ =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred x₁ itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfPred x₂ itTy (c ∪ r₁.2) env <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₂
    cases h₃ : typeOfPred x₃ itTy c env <;> simp only [h₃, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₃
    have ih₂ := type_of_pred_implies_wf_type (p := x₂) hwf hitwf h₂
    have ih₃ := type_of_pred_implies_wf_type (p := x₃) hwf hitwf h₃
    simp only [typeOfIf] at h
    split at h <;>
      simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq, Except.bind_ok,
        Except.bind_err] at h
    · obtain ⟨htx, _⟩ := h; subst htx; simpa only [TypedExpr.typeOf] using ih₂
    · obtain ⟨htx, _⟩ := h; subst htx; simpa only [TypedExpr.typeOf] using ih₃
    · split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      rename_i hlub
      obtain ⟨htx, _⟩ := h; subst htx; simp only [TypedExpr.typeOf]
      exact lub_wf ih₂ hlub
  | .and x₁ x₂ =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred x₁ itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfPred x₂ itTy (c ∪ r₁.2) env <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₂
    -- `typeOfAnd` output is always `.bool`-typed: the `.ff` short-circuit keeps the
    -- (bool-typed) left operand; every other arm builds `.and _ _ (.bool _)`.
    have hbool : ∃ bty, tx.typeOf = .bool bty := by
      simp only [typeOfAnd, Except.bind_ok, bind, Except.bind] at h
      split at h
      case h_1 hg =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨htx, _⟩ := h; subst htx; exact ⟨.ff, hg⟩
      case h_2 bty₁ hg =>
        split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
          (obtain ⟨htx, _⟩ := h; subst htx; exact ⟨_, rfl⟩)
      case h_3 => simp only [err, reduceCtorEq] at h
    obtain ⟨bty, hbty⟩ := hbool; rw [hbty]; exact CedarType.WellFormed.bool_wf
  | .or x₁ x₂ =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred x₁ itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfPred x₂ itTy c env <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₂
    -- `typeOfOr` output is always `.bool`-typed: either the (bool-typed) short-circuit
    -- operand, or a freshly-built `.or _ _ (.bool _)`.
    have hbool : ∃ bty, tx.typeOf = .bool bty := by
      simp only [typeOfOr, Except.bind_ok, bind, Except.bind] at h
      split at h
      case h_1 hg =>
        -- `.tt` short-circuit: `tx = r₁.fst`, `r₁.fst.typeOf = .bool .tt`
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨htx, _⟩ := h; subst htx; exact ⟨.tt, hg⟩
      case h_2 hg =>
        -- `.ff`: inner match on `r₂.fst.typeOf`, output `.or _ _ r₂.fst.typeOf` (a bool)
        split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
        rename_i bty hr₂
        obtain ⟨htx, _⟩ := h; subst htx
        exact ⟨bty, by simp only [TypedExpr.typeOf]; exact hr₂⟩
      case h_3 hg₁ hg₂ =>
        -- `.anyBool` left: inner match on `r₂.fst.typeOf`, output `.or _ _ (.bool _)`
        split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
          (obtain ⟨htx, _⟩ := h; subst htx; exact ⟨_, by simp only [TypedExpr.typeOf]⟩)
      case h_4 => simp only [err, reduceCtorEq] at h
    obtain ⟨bty, hbty⟩ := hbool; rw [hbty]; exact CedarType.WellFormed.bool_wf
  | .unaryApp op x₁ =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred x₁ itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    exact typeOfUnaryApp_wf h
  | .binaryApp op x₁ x₂ =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred x₁ itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfPred x₂ itTy c env <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₂
    exact typeOfBinaryApp_wf hwf h
  | .hasAttr x₁ a =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred x₁ itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    exact typeOfHasAttr_wf h
  | .extHasAttr x₁ a attrs =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred x₁ itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfExtHasAttr r₁.1 x₁.toCapKey (a :: attrs) c env <;>
      simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨htx, _⟩ := h; subst htx; simp only [TypedExpr.typeOf]
    exact CedarType.WellFormed.bool_wf
  | .getAttr x₁ a =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred x₁ itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    have ih := type_of_pred_implies_wf_type (p := x₁) hwf hitwf h₁
    exact typeOfGetAttr_wf hwf ih h
  | .record axs =>
    have ⟨_, atxs, htx, hforall⟩ := type_of_pred_record_inversion h
    subst htx
    simp only [TypedExpr.typeOf]
    have hwf_rty : Map.WellFormed (Map.make (atxs.map λ (a, tx) => (a, Qualified.required tx.typeOf))) :=
      Map.make_wf _
    apply CedarType.WellFormed.record_wf hwf_rty
    intro attr qty hfind
    have hin := Map.mem_make_mem_list ((Map.in_list_iff_find?_some hwf_rty).mpr hfind)
    simp only [List.mem_map, Prod.mk.injEq, Prod.exists] at hin
    obtain ⟨a, tx', htx'mem, haeq, hqeq⟩ := hin
    subst hqeq
    apply QualifiedType.WellFormed.required_wf
    -- `tx'` is the typed sub-expression for attr `a`; its type is WF by IH.
    have ⟨ax, haxmem, hax⟩ := List.forall₂_implies_all_right hforall (a, tx') htx'mem
    simp only [AttrPredHasAttrType] at hax
    obtain ⟨_, c'', htypred⟩ := hax
    have hsz : sizeOf ax.snd < sizeOf axs := List.sizeOf_snd_lt_sizeOf_list haxmem
    exact type_of_pred_implies_wf_type (p := ax.snd) hwf hitwf htypred
  | .call f xs =>
    simp only [typeOfPred] at h
    cases h₁ : xs.mapM₁ (λ x => justType (typeOfPred x.1 itTy c env)) <;>
      simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i tys
    exact typeOfCall_wf h
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals (try (first | (have := hsz; omega) | omega))

end Cedar.Thm
