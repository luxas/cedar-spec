/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Typechecker.LitVar

/-!
# Predicate type soundness — foundation (D-74 option A, Phase 9c, §5.1/§5.2)

This file states the predicate analogue of `type_of_is_sound`
(`Thm/Validation/Typechecker.lean`) over `PredExpr`/`evaluatePred`/`typeOfPred`,
with the quantifier element keyword `it` (`PredExpr.item`) bound to a value `it`
that is an instance of its static element type `itTy`.

**WEAK soundness (D-94 / D-P9c-5 resolved option (c)).** The statement admits
*any* error on the error side and carries **no** capability invariant: a
well-typed predicate, evaluated with the element bound to a value of its static
type, either errors (with any error) or yields a value that is an instance of the
returned type. This is deliberately weaker than the expression `type_of_is_sound`
(which rules out `attrDoesNotExist`/`typeError` via a capability invariant): the
capability invariant cannot be threaded soundly through a predicate because
`itExpr := .var .principal` and `typeOfAll` passes the OUTER capabilities into
`typeOfPred`, so an `it`-dependent attribute capability would be keyed by
`principal` (D-95, an OPEN Lean-spec precision/parity follow-up). Weak soundness
is all every downstream D-74-A consumer needs — `normalize_evaluatePred` only
needs "a `.bool .ff`-typed sub-predicate evaluates to `false` or errors (never
`true`)", which the any-error form delivers via `instance_of_ff_is_false`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Predicate analogue of `EvaluatesTo`, WEAK form (D-94): evaluating `p` with the
element bound to `it` yields the value `v`, or **any** error. No restriction to
the three validation-time errors — a predicate may legitimately raise
`attrDoesNotExist` (hence `quantifierError` at the quantifier), which the
capability invariant would have ruled out for expressions but which we do not
track for predicates.
-/
def EvaluatesToPred (p : PredExpr) (it : Value) (request : Request) (entities : Entities) (v : Value) : Prop :=
  (∃ err, evaluatePred p it request entities = .error err) ∨
  evaluatePred p it request entities = .ok v

/--
Predicate analogue of `CapabilitiesInvariant` (D-97 option b). A capability
`(e, k) ∈ c` is interpreted against the `it`-bound predicate evaluation: the
capability-key `Expr` `e` is inverted to the predicate `ofCapKey e` and the
attribute/tag fact must hold of `evaluatePred (ofCapKey e) it` (D-P9c-7,
approach A). On the consumer side `typeOfHasAttr` consults `(x₁.toCapKey, .attr a)
∈ c`, and `ofCapKey x₁.toCapKey = x₁` for `x₁.NoReservedItAccess`
(`ofCapKey_toCapKey`), so the invariant yields the fact about `x₁` directly. On
the production side a new singleton key `x₁.toCapKey` carries exactly the fact
`evaluatePred x₁ it = true`, with no `∀ q` quantifier to discharge.
-/
def CapabilitiesInvariantPred (c : Capabilities) (it : Value) (request : Request) (entities : Entities) : Prop :=
  (∀ (e : Expr) (k : Attr), (e, .attr k) ∈ c →
    EvaluatesToPred (.hasAttr (PredExpr.ofCapKey e) k) it request entities true) ∧
  (∀ (e k : Expr), (e, .tag k) ∈ c →
    EvaluatesToPred (.binaryApp .hasTag (PredExpr.ofCapKey e) (PredExpr.ofCapKey k)) it request entities true)

/-- The context record type does not declare the reserved `it` capability-key
attribute `__cedar::anyall::it` (D-P9c-7). A predicate well-typed under this can
never contain the reserved access, so `toCapKey` is injective on it. -/
def NoReservedItKey (env : TypeEnv) : Prop :=
  ¬ env.reqty.context.contains "__cedar::anyall::it"

/-- The empty capability set trivially satisfies the predicate invariant. -/
theorem empty_capabilities_invariant_pred (it : Value) (request : Request) (entities : Entities) :
    CapabilitiesInvariantPred ∅ it request entities := by
  constructor <;> intro e k h <;> contradiction

/-- Union of two predicate-invariant capability sets is predicate-invariant (pred twin of `capability_union_invariant`). -/
theorem capability_union_invariant_pred {c₁ c₂ : Capabilities} {it : Value}
    {request : Request} {entities : Entities}
    (h₁ : CapabilitiesInvariantPred c₁ it request entities)
    (h₂ : CapabilitiesInvariantPred c₂ it request entities) :
    CapabilitiesInvariantPred (c₁ ∪ c₂) it request entities := by
  simp only [CapabilitiesInvariantPred, List.mem_union_iff] at *
  refine ⟨?_, ?_⟩
  · intro e k h₃
    rcases h₃ with h₃ | h₃
    · exact h₁.left e k h₃
    · exact h₂.left e k h₃
  · intro e k h₃
    rcases h₃ with h₃ | h₃
    · exact h₁.right e k h₃
    · exact h₂.right e k h₃

/--
Predicate analogue of `GuardedCapabilitiesInvariant`: the output capabilities
satisfy `CapabilitiesInvariantPred` provided the predicate evaluates to `true`.
-/
def GuardedCapabilitiesInvariantPred (p : PredExpr) (c : Capabilities) (it : Value)
    (request : Request) (entities : Entities) : Prop :=
  evaluatePred p it request entities = .ok true → CapabilitiesInvariantPred c it request entities

theorem empty_guarded_capabilities_invariant_pred {p : PredExpr} {it : Value}
    {request : Request} {entities : Entities} :
    GuardedCapabilitiesInvariantPred p ∅ it request entities := by
  intro _; exact empty_capabilities_invariant_pred it request entities

/-- `ofCapKey` inverts `toCapKey` on predicates without the reserved `it` access
(D-P9c-7, approach A). Structural induction on `q`; the only non-structural arm
is `.item`, whose `toCapKey` is `itCapKey`, inverted to `.item`. The `.getAttr`
arm uses `NoReservedItAccess` to rule out the colliding
`context["__cedar::anyall::it"]` shape. -/
theorem ofCapKey_toCapKey {q : PredExpr} (h : q.NoReservedItAccess = true) :
    PredExpr.ofCapKey q.toCapKey = q := by
  match q with
  | .item => simp only [PredExpr.toCapKey, itCapKey, PredExpr.ofCapKey, and_self, ↓reduceIte]
  | .lit _ => simp only [PredExpr.toCapKey, PredExpr.ofCapKey]
  | .var _ => simp only [PredExpr.toCapKey, PredExpr.ofCapKey]
  | .ite a b c =>
    simp only [PredExpr.NoReservedItAccess, Bool.and_eq_true] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey, ofCapKey_toCapKey h.1.1,
      ofCapKey_toCapKey h.1.2, ofCapKey_toCapKey h.2]
  | .and a b =>
    simp only [PredExpr.NoReservedItAccess, Bool.and_eq_true] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey, ofCapKey_toCapKey h.1, ofCapKey_toCapKey h.2]
  | .or a b =>
    simp only [PredExpr.NoReservedItAccess, Bool.and_eq_true] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey, ofCapKey_toCapKey h.1, ofCapKey_toCapKey h.2]
  | .unaryApp op a =>
    simp only [PredExpr.NoReservedItAccess] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey, ofCapKey_toCapKey h]
  | .binaryApp op a b =>
    simp only [PredExpr.NoReservedItAccess, Bool.and_eq_true] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey, ofCapKey_toCapKey h.1, ofCapKey_toCapKey h.2]
  | .getAttr a attr =>
    have hguard : ¬ (a.toCapKey = Expr.var Var.context ∧ attr = "__cedar::anyall::it") := by
      rintro ⟨ha, hattr⟩
      have havar : a = PredExpr.var Var.context := by
        cases a <;> simp only [PredExpr.toCapKey, itCapKey, Expr.var.injEq, reduceCtorEq] at ha ⊢
        rename_i v
        simp only [PredExpr.var.injEq]
        exact ha
      subst havar
      simp only [PredExpr.NoReservedItAccess, hattr, ne_eq, not_true, decide_false,
        Bool.false_eq_true] at h
    have hrec : a.NoReservedItAccess = true := by
      cases a with
      | var v => cases v <;> simp_all only [PredExpr.NoReservedItAccess]
      | _ => simp_all only [PredExpr.NoReservedItAccess]
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey, if_neg hguard, ofCapKey_toCapKey hrec]
  | .hasAttr a attr =>
    simp only [PredExpr.NoReservedItAccess] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey, ofCapKey_toCapKey h]
  | .extHasAttr a attr attrs =>
    simp only [PredExpr.NoReservedItAccess] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey, ofCapKey_toCapKey h]
  | .record axs =>
    simp only [PredExpr.NoReservedItAccess, List.all_attach₂_snd, List.all_eq_true] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey]
    congr 1
    rw [List.map₂_eq_map_snd, List.map₂_eq_map_snd, List.map_map]
    conv => rhs; rw [← List.map_id axs]
    apply List.map_congr_left
    intro x hx
    have := List.sizeOf_snd_lt_sizeOf_list hx
    obtain ⟨a, b⟩ := x
    simp only [Function.comp_apply, id_eq, Prod.mk.injEq, true_and]
    exact ofCapKey_toCapKey (h (a, b) hx)
  | .call f xs =>
    simp only [PredExpr.NoReservedItAccess, List.all_eq_true] at h
    simp only [PredExpr.toCapKey, PredExpr.ofCapKey]
    congr 1
    rw [List.map₁_eq_map, List.map₁_eq_map, List.map_map]
    conv => rhs; rw [← List.map_id xs]
    apply List.map_congr_left
    intro x hx
    have := List.sizeOf_lt_of_mem hx
    simp only [Function.comp_apply, id_eq]
    exact ofCapKey_toCapKey (h ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩))
termination_by sizeOf q
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals
    (first
      | (have := List.sizeOf_snd_lt_sizeOf_list hx; omega)
      | (have := List.sizeOf_lt_of_mem hx; omega)
      | omega)

/--
**Support lemma (a) (§5.1 step 1).** A predicate that type-checks under
`NoReservedItKey env` has `NoReservedItAccess`: it cannot contain the reserved
capability-key access `context["__cedar::anyall::it"]`, because typing
`context["__cedar::anyall::it"]` reads `env.reqty.context`, which `NoReservedItKey`
says does not declare that attribute, so `getAttrInRecord` returns
`attrNotFound` and the whole `typeOfPred` errors — contradicting the `.ok`
hypothesis. Structural recursion on `p` (`termination_by sizeOf p`), the same
shape as `ofCapKey_toCapKey`; every arm but `.getAttr (.var .context) …` just
recurses into its typed operands. -/
theorem type_of_pred_implies_no_reserved {p : PredExpr} {itTy : CedarType}
    {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (hnr : NoReservedItKey env)
    (h : typeOfPred p itTy c env = Except.ok (tx, c')) :
    p.NoReservedItAccess = true := by
  match p with
  | .item => simp only [PredExpr.NoReservedItAccess]
  | .lit _ => simp only [PredExpr.NoReservedItAccess]
  | .var _ => simp only [PredExpr.NoReservedItAccess]
  | .ite a b d =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred a itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfPred b itTy (c ∪ r₁.2) env <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    cases h₃ : typeOfPred d itTy c env <;> simp only [h₃, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₂ r₃
    simp only [PredExpr.NoReservedItAccess, Bool.and_eq_true]
    exact ⟨⟨type_of_pred_implies_no_reserved hnr h₁, type_of_pred_implies_no_reserved hnr h₂⟩,
      type_of_pred_implies_no_reserved hnr h₃⟩
  | .and a b =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred a itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfPred b itTy (c ∪ r₁.2) env <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    simp only [PredExpr.NoReservedItAccess, Bool.and_eq_true]
    exact ⟨type_of_pred_implies_no_reserved hnr h₁, type_of_pred_implies_no_reserved hnr h₂⟩
  | .or a b =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred a itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfPred b itTy c env <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    simp only [PredExpr.NoReservedItAccess, Bool.and_eq_true]
    exact ⟨type_of_pred_implies_no_reserved hnr h₁, type_of_pred_implies_no_reserved hnr h₂⟩
  | .unaryApp op a =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred a itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    simp only [PredExpr.NoReservedItAccess]
    exact type_of_pred_implies_no_reserved hnr h₁
  | .binaryApp op a b =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred a itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    cases h₂ : typeOfPred b itTy c env <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    simp only [PredExpr.NoReservedItAccess, Bool.and_eq_true]
    exact ⟨type_of_pred_implies_no_reserved hnr h₁, type_of_pred_implies_no_reserved hnr h₂⟩
  | .hasAttr a attr =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred a itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    simp only [PredExpr.NoReservedItAccess]
    exact type_of_pred_implies_no_reserved hnr h₁
  | .extHasAttr a attr attrs =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred a itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    simp only [PredExpr.NoReservedItAccess]
    exact type_of_pred_implies_no_reserved hnr h₁
  | .getAttr a attr =>
    simp only [typeOfPred] at h
    cases h₁ : typeOfPred a itTy c env <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i r₁
    -- First, the operand recurses.
    have hrec := type_of_pred_implies_no_reserved (p := a) hnr h₁
    -- `NoReservedItAccess (.getAttr a attr)` is `a.NoReservedItAccess` for every
    -- `a` except `.var .context`, where it is `attr ≠ reserved`. Rule out the
    -- reserved shape by showing typing it fails.
    cases a with
    | var v =>
      cases v with
      | context =>
        by_cases hattr : attr = "__cedar::anyall::it"
        · exfalso
          subst hattr
          have hvar : typeOfPred (.var Var.context) itTy c env = Except.ok (r₁.1, r₁.2) := h₁
          simp only [typeOfPred, typeOfVar, Validation.ok, Function.comp_apply,
            Except.ok.injEq, Prod.mk.injEq] at hvar
          obtain ⟨hv1, _⟩ := hvar
          simp only [typeOfGetAttr, ← hv1, TypedExpr.typeOf, getAttrInRecord] at h
          have hnone : env.reqty.context.find? "__cedar::anyall::it" = none := by
            have hc := hnr
            simp only [NoReservedItKey, Map.contains, Bool.not_eq_true] at hc
            exact Option.not_isSome_iff_eq_none.mp (by simp only [hc, Bool.false_eq_true, not_false_eq_true])
          simp only [hnone, Validation.err, Except.bind_err, reduceCtorEq] at h
        · simp only [PredExpr.NoReservedItAccess, PredExpr.var, ne_eq, hattr, not_false_eq_true,
            decide_true]
      | principal => simpa only [PredExpr.NoReservedItAccess, PredExpr.var] using hrec
      | action => simpa only [PredExpr.NoReservedItAccess, PredExpr.var] using hrec
      | resource => simpa only [PredExpr.NoReservedItAccess, PredExpr.var] using hrec
    | item => simpa only [PredExpr.NoReservedItAccess] using hrec
    | lit _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | ite _ _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | and _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | or _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | unaryApp _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | binaryApp _ _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | getAttr _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | hasAttr _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | extHasAttr _ _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | record _ => simpa only [PredExpr.NoReservedItAccess] using hrec
    | call _ _ => simpa only [PredExpr.NoReservedItAccess] using hrec
  | .record axs =>
    simp only [typeOfPred] at h
    cases h₁ : axs.mapM₂ (λ x => (typeOfPred x.1.snd itTy c env).map (λ (ty, _) => (x.1.fst, ty)))
      <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i rtx
    simp only [PredExpr.NoReservedItAccess, List.all_attach₂_snd, List.all_eq_true]
    intro x hx
    -- each element typed under the same env/caps; recurse via the mapM₂ success
    simp only [List.mapM₂_eq_mapM
      (λ (x : Attr × PredExpr) => Except.map (fun x₁ : (TypedExpr × Capabilities) => (x.fst, x₁.fst)) (typeOfPred x.snd itTy c env))] at h₁
    have hmem := List.mapM_ok_implies_all_ok h₁ x hx
    obtain ⟨b, _, hb⟩ := hmem
    cases hty : typeOfPred x.snd itTy c env <;> simp only [hty, Except.map, reduceCtorEq] at hb
    have := List.sizeOf_snd_lt_sizeOf_list hx
    exact type_of_pred_implies_no_reserved hnr hty
  | .call f xs =>
    simp only [typeOfPred] at h
    cases h₁ : xs.mapM₁ (λ x => justType (typeOfPred x.1 itTy c env))
      <;> simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at h
    rename_i tys
    simp only [PredExpr.NoReservedItAccess, List.all_eq_true]
    intro x hx
    have hxmem : x.val ∈ xs := x.property
    simp only [List.mapM₁_eq_mapM (λ (x : PredExpr) => justType (typeOfPred x itTy c env))] at h₁
    have hmem := List.mapM_ok_implies_all_ok h₁ x.val hxmem
    obtain ⟨b, _, hb⟩ := hmem
    cases hty : typeOfPred x.val itTy c env <;> simp only [hty, justType, Except.map, reduceCtorEq] at hb
    have := List.sizeOf_lt_of_mem hxmem
    exact type_of_pred_implies_no_reserved hnr hty
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  all_goals
    (first
      | (have := List.sizeOf_snd_lt_sizeOf_list hx; omega)
      | (have := List.sizeOf_lt_of_mem hx; omega)
      | omega)

/--
Predicate analogue of `TypeOfIsSound` (D-97 option b). The true mirror: it takes
`CapabilitiesInvariantPred c₁ it …` and `env.NoReservedItKey`, and concludes the
guarded production of `CapabilitiesInvariantPred c₂` AND that evaluation yields a
value of the returned type or (D-94) **any** error.
-/
def TypeOfPredIsSound (p : PredExpr) : Prop :=
  ∀ {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities} {env : TypeEnv}
    {ty : TypedExpr} {request : Request} {entities : Entities},
    NoReservedItKey env →
    itTy.WellFormed env →
    CapabilitiesInvariantPred c₁ it request entities →
    InstanceOfWellFormedEnvironment request entities env →
    InstanceOfType env it itTy →
    typeOfPred p itTy c₁ env = Except.ok (ty, c₂) →
    GuardedCapabilitiesInvariantPred p c₂ it request entities ∧
    ∃ v, EvaluatesToPred p it request entities v ∧ InstanceOfType env v ty.typeOf

/-- An error on the left of `EvaluatesToPred` for any witness `v`. -/
theorem EvaluatesToPred.error {p : PredExpr} {it : Value} {request : Request} {entities : Entities}
    {err : Error} {v : Value}
    (h : evaluatePred p it request entities = .error err) :
    EvaluatesToPred p it request entities v :=
  Or.inl ⟨err, h⟩

/-! ### Trivial arms: `.item`, `.lit`, `.var`. -/

/--
`.item`: `typeOfPred .item itTy = ok (.var .principal itTy)` and
`evaluatePred .item it = .ok it`. The result type is `itTy`, closed directly by
the `InstanceOfType env it itTy` hypothesis.
-/
theorem type_of_pred_item_is_sound {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (hit : InstanceOfType env it itTy)
    (h₃ : typeOfPred .item itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariantPred .item c₂ it request entities ∧
    ∃ v, EvaluatesToPred .item it request entities v ∧ InstanceOfType env v ty.typeOf := by
  simp only [typeOfPred, Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h₃
  obtain ⟨hty, hc⟩ := h₃
  subst hc; subst hty
  refine ⟨empty_guarded_capabilities_invariant_pred, it, ?_, ?_⟩
  · exact Or.inr (by simp only [evaluatePred])
  · show InstanceOfType env it (TypedExpr.var Var.principal itTy).typeOf
    simp only [TypedExpr.typeOf]
    exact hit

/-- `.lit`: value typing coincides with the expression `.lit` soundness. -/
theorem type_of_pred_lit_is_sound {l : Prim} {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₃ : typeOfPred (.lit l) itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariantPred (.lit l) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.lit l) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have hc : c₂ = ∅ := by
    simp only [typeOfPred, typeOfLit] at h₃
    split at h₃ <;> (try split at h₃) <;> simp_all [Validation.ok, Validation.err]
  subst hc
  have hexpr : typeOf (Expr.lit l) c₁ env = Except.ok (ty, ∅) := by
    simpa only [typeOf, typeOfPred] using h₃
  have ⟨_, v, hev, hinst⟩ := type_of_lit_is_sound (request := request) (entities := entities) hexpr
  refine ⟨empty_guarded_capabilities_invariant_pred, v, ?_, hinst⟩
  simp only [EvaluatesTo, evaluate] at hev
  simp only [EvaluatesToPred, evaluatePred]
  rcases hev with hev | hev | hev | hev | hev
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact absurd hev (by simp)
  · exact Or.inr hev

/-- `.var`: value typing coincides with the expression `.var` soundness. -/
theorem type_of_pred_var_is_sound {vr : Var} {itTy : CedarType} {it : Value} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (h₃ : typeOfPred (.var vr) itTy c₁ env = Except.ok (ty, c₂)) :
    GuardedCapabilitiesInvariantPred (.var vr) c₂ it request entities ∧
    ∃ v, EvaluatesToPred (.var vr) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have hc : c₂ = ∅ := by
    simp only [typeOfPred, typeOfVar] at h₃
    cases vr <;> simp_all [Validation.ok]
  subst hc
  have hexpr : typeOf (Expr.var vr) c₁ env = Except.ok (ty, ∅) := by
    simpa only [typeOf, typeOfPred] using h₃
  have ⟨_, v, hev, hinst⟩ := type_of_var_is_sound h₂ hexpr
  refine ⟨empty_guarded_capabilities_invariant_pred, v, ?_, hinst⟩
  have heval : evaluatePred (.var vr) it request entities = evaluate (.var vr) request entities := by
    cases vr <;> simp only [evaluatePred, evaluate]
  simp only [EvaluatesToPred, heval]
  simp only [EvaluatesTo] at hev
  rcases hev with hev | hev | hev | hev | hev
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inl ⟨_, hev⟩
  · exact Or.inr hev

end Cedar.Thm
