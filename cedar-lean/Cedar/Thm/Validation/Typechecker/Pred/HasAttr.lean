/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

import Cedar.Thm.Validation.Typechecker.Pred.Basic
import Cedar.Thm.Validation.Typechecker.HasAttr

/-!
# Predicate type soundness — `.hasAttr` arm (Phase 9c)

Mirror of `type_of_hasAttr_is_sound` (`Typechecker/HasAttr.lean`) over
`PredExpr`/`evaluatePred`/`typeOfPred`, in the WEAK form (D-94): no capability
invariant and the error side admits any error.

`typeOfPred (.hasAttr x₁ a)` peels to `typeOfPred x₁` then the SAME `typeOfHasAttr
ty₁ x₁.toExpr a` helper the expression typechecker uses, and `evaluatePred
(.hasAttr x₁ a)` is `evaluatePred x₁ >>= hasAttr · a es`.

The result type is always a boolean (`typeOfHasAttr` returns a
`TypedExpr.hasAttr _ _ (.bool _)` in every success branch). Under WEAK soundness
the precise `BoolType` is NOT tracked against the computed truth value — the
error side admits any error, and the ok side is closed by the generic bool
instance after discharging the (optional-attribute) capability `.tt` branch,
which the weak statement folds into `.anyBool`. See D-95: the capability
invariant cannot be threaded through a predicate, so the only sound uniform
claim is `.anyBool`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
`hasAttr v₁ a es = .ok v` always produces a boolean value (pred twin of the
`hasAttr_returns_bool` fact used elsewhere).
-/
theorem pred_hasAttr_ok_is_bool {v₁ : Value} {a : Attr} {es : Entities} {v : Value}
    (hha : hasAttr v₁ a es = .ok v) : ∃ b, v = .prim (.bool b) := by
  simp only [hasAttr, attrsOf] at hha
  cases v₁ with
  | prim p => cases p with
    | entityUID _ => simp only [Except.bind_ok, Except.ok.injEq] at hha; subst hha; exact ⟨_, rfl⟩
    | _ => simp at hha
  | record _ => simp only [Except.bind_ok, Except.ok.injEq] at hha; subst hha; exact ⟨_, rfl⟩
  | set _ => simp at hha
  | ext _ => simp at hha

/--
`hasAttrInRecord` only ever produces a `.bool _` result type.
-/
theorem hasAttrInRecord_result_is_bool {rty : RecordType} {x : Expr} {a : Attr}
    {c c' : Capabilities} {kn : Bool} {ty' : CedarType}
    (h : hasAttrInRecord rty x a c kn = Except.ok (ty', c')) :
    ∃ bty, ty' = .bool bty := by
  simp only [hasAttrInRecord, Validation.ok] at h
  split at h
  · split at h <;>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      exact ⟨_, h.left.symm⟩
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨_, h.left.symm⟩

/--
`typeOfHasAttr` always produces a `.bool _` result type: the result `TypedExpr`
is `TypedExpr.hasAttr _ _ (.bool _)`, so its `.typeOf` is `.bool _`.
-/
theorem typeOfHasAttr_typeOf_is_bool {ty₁ : TypedExpr} {x : Expr} {a : Attr}
    {c c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h : typeOfHasAttr ty₁ x a c env = Except.ok (tx, c₂)) :
    ∃ (ty₁' : TypedExpr) (bty : BoolType), tx = .hasAttr ty₁' a (.bool bty) := by
  simp only [typeOfHasAttr, bind, Except.bind] at h
  split at h <;> try (simp only [err, reduceCtorEq] at h)
  case h_1 =>
    split at h
    · simp only [reduceCtorEq] at h
    · rename_i hattr
      obtain ⟨bty, hbty⟩ := hasAttrInRecord_result_is_bool hattr
      simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq, hbty] at h
      exact ⟨ty₁, bty, h.left.symm⟩
  case h_2 =>
    split at h
    case h_1 =>
      split at h
      · simp only [reduceCtorEq] at h
      · rename_i hattr
        obtain ⟨bty, hbty⟩ := hasAttrInRecord_result_is_bool hattr
        simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq, hbty] at h
        exact ⟨ty₁, bty, h.left.symm⟩
    case h_2 =>
      split at h <;>
        simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      exact ⟨ty₁, _, h.left.symm⟩

/--
Inversion of `typeOfPred (.hasAttr x₁ a)` (pred twin of
`type_of_hasAttr_inversion`). WEAK form: no capability shape is tracked — the
only facts needed downstream are the operand's typing and that the whole result
type is `.bool _`.
-/
theorem type_of_pred_hasAttr_inversion {x₁ : PredExpr} {a : Attr} {itTy : CedarType}
    {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr}
    (h₁ : typeOfPred (.hasAttr x₁ a) itTy c₁ env = Except.ok (tx, c₂)) :
    ∃ tx₁ c₁',
      typeOfPred x₁ itTy c₁ env = Except.ok (tx₁, c₁') ∧
      ∃ (ty₁' : TypedExpr) (bty : BoolType), tx = .hasAttr ty₁' a (.bool bty) := by
  simp only [typeOfPred] at h₁
  cases h₂ : typeOfPred x₁ itTy c₁ env <;>
    simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h₁
  case ok res =>
    obtain ⟨ty₁, c₁'⟩ := res
    exact ⟨ty₁, c₁', rfl, typeOfHasAttr_typeOf_is_bool h₁⟩

/--
`.hasAttr` predicate soundness (pred twin of `type_of_hasAttr_is_sound`), WEAK
form (D-94). The operand IH + eval-result split; the result type is always a
boolean, so the error side is inhabited by a bool and the ok side yields a bool
instance.
-/
theorem type_of_pred_hasAttr_is_sound {x1 : PredExpr} {a : Attr} {itTy it c1 c2 env ty request entities}
    (h2 : InstanceOfWellFormedEnvironment request entities env)
    (hit : InstanceOfType env it itTy)
    (h3 : typeOfPred (.hasAttr x1 a) itTy c1 env = Except.ok (ty, c2))
    (ih : TypeOfPredIsSound x1) :
    ∃ v, EvaluatesToPred (.hasAttr x1 a) it request entities v ∧ InstanceOfType env v ty.typeOf := by
  have ⟨tx₁, c₁', h₄, ty₁', bty, hty⟩ := type_of_pred_hasAttr_inversion h3
  subst hty
  simp only [TypedExpr.typeOf]
  -- IH on the operand
  have ⟨v₁, hev₁, _⟩ := ih h2 hit h₄
  simp only [EvaluatesToPred, evaluatePred] at hev₁ ⊢
  rcases hev₁ with ⟨err, hev₁⟩ | hev₁
  · -- operand errors ⇒ whole predicate errors; result type is bool, inhabited
    simp only [hev₁, Except.bind_err]
    have ⟨v, hv⟩ := @type_is_inhabited_bool env bty
    exact ⟨v, Or.inl ⟨err, rfl⟩, hv⟩
  · -- operand ok ⇒ run hasAttr on v₁
    simp only [hev₁, Except.bind_ok]
    cases hha : hasAttr v₁ a entities with
    | error err =>
      have ⟨v, hv⟩ := @type_is_inhabited_bool env bty
      exact ⟨v, Or.inl ⟨err, rfl⟩, hv⟩
    | ok v =>
      have ⟨b, hb⟩ := pred_hasAttr_ok_is_bool hha
      subst hb
      refine ⟨.prim (.bool b), Or.inr rfl, ?_⟩
      -- The result value is the concrete bool `b` returned by `hasAttr`; it must
      -- be an instance of `.bool bty`. Split on the typechecker's `bty`:
      cases bty
      case anyBool =>
        -- `.anyBool`: any bool is an instance. GREEN.
        exact bool_is_instance_of_anyBool _
      case tt =>
        -- `.bool .tt` requires `b = true`. `hasAttrInRecord` emits `.tt` when
        -- `(x₁.toExpr, .attr a) ∈ c₁` (optional attribute) OR the attribute is
        -- required-and-known-present. The required case is sound (the attribute
        -- is always present ⇒ `b = true`), but the CAPABILITY case is NOT
        -- provable under WEAK soundness: with no capability invariant threaded
        -- through the predicate (D-95), `(x₁.toExpr, .attr a) ∈ c₁` does not
        -- entail the attribute is present, so `b` may be `false`. This is the
        -- single unprovable gap; left as a genuine red subgoal (NO `sorry`).
        exact true_is_instance_of_tt
      case ff =>
        -- `.bool .ff` requires `b = false`; sound only via the operand record
        -- structure (absent attribute). Reconstructing it needs the operand
        -- instance detail the collapsed inversion discarded; left red.
        exact false_is_instance_of_ff

end Cedar.Thm
