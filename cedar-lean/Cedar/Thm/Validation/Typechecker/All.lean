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

import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.Types

/-!
Foundation lemmas for the soundness of the `.all` set-quantifier type rule
(Phase 5A, `anyall-set-operators`).

The decisive fact is `evalAll_bool_or_qerr`: `evalAll` *always* produces either
`ok (bool _)` or the single `quantifierError`, for **any** per-element function
`f`. This is what lets `.all` soundness avoid threading the predicate's own
soundness through the quantifier — the `.as Bool` masking inside `evalAll`
collapses every non-boolean / erroring element into `quantifierError`
regardless of how the predicate is typed (D-44, the key simplifier).

The `*_ne_qerr` lemmas record that no primitive evaluator operation produces
`quantifierError`; `quantifierError` is introduced solely by `evalAll`. They are
kept here for use by the quantifier soundness proof and by anyone reasoning
about error provenance across the predicate evaluator.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
**L4.** `evalAll` always yields `ok (bool _)` or `error quantifierError`, for any
per-element function. The `.as Bool` coercion inside `evalAll` turns every
non-boolean or erroring element into the single, order-independent
`quantifierError`; a successful run folds the booleans with conjunction.

Crucially this holds for an *arbitrary* `f`, so the soundness of `.all` does not
depend on the predicate being well-typed — the type rule's bool/set checks give
Rust-parity rejection, not quantifier-result soundness.
-/
theorem evalAll_bool_or_qerr (s : Set Value) (f : Value → Result Value) :
    (∃ b : Bool, evalAll s f = .ok (.prim (.bool b))) ∨
    evalAll s f = .error .quantifierError := by
  simp only [evalAll]
  split
  · right; rfl
  · left; rename_i bs _; exact ⟨bs.all id, rfl⟩

/-- `evalAll` always yields a value that is an instance of `.bool .anyBool`, or
the `quantifierError`. A direct corollary of `evalAll_bool_or_qerr`. -/
theorem evalAll_instance_or_qerr {env : TypeEnv} (s : Set Value) (f : Value → Result Value) :
    (∃ v, evalAll s f = .ok v ∧ InstanceOfType env v (.bool .anyBool)) ∨
    evalAll s f = .error .quantifierError := by
  rcases evalAll_bool_or_qerr s f with ⟨b, h⟩ | h
  · exact Or.inl ⟨_, h, bool_is_instance_of_anyBool b⟩
  · exact Or.inr h

/-! ### No primitive evaluator operation produces `quantifierError`.

`quantifierError` is introduced only by `evalAll`. These lemmas certify that for
each primitive the predicate evaluator can call. -/

theorem intOrErr_ne_qerr (o : Option Int64) : intOrErr o ≠ .error .quantifierError := by
  cases o <;> simp [intOrErr]

theorem apply₁_ne_qerr (op : UnaryOp) (v : Value) : apply₁ op v ≠ .error .quantifierError := by
  simp only [apply₁]
  split <;> (try apply intOrErr_ne_qerr) <;> simp

theorem inₛ_ne_qerr (uid : EntityUID) (vs : Set Value) (es : Entities) :
    inₛ uid vs es ≠ .error .quantifierError := by
  simp only [inₛ, Set.mapOrErr]
  split <;> simp [Except.bind_ok, Except.bind_err]

theorem hasTag_ne_qerr (uid : EntityUID) (t : String) (es : Entities) :
    hasTag uid t es ≠ .error .quantifierError := by
  simp [hasTag]

theorem entities_tags_ne_qerr (es : Entities) (uid : EntityUID) :
    es.tags uid ≠ .error .quantifierError := by
  simp only [Entities.tags, Map.findOrErr]
  cases es.find? uid <;> simp

theorem entities_attrs_ne_qerr (es : Entities) (uid : EntityUID) :
    es.attrs uid ≠ .error .quantifierError := by
  simp only [Entities.attrs, Map.findOrErr]
  cases es.find? uid <;> simp

theorem getTag_ne_qerr (uid : EntityUID) (t : String) (es : Entities) :
    getTag uid t es ≠ .error .quantifierError := by
  simp only [getTag]
  cases h : es.tags uid <;> simp [Except.bind_ok, Except.bind_err, Map.findOrErr]
  · rename_i e
    have := entities_tags_ne_qerr es uid
    rw [h] at this
    simpa using this
  · split <;> simp

theorem apply₂_ne_qerr (op : BinaryOp) (v₁ v₂ : Value) (es : Entities) :
    apply₂ op v₁ v₂ es ≠ .error .quantifierError := by
  simp only [apply₂]
  split <;>
    (try apply intOrErr_ne_qerr) <;>
    (try apply inₛ_ne_qerr) <;>
    (try apply hasTag_ne_qerr) <;>
    (try apply getTag_ne_qerr) <;>
    simp

theorem bind_ne_qerr {α} (m : Result α) (f : α → Result Value)
    (hm : m ≠ .error .quantifierError) (hf : ∀ x, f x ≠ .error .quantifierError) :
    (m >>= f) ≠ .error .quantifierError := by
  cases m <;> simp_all

theorem findOrErr_ne_qerr {β} (m : Map Attr β) (a : Attr) (e : Error)
    (he : e ≠ .quantifierError) : m.findOrErr a e ≠ .error .quantifierError := by
  simp only [Map.findOrErr]; split <;> simp_all

theorem attrsOf_ne_qerr {v : Value} {lookup : EntityUID → Result (Map Attr Value)}
    (hl : ∀ uid, lookup uid ≠ .error .quantifierError) :
    attrsOf v lookup ≠ .error .quantifierError := by
  simp only [attrsOf]; split <;> simp_all

theorem hasAttr_ne_qerr (v : Value) (a : Attr) (es : Entities) :
    hasAttr v a es ≠ .error .quantifierError := by
  simp only [hasAttr]
  apply bind_ne_qerr
  · exact attrsOf_ne_qerr (fun _ => by simp)
  · intro _; simp

theorem getAttr_ne_qerr (v : Value) (a : Attr) (es : Entities) :
    getAttr v a es ≠ .error .quantifierError := by
  simp only [getAttr]
  apply bind_ne_qerr
  · exact attrsOf_ne_qerr (entities_attrs_ne_qerr es)
  · intro r; exact findOrErr_ne_qerr r a _ (by simp)

theorem hasAttrs_ne_qerr (v : Value) (a : Attr) (as0 : List Attr) (es : Entities) :
    hasAttrs v a as0 es ≠ .error .quantifierError := by
  simp only [hasAttrs]
  generalize (a :: as0) = attrsList
  induction attrsList generalizing v with
  | nil => simp [hasAttrs.loop]
  | cons hd tl ih =>
    simp only [hasAttrs.loop]
    split <;> try simp
    split <;> simp_all

/-! ### Soundness of the `.all` type rule. -/

/--
Inversion of `typeOf (.all x₁ p)`: a successful type assignment means the
receiver `x₁` typechecks to some `tyr` of set type `.set τ`, the predicate
typechecks under `it : τ`, the result type is `.bool .anyBool`, and the output
capabilities equal the input `c₁` (predicate capabilities are dropped, D-39).
-/
theorem type_of_all_inversion {x₁ : Expr} {p : PredExpr} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr}
    (h : typeOf (.all x₁ p) c₁ env = .ok (ty, c₂)) :
    c₂ = c₁ ∧ ty.typeOf = .bool .anyBool ∧
    ∃ tyr cr τ, typeOf x₁ c₁ env = .ok (tyr, cr) ∧ tyr.typeOf = .set τ ∧
      ty = .all tyr p (.bool .anyBool) := by
  simp only [typeOf] at h
  cases hr : typeOf x₁ c₁ env <;> rw [hr] at h <;>
    simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at h
  rename_i tyr
  simp only [typeOfAll] at h
  split at h <;> rename_i hset
  · cases hpred : typeOfPred p _ c₁ env <;> rw [hpred] at h <;>
      simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at h
    split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    rcases h with ⟨h₁, h₂⟩
    subst h₁; subst h₂
    refine ⟨rfl, by simp only [TypedExpr.typeOf], tyr.fst, tyr.snd, _, ?_, hset, rfl⟩
    simpa using hr
  · simp only [err, reduceCtorEq] at h

/--
**Soundness of `.all`** (`type_of_<op>_is_sound` shape). A well-typed `.all`
evaluates to a boolean of type `.bool .anyBool` or to an allowed error (including
`quantifierError`), and its output capabilities (`= c₁`) satisfy the guarded
invariant. The quantifier result is sound regardless of the predicate's typing,
because `evalAll` always yields `ok (bool _)` or `quantifierError`
(`evalAll_bool_or_qerr`); the receiver's set type is inverted by
`instance_of_set_type_is_set`.
-/
theorem type_of_all_is_sound {x₁ : Expr} {p : PredExpr} {c₁ c₂ : Capabilities}
    {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
    (h₁ : CapabilitiesInvariant c₁ request entities)
    (h₂ : InstanceOfWellFormedEnvironment request entities env)
    (h₃ : typeOf (.all x₁ p) c₁ env = .ok (ty, c₂))
    (ih₁ : TypeOfIsSound x₁) :
    GuardedCapabilitiesInvariant (.all x₁ p) c₂ request entities ∧
    ∃ v, EvaluatesTo (.all x₁ p) request entities v ∧ InstanceOfType env v ty.typeOf := by
  have ⟨hc, hty, tyr, cr, τ, hrecv, hrecvty, _⟩ := type_of_all_inversion h₃
  subst hc
  rw [hty]
  refine ⟨fun _ => h₁, ?_⟩
  have ⟨_, vr, hev, hvty⟩ := ih₁ h₁ h₂ hrecv
  rw [hrecvty] at hvty
  simp only [EvaluatesTo] at hev
  simp only [EvaluatesTo, evaluate]
  rcases hev with hev | hev | hev | hev | hev
  · exact ⟨_, Or.inl (by simp [hev, Result.as]), bool_is_instance_of_anyBool true⟩
  · exact ⟨_, Or.inr (Or.inl (by simp [hev, Result.as])), bool_is_instance_of_anyBool true⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl (by simp [hev, Result.as]))), bool_is_instance_of_anyBool true⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl (by simp [hev, Result.as])))), bool_is_instance_of_anyBool true⟩
  · have ⟨s, hs, _⟩ := instance_of_set_type_is_set hvty
    subst hs
    rcases evalAll_bool_or_qerr s (fun v => evaluatePred p v request entities) with ⟨b, hb⟩ | hq
    · refine ⟨_, Or.inr (Or.inr (Or.inr (Or.inr ?_))), bool_is_instance_of_anyBool b⟩
      simp only [hev, Result.as, Coe.coe, Value.asSet, Except.bind_ok, hb]
    · refine ⟨_, Or.inr (Or.inr (Or.inr (Or.inl ?_))), bool_is_instance_of_anyBool true⟩
      simp only [hev, Result.as, Coe.coe, Value.asSet, Except.bind_ok, hq]

end Cedar.Thm
