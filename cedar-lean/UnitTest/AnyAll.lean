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

import Cedar.Spec.Evaluator
import Cedar.Data.Map
import Cedar.Validation.EnvironmentValidator
import UnitTest.Run

/-! Unit tests for the `.all` / `.any` set quantifier (anyall feature). -/

namespace UnitTest.AnyAll

open Cedar.Spec
open Cedar.Data

/-- `Result Value` as a `Sum`, which has `DecidableEq` and `Repr`. -/
private def asSum (r : Result Value) : Sum Error Value :=
  match r with
  | .ok v    => .inr v
  | .error e => .inl e

private def eval (x : Expr) : Sum Error Value :=
  asSum (evaluate x default Map.empty)

private def int (i : Int) : Expr := .lit (.int (Int64.ofInt i))
private def str (s : String) : Expr := .lit (.string s)
private def bool (b : Bool) : Sum Error Value := .inr (.prim (.bool b))

/-- `0 < it` (errors on non-integer elements) -/
private def itPos : PredExpr := .binaryApp .less (.lit (.int 0)) .item
/-- `1 < it` -/
private def itGt1 : PredExpr := .binaryApp .less (.lit (.int 1)) .item
/-- `it == 2` -/
private def itEq2 : PredExpr := .binaryApp .eq .item (.lit (.int 2))

/-- `e.any(p)` is lowered to `!e.all(!p)` before reaching the Lean spec. -/
private def any (e : Expr) (p : PredExpr) : Expr :=
  .unaryApp .not (.all e (.unaryApp .not p))

private def t (name : String) (x : Expr) (expected : Sum Error Value) : TestCase IO :=
  test name ⟨λ _ => checkEq (eval x) expected⟩

private def rec (dept : String) : Expr := .record [("dept", str dept)]

private def deptIsEng : PredExpr :=
  .binaryApp .eq (.getAttr .item "dept") (.lit (.string "eng"))

def testsForAll :=
  suite "anyall: .all evaluation"
  [
    -- req 2.1
    t "all true" (.all (.set [int 1, int 2, int 3]) itPos) (bool true),
    -- req 2.2
    t "all false" (.all (.set [int 1, int 2, int 3]) itGt1) (bool false),
    -- req 2.7
    t "empty set is true" (.all (.set []) itGt1) (bool true),
    -- req 2.4: a non-set receiver is a type error, not a quantifier error
    t "non-set receiver" (.all (int 1) itPos) (.inl .typeError),
    -- receiver errors propagate unchanged
    t "receiver error propagates" (.all (.getAttr (int 1) "x") itPos) (.inl .typeError),
    -- req 2.5: an erroring element yields quantifierError
    t "erroring element" (.all (.set [int 1, str "a"]) itPos) (.inl .quantifierError),
    -- req 2.8: an earlier false element must not short-circuit past a later
    -- error (ints order before strings, so 0 is visited before "a")
    t "false then error is quantifierError" (.all (.set [int 0, str "a"]) itPos) (.inl .quantifierError),
    -- req 2.5: same elements, reversed insertion order, same result
    t "error then false (reversed) is quantifierError" (.all (.set [str "a", int 0]) itPos) (.inl .quantifierError),
    -- a non-boolean predicate result counts as an erroring element
    t "non-bool predicate" (.all (.set [int 1]) .item) (.inl .quantifierError),
    -- elements bind full values, e.g. records
    t "records, all match" (.all (.set [rec "eng"]) deptIsEng) (bool true),
    t "records, one differs" (.all (.set [rec "eng", rec "ops"]) deptIsEng) (bool false),
    t "records, missing attr errors" (.all (.set [.record [("team", str "eng")]]) deptIsEng)
      (.inl .quantifierError),
    -- predicates can mix `it` with request variables
    t "predicate uses principal" (.all (.set [int 1])
      (.binaryApp .eq (.var .principal) (.var .principal))) (bool true)
  ]

def testsForAny :=
  suite "anyall: .any (lowered to !all(!p))"
  [
    -- req 2.3
    t "any true" (any (.set [int 1, int 2, int 3]) itEq2) (bool true),
    t "any false" (any (.set [int 1, int 3]) itEq2) (bool false),
    -- req 2.7
    t "empty set is false" (any (.set []) itEq2) (bool false),
    -- req 2.8 for any: an earlier true element must not hide a later error
    t "true then error is quantifierError" (any (.set [int 1, str "a"]) itPos) (.inl .quantifierError)
  ]

def tests := [ testsForAll, testsForAny ]

/-! ### D-98 regression: the environment validator rejects a context that declares
the reserved quantifier capability-key attribute `__cedar::anyall::it`. -/

section D98
open Cedar.Validation

private def reservedCtx : RecordType :=
  Map.mk [("__cedar::anyall::it", Qualified.required (.bool .anyBool))]

private def userTy : EntityType := ⟨"User", []⟩
private def resTy  : EntityType := ⟨"Res", []⟩
private def actUid : EntityUID := ⟨⟨"Action", []⟩, "act"⟩

private def reservedEnv : TypeEnv where
  ets := Map.mk []
  acts := Map.mk [(actUid, {
    appliesToPrincipal := Set.mk [userTy]
    appliesToResource := Set.mk [resTy]
    ancestors := Set.mk []
    context := reservedCtx })]
  reqty := {
    principal := userTy
    action := actUid
    resource := resTy
    context := reservedCtx }

private def isErr (r : EnvironmentValidationResult) : Bool :=
  match r with | .error _ => true | .ok _ => false

-- The reserved-attr context is REJECTED by the request-type validator (D-98):
-- the action/principal/resource/context-shape checks all pass, so the error is
-- exactly the reserved-attribute rejection.
#guard isErr (reservedEnv.reqty.validateWellFormed reservedEnv)

end D98

/-! ### D-99 regression (Phase 9c): capability boundary of the `.all` predicate.

`typeOfAll` types the predicate under `it : τ` with the OUTER capabilities filtered to the
clean (`it`-free) keys. So a `has` on `principal` in the enclosing `&&` DOES reach the predicate
(its capability key is clean), but no attribute is accessible on `it` unless the predicate itself
guards it. With `a` OPTIONAL on the element entity type `E`:

  * `principal has "a" && context.s.all(it.a == 1)` must be REJECTED — the outer `has` is about
    `principal`, not `it`, so `it.a` reads an optional attr with no capability.
  * `principal has "a" && context.s.all(principal.a == it)` must be ACCEPTED — the outer `has`
    establishes the clean `principal` capability, which survives into the predicate. -/
section D99
open Cedar.Validation

private def elemTy : EntityType := ⟨"E", []⟩
private def princTy : EntityType := ⟨"User", []⟩
private def resTy99  : EntityType := ⟨"Res", []⟩
private def actUid99 : EntityUID := ⟨⟨"Action", []⟩, "act"⟩

-- `a` is OPTIONAL on both entity types: `int` on the element `E` (so `it.a == 1` type-checks when
-- a capability exists), and `E` on the principal (so `principal.a == it` compares `E == E`).
private def optAInt : RecordType := Map.mk [("a", Qualified.optional (.int))]
private def optAElem : RecordType := Map.mk [("a", Qualified.optional (.entity elemTy))]
-- context has `s : Set<E>`.
private def ctx99 : RecordType := Map.mk [("s", Qualified.required (.set (.entity elemTy)))]

private def env99 : TypeEnv where
  ets := Map.mk [
    (elemTy, .standard { ancestors := Set.empty, attrs := optAInt, tags := none }),
    (princTy, .standard { ancestors := Set.empty, attrs := optAElem, tags := none }),
    (resTy99, .standard { ancestors := Set.empty, attrs := Map.empty, tags := none })]
  acts := Map.mk [(actUid99, {
    appliesToPrincipal := Set.mk [princTy]
    appliesToResource := Set.mk [resTy99]
    ancestors := Set.mk []
    context := ctx99 })]
  reqty := {
    principal := princTy
    action := actUid99
    resource := resTy99
    context := ctx99 }

-- `context.s` : Set<E>
private def ctxS : Expr := .getAttr (.var .context) "s"
-- predicate `it.a == 1` (reads optional attr on `it` with no capability)
private def predItA : PredExpr := .binaryApp .eq (.getAttr .item "a") (.lit (.int (Int64.ofInt 1)))
-- predicate `principal.a == it` (uses the clean principal capability from the outer `has`)
private def predPrincA : PredExpr := .binaryApp .eq (.getAttr (.var .principal) "a") .item

private def hasPrincA : Expr := .hasAttr (.var .principal) "a"

private def isOkT (r : ResultType) : Bool := match r with | .ok _ => true | .error _ => false
private def isErrT (r : ResultType) : Bool := match r with | .ok _ => false | .error _ => true

-- REJECTED: `it.a` on an optional attr with no capability inside the predicate.
#guard isErrT (typeOf (.and hasPrincA (.all ctxS predItA)) [] env99)
-- ACCEPTED: `principal.a` is capability-covered by the outer `principal has "a"` (clean key, D-99).
#guard isOkT (typeOf (.and hasPrincA (.all ctxS predPrincA)) [] env99)

end D99

end UnitTest.AnyAll
