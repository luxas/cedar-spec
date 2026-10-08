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

end UnitTest.AnyAll
