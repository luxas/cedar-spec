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

import Cedar.SymCC

/-! Compile-time regression guards for the `set.all` concrete fold under
`Term.interpret` (D-55/D-60), guarding against the D-61 bound-variable
substitution bug (`some vi` coercing to `Option.some (Term.some vi)` inside a
`Term` namespace, which double-wrapped the substituted element). A literal
receiver must fold element-by-element to a literal result, matching `evalAll`. -/

namespace SymTest.AnyAll

open Cedar.SymCC Cedar.Data Cedar.Spec

private def ety : TermType := .bitvec 64
private def it : Term := .var (Factory.anyAllItVar ety)

-- Non-erroring predicate value `pt : .option .bool` = `some (0 <ₛ it)`.
private def pt : Term := Factory.someOf (Factory.bvslt (0 : BitVec 64) it)
private def predT : Term := Factory.option.get pt
private def errT : Term := Factory.not (Factory.isSome pt)

private def lit (n : BitVec 64) : Term := (n : Term)
private def mkset (ns : List (BitVec 64)) : Term := .set (Set.mk (ns.map lit)) ety
private def allT (ns : List (BitVec 64)) : Term := .app Op.set.all [mkset ns, predT, errT] (.option .bool)

-- Erroring predicate: `none` exactly when the element equals 7.
private def ptErr : Term :=
  Factory.ite (Factory.eq it (lit 7)) (Factory.noneOf .bool)
    (Factory.someOf (Factory.bvslt (0 : BitVec 64) it))
private def predE : Term := Factory.option.get ptErr
private def errE : Term := Factory.not (Factory.isSome ptErr)
private def allErr (ns : List (BitVec 64)) : Term := .app Op.set.all [mkset ns, predE, errE] (.option .bool)

-- A well-formed-shaped interpretation; this predicate uses no symbolic vars/uufs.
private def I0 : Interpretation :=
  { vars := fun v => .var v,
    funs := fun _ => { arg := .bool, out := .bool, table := Map.mk [], default := Term.prim (.bool false) },
    partials := fun t => t }

-- all elements satisfy the predicate ⇒ `some true`.
#guard (allT [1, 2]).interpret I0 == Term.some (Term.prim (.bool true))
-- an element fails (0 is not > 0) ⇒ `some false`.
#guard (allT [0, 1]).interpret I0 == Term.some (Term.prim (.bool false))
-- empty receiver ⇒ `some true`.
#guard (allT []).interpret I0 == Term.some (Term.prim (.bool true))
-- an element errors (7) ⇒ `none` (quantifierError).
#guard (allErr [1, 7]).interpret I0 == Term.none (.bool)

end SymTest.AnyAll
