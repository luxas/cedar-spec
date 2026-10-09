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
import SymTest.Util

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

-- A predicate mentioning a FREE variable `n` is interpreted under the model: the
-- fold interprets the free var before comparing, so the result depends on `I n`.
private def nvar : Term := .var { id := "n", ty := ety }
private def ptN : Term := Factory.someOf (Factory.bvslt nvar it)  -- it > n
private def predN : Term := Factory.option.get ptN
private def errN : Term := Factory.not (Factory.isSome ptN)
private def allN : Term := .app Op.set.all [mkset [1, 2], predN, errN] (.option .bool)
private def In (nval : BitVec 64) : Interpretation :=
  { vars := fun v => if v.id = "n" then (lit nval) else .var v,
    funs := fun _ => { arg := .bool, out := .bool, table := Map.mk [], default := Term.prim (.bool false) },
    partials := fun t => t }
-- `[1,2].all(it > n)` with n = 0 ⇒ `some true`; with n = 1 ⇒ `some false` (1 is not > 1).
#guard allN.interpret (In 0) == Term.some (Term.prim (.bool true))
#guard allN.interpret (In 1) == Term.some (Term.prim (.bool false))

end SymTest.AnyAll

/-! End-to-end symbolic `.all` tests through the encoder + cvc5. -/

namespace SymTest.AnyAll.E2E

open Cedar Data Spec SymCC Validation
open UnitTest

-- Context with a set-of-int attr `xs`, a set-of-record attr `rs` (record with int `k`),
-- and a set-of-entity attr `es`.
private def recTy : RecordType := Map.make [("k", .required .int)]
private def E : EntityType := ⟨"Principal", []⟩

private def ctx : RecordType :=
  Map.make [
    ("xs", .required (.set .int)),
    ("rs", .required (.set (.record recTy))),
    ("es", .required (.set (.entity E))),
    ("n",  .required .int)
  ]

private def Γ := BasicTypes.env (Map.make [("k", .optional .int)]) Map.empty ctx

private def xs : Expr := .getAttr (.var .context) "xs"
private def rs : Expr := .getAttr (.var .context) "rs"
private def es : Expr := .getAttr (.var .context) "es"
private def nAttr : Expr := .getAttr (.var .context) "n"

-- predicate `it > 0`
private def pGt0 : PredExpr := .binaryApp .less (.lit (.int 0)) .item
-- predicate `it >= 0`
private def pGe0 : PredExpr := .or (.binaryApp .less (.lit (.int 0)) .item) (.binaryApp .eq .item (.lit (.int 0)))
-- predicate `it.k > 0`  (record-attr)
private def pRecK : PredExpr := .binaryApp .less (.lit (.int 0)) (.getAttr .item "k")
-- predicate `it has k`   (entity/record-attr existence; always typed Bool)
private def pHasK : PredExpr := .hasAttr .item "k"
-- predicate `principal in it`  (entity, it on the RIGHT — the sound/footprint-free side)
private def pPrinIn : PredExpr := .binaryApp .mem (.var .principal) .item
-- predicate `it in principal`  (entity, it on the LEFT — it-dependent `in`, D-70 guard REJECTS)
private def pItIn : PredExpr := .binaryApp .mem .item (.var .principal)
-- predicate `it > n`  (free context variable n)
private def pGtN : PredExpr := .binaryApp .less (.getAttr (.var .context) "n") .item
-- erroring predicate `it.k > 0` (getAttr on an entity may error if `k` absent) and its guarded form
private def pRecKErr : PredExpr := .binaryApp .less (.lit (.int 0)) (.getAttr .item "k")
private def pRecKGuard : PredExpr := .and (.hasAttr .item "k") (.binaryApp .less (.lit (.int 0)) (.getAttr .item "k"))

private def permit (x : Expr) : Policy :=
  { id := "policy", effect := .permit, principalScope := .principalScope .any,
    actionScope := .actionScope .any, resourceScope := .resourceScope .any, condition := [⟨.when, x⟩] }

private def mkEquiv (desc : String) (x₁ x₂ : Expr) (o : Outcome) : TestCase SolverM :=
  test desc ⟨λ _ => o.check (verifyEquivalent [permit x₁] [permit x₂]) (SymEnv.ofTypeEnv Γ)⟩

private def mkImplies (desc : String) (x₁ x₂ : Expr) (o : Outcome) : TestCase SolverM :=
  test desc ⟨λ _ => o.check (verifyImplies [permit x₁] [permit x₂]) (SymEnv.ofTypeEnv Γ)⟩

-- NOTE: unoptimized SymCC path only; the optimized SymCCOpt compiler still rejects `.all`
-- (`Cedar/SymCCOpt/Compiler.lean:412`), which is M4 scope (blocked on the D-70 footprint decision).
def tests : List (TestSuite SolverM) :=
  [ { name := "AnyAll.e2e", tests :=
      [ mkEquiv "all(it>0) ≢ true" (.all xs pGt0) (.lit (.bool true)) .sat,
        mkImplies "all(it>0) ⇒ all(it>=0)" (.all xs pGt0) (.all xs pGe0) .unsat,
        mkEquiv "all(it.k>0) ≢ true" (.all rs pRecK) (.lit (.bool true)) .sat,
        mkEquiv "all(principal in it) ≢ true" (.all es pPrinIn) (.lit (.bool true)) .sat,
        mkEquiv "all(it has k) ≢ true" (.all es pHasK) (.lit (.bool true)) .sat,
        mkEquiv "all(it>n) ≢ true" (.all xs pGtN) (.lit (.bool true)) .sat,
        mkEquiv "all(it>0) ≡ all(it>0)" (.all xs pGt0) (.all xs pGt0) .unsat,
        -- erroring vs guarded predicate: distinguishes the encoder's quantifierError filter.
        -- With the filter, `all(it.k>0)` errors when some element lacks `k` while the guarded
        -- form short-circuits ⇒ NOT equivalent (sat). Dropping the filter collapses them (would flip to unsat).
        mkEquiv "all(it.k>0) ≡ all(it has k && it.k>0) [entity attrs total]" (.all es pRecKErr) (.all es pRecKGuard) .unsat,
        -- D-70 guard: an `it`-dependent LEFT operand of `in` is rejected (unsupportedError);
        -- the it-free-left form (`principal in it`, pPrinIn above) is accepted and verified sat.
        testFailsCompilePolicy "all(it in principal) rejected (D-70 guard)" (.all es pItIn) Γ ] } ]

end SymTest.AnyAll.E2E
