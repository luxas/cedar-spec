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

module

public import Cedar.SymCC.Compiler
import all Cedar.SymCC.Compiler
import all Cedar.SymCC.Factory
import all Cedar.Thm.SymCC.Term.Interpret.SubstAnyAllIt
import all Cedar.Thm.SymCC.Compiler.SetAllWF

/-! Per-helper `NoSetAll` / `anyAllItTyped` preservation lemmas for the `compilePred`
compile helpers, assembled from the Factory-fn facts in `SetAllWF.lean`. These feed
`compilePred_noSetAll` / `compilePred_anyAllItTyped`. -/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

/-! ### ifFalse (used by compileApp₁ neg and the compileCall/ext error wrappers) -/

theorem noSetAll_ifFalse {g t : Term} (hg : g.NoSetAll = true) (ht : t.NoSetAll = true) :
    (Factory.ifFalse g t).NoSetAll = true := by
  unfold Factory.ifFalse; exact noSetAll_ite hg noSetAll_noneOf (noSetAll_someOf ht)
theorem anyAllItTyped_ifFalse {ety : TermType} {g t : Term}
    (hg : g.anyAllItTyped ety = true) (ht : t.anyAllItTyped ety = true) :
    (Factory.ifFalse g t).anyAllItTyped ety = true := by
  unfold Factory.ifFalse; exact anyAllItTyped_ite hg anyAllItTyped_noneOf (anyAllItTyped_someOf ht)

/-! ### compileApp₁ -/

theorem noSetAll_compileApp₁ {op₁ : UnaryOp} {t r : Term} (h : t.NoSetAll = true)
    (hok : compileApp₁ op₁ t = Except.ok r) : r.NoSetAll = true := by
  unfold compileApp₁ at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok <;> subst hok
  · exact noSetAll_someOf (noSetAll_not h)
  · exact noSetAll_ifFalse (noSetAll_bvnego h) (noSetAll_bvneg h)
  · exact noSetAll_someOf (noSetAll_string_like h)
  · exact noSetAll_someOf (by simp [Term.NoSetAll])
  · exact noSetAll_someOf (noSetAll_set_isEmpty h)
theorem anyAllItTyped_compileApp₁ {ety : TermType} {op₁ : UnaryOp} {t r : Term}
    (h : t.anyAllItTyped ety = true) (hok : compileApp₁ op₁ t = Except.ok r) :
    r.anyAllItTyped ety = true := by
  unfold compileApp₁ at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok <;> subst hok
  · exact anyAllItTyped_someOf (anyAllItTyped_not h)
  · exact anyAllItTyped_ifFalse (anyAllItTyped_bvnego h) (anyAllItTyped_bvneg h)
  · exact anyAllItTyped_someOf (anyAllItTyped_string_like h)
  · exact anyAllItTyped_someOf (by simp [Term.anyAllItTyped])
  · exact anyAllItTyped_someOf (anyAllItTyped_set_isEmpty h)

end Cedar.Thm
