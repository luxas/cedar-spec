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

import Cedar.Data.SizeOf
public import Cedar.SymCC.Env
public import Cedar.SymCC.Interpretation
public import Cedar.SymCC.Term
import Cedar.Thm.SymCC.Data
import all Cedar.SymCC.Factory
import all Cedar.Thm.SymCC.Term.Interpret.SubstAnyAllIt

/-! `NoSetAll` / `anyAllItTyped` preservation for the Factory smart constructors
used by `compilePred`, built on `.app`-constructor helpers. -/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

/-! ### `.app` constructor helpers (non-`set.all` ops) -/

theorem noSetAll_app1 {op : Op} {t : Term} {ty : TermType} (hop : op ≠ Op.set.all)
    (h : t.NoSetAll = true) : (Term.app op [t] ty).NoSetAll = true := by
  cases op <;> (try exact absurd rfl hop) <;>
    (simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h])
theorem noSetAll_app2 {op : Op} {t₁ t₂ : Term} {ty : TermType} (hop : op ≠ Op.set.all)
    (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (Term.app op [t₁, t₂] ty).NoSetAll = true := by
  cases op <;> (try exact absurd rfl hop) <;>
    (simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2])
theorem noSetAll_app3 {op : Op} {t₁ t₂ t₃ : Term} {ty : TermType} (hop : op ≠ Op.set.all)
    (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) (h3 : t₃.NoSetAll = true) :
    (Term.app op [t₁, t₂, t₃] ty).NoSetAll = true := by
  cases op <;> (try exact absurd rfl hop) <;>
    (simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2, h3])

theorem anyAllItTyped_app1 {ety : TermType} {op : Op} {t : Term} {ty : TermType}
    (h : t.anyAllItTyped ety = true) : (Term.app op [t] ty).anyAllItTyped ety = true := by
  simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h]
theorem anyAllItTyped_app2 {ety : TermType} {op : Op} {t₁ t₂ : Term} {ty : TermType}
    (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) :
    (Term.app op [t₁, t₂] ty).anyAllItTyped ety = true := by
  simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2]
theorem anyAllItTyped_app3 {ety : TermType} {op : Op} {t₁ t₂ t₃ : Term} {ty : TermType}
    (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) (h3 : t₃.anyAllItTyped ety = true) :
    (Term.app op [t₁, t₂, t₃] ty).anyAllItTyped ety = true := by
  simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2, h3]

/-! ### leaf constructors -/

theorem noSetAll_someOf {t : Term} (h : t.NoSetAll = true) : (Factory.someOf t).NoSetAll = true := by
  simp only [Factory.someOf, Term.NoSetAll]; exact h
theorem anyAllItTyped_someOf {ety : TermType} {t : Term} (h : t.anyAllItTyped ety = true) :
    (Factory.someOf t).anyAllItTyped ety = true := by simp only [Factory.someOf, Term.anyAllItTyped]; exact h
theorem noSetAll_noneOf {ty : TermType} : (Factory.noneOf ty).NoSetAll = true := by
  simp only [Factory.noneOf, Term.NoSetAll]
theorem anyAllItTyped_noneOf {ety ty : TermType} : (Factory.noneOf ty).anyAllItTyped ety = true := by
  simp only [Factory.noneOf, Term.anyAllItTyped]

theorem noSetAll_not {t : Term} (h : t.NoSetAll = true) : (Factory.not t).NoSetAll = true := by
  unfold Factory.not
  split
  · simp only [Term.NoSetAll]
  · rename_i t' _
    simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all,
      Bool.and_eq_true, and_true] at h; exact h
  · exact noSetAll_app1 (op := Op.not) (by intro h; cases h) h
theorem anyAllItTyped_not {ety : TermType} {t : Term} (h : t.anyAllItTyped ety = true) :
    (Factory.not t).anyAllItTyped ety = true := by
  unfold Factory.not
  split
  · simp only [Term.anyAllItTyped]
  · rename_i t' _
    simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all,
      Bool.and_eq_true, and_true] at h; exact h
  · exact anyAllItTyped_app1 (op := Op.not) h

theorem noSetAll_and {t₁ t₂ : Term} (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) :
    (Factory.and t₁ t₂).NoSetAll = true := by
  unfold Factory.and; repeat' split
  all_goals (try exact h1) <;> (try exact h2) <;>
    (try (simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2])) <;>
    (try simp only [Term.NoSetAll])
theorem anyAllItTyped_and {ety : TermType} {t₁ t₂ : Term}
    (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) :
    (Factory.and t₁ t₂).anyAllItTyped ety = true := by
  unfold Factory.and; repeat' split
  all_goals (try exact h1) <;> (try exact h2) <;>
    (try (simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2])) <;>
    (try simp only [Term.anyAllItTyped])

theorem noSetAll_or {t₁ t₂ : Term} (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) :
    (Factory.or t₁ t₂).NoSetAll = true := by
  unfold Factory.or; repeat' split
  all_goals (try exact h1) <;> (try exact h2) <;>
    (try (simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2])) <;>
    (try simp only [Term.NoSetAll])
theorem anyAllItTyped_or {ety : TermType} {t₁ t₂ : Term}
    (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) :
    (Factory.or t₁ t₂).anyAllItTyped ety = true := by
  unfold Factory.or; repeat' split
  all_goals (try exact h1) <;> (try exact h2) <;>
    (try (simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2])) <;>
    (try simp only [Term.anyAllItTyped])

end Cedar.Thm
