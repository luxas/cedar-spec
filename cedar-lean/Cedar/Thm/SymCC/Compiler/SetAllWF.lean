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

/-! ### eq -/

theorem noSetAll_eq_simplify {a b : Term} (h1 : a.NoSetAll = true) (h2 : b.NoSetAll = true) :
    (Factory.eq.simplify a b).NoSetAll = true := by
  unfold Factory.eq.simplify; repeat' split
  all_goals first | exact h1 | exact h2 | exact noSetAll_not h2 | exact noSetAll_not h1 | (simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2]) | simp only [Term.NoSetAll]
theorem noSetAll_eq {t₁ t₂ : Term} (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) :
    (Factory.eq t₁ t₂).NoSetAll = true := by
  unfold Factory.eq; split
  · exact noSetAll_eq_simplify (by simp_all [Term.NoSetAll]) (by simp_all [Term.NoSetAll])
  · simp only [Term.NoSetAll]
  · simp only [Term.NoSetAll]
  · exact noSetAll_eq_simplify h1 h2

theorem anyAllItTyped_eq_simplify {ety : TermType} {a b : Term}
    (h1 : a.anyAllItTyped ety = true) (h2 : b.anyAllItTyped ety = true) :
    (Factory.eq.simplify a b).anyAllItTyped ety = true := by
  unfold Factory.eq.simplify; repeat' split
  all_goals first | exact h1 | exact h2 | exact anyAllItTyped_not h2 | exact anyAllItTyped_not h1 | (simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, h2]) | simp only [Term.anyAllItTyped]
theorem anyAllItTyped_eq {ety : TermType} {t₁ t₂ : Term}
    (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) :
    (Factory.eq t₁ t₂).anyAllItTyped ety = true := by
  unfold Factory.eq; split
  · exact anyAllItTyped_eq_simplify (by simp_all [Term.anyAllItTyped]) (by simp_all [Term.anyAllItTyped])
  · simp only [Term.anyAllItTyped]
  · simp only [Term.anyAllItTyped]
  · exact anyAllItTyped_eq_simplify h1 h2

/-! ### ite -/

theorem noSetAll_ite_simplify {t₁ a b : Term}
    (h1 : t₁.NoSetAll = true) (ha : a.NoSetAll = true) (hb : b.NoSetAll = true) :
    (Factory.ite.simplify t₁ a b).NoSetAll = true := by
  unfold Factory.ite.simplify; repeat' split
  all_goals first | exact ha | exact hb | exact h1 | exact noSetAll_not h1 | exact noSetAll_and h1 ha | exact noSetAll_or h1 hb | (simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, ha, hb]) | simp only [Term.NoSetAll]
theorem noSetAll_ite {t₁ t₂ t₃ : Term}
    (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) (h3 : t₃.NoSetAll = true) :
    (Factory.ite t₁ t₂ t₃).NoSetAll = true := by
  unfold Factory.ite; split
  · simp only [Term.NoSetAll]
    exact noSetAll_ite_simplify h1 (by simp_all [Term.NoSetAll]) (by simp_all [Term.NoSetAll])
  · exact noSetAll_ite_simplify h1 h2 h3

theorem anyAllItTyped_ite_simplify {ety : TermType} {t₁ a b : Term}
    (h1 : t₁.anyAllItTyped ety = true) (ha : a.anyAllItTyped ety = true) (hb : b.anyAllItTyped ety = true) :
    (Factory.ite.simplify t₁ a b).anyAllItTyped ety = true := by
  unfold Factory.ite.simplify; repeat' split
  all_goals first | exact ha | exact hb | exact h1 | exact anyAllItTyped_not h1 | exact anyAllItTyped_and h1 ha | exact anyAllItTyped_or h1 hb | (simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all]; simp [h1, ha, hb]) | simp only [Term.anyAllItTyped]
theorem anyAllItTyped_ite {ety : TermType} {t₁ t₂ t₃ : Term}
    (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) (h3 : t₃.anyAllItTyped ety = true) :
    (Factory.ite t₁ t₂ t₃).anyAllItTyped ety = true := by
  unfold Factory.ite; split
  · simp only [Term.anyAllItTyped]
    exact anyAllItTyped_ite_simplify h1 (by simp_all [Term.anyAllItTyped]) (by simp_all [Term.anyAllItTyped])
  · exact anyAllItTyped_ite_simplify h1 h2 h3

/-! ### isNone / isSome / ifSome -/

theorem noSetAll_isNone {t : Term} (h : t.NoSetAll = true) : (Factory.isNone t).NoSetAll = true := by
  unfold Factory.isNone; repeat' split
  all_goals (try exact h) <;> (try exact noSetAll_eq h noSetAll_noneOf) <;>
    (try (apply noSetAll_not; simp_all [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all])) <;>
    (try (simp only [Term.NoSetAll, List.map, List.attach, List.attachWith, List.pmap, List.all] at *; simp_all)) <;>
    (try simp only [Term.NoSetAll])
theorem anyAllItTyped_isNone {ety : TermType} {t : Term} (h : t.anyAllItTyped ety = true) :
    (Factory.isNone t).anyAllItTyped ety = true := by
  unfold Factory.isNone; repeat' split
  all_goals (try exact h) <;> (try exact anyAllItTyped_eq h anyAllItTyped_noneOf) <;>
    (try (apply anyAllItTyped_not; simp_all [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all])) <;>
    (try (simp only [Term.anyAllItTyped, List.map, List.attach, List.attachWith, List.pmap, List.all] at *; simp_all)) <;>
    (try simp only [Term.anyAllItTyped])

theorem noSetAll_isSome {t : Term} (h : t.NoSetAll = true) : (Factory.isSome t).NoSetAll = true := by
  unfold Factory.isSome; exact noSetAll_not (noSetAll_isNone h)
theorem anyAllItTyped_isSome {ety : TermType} {t : Term} (h : t.anyAllItTyped ety = true) :
    (Factory.isSome t).anyAllItTyped ety = true := by
  unfold Factory.isSome; exact anyAllItTyped_not (anyAllItTyped_isNone h)

theorem noSetAll_ifSome {g t : Term} (hg : g.NoSetAll = true) (ht : t.NoSetAll = true) :
    (Factory.ifSome g t).NoSetAll = true := by
  unfold Factory.ifSome Factory.ifFalse; split
  · exact noSetAll_ite (noSetAll_isNone hg) noSetAll_noneOf ht
  · exact noSetAll_ite (noSetAll_isNone hg) noSetAll_noneOf (noSetAll_someOf ht)
theorem anyAllItTyped_ifSome {ety : TermType} {g t : Term}
    (hg : g.anyAllItTyped ety = true) (ht : t.anyAllItTyped ety = true) :
    (Factory.ifSome g t).anyAllItTyped ety = true := by
  unfold Factory.ifSome Factory.ifFalse; split
  · exact anyAllItTyped_ite (anyAllItTyped_isNone hg) anyAllItTyped_noneOf ht
  · exact anyAllItTyped_ite (anyAllItTyped_isNone hg) anyAllItTyped_noneOf (anyAllItTyped_someOf ht)

end Cedar.Thm
