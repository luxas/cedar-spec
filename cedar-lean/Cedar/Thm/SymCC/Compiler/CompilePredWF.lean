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
import Cedar.Thm.Tactics

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

/-! ### compileIf / compileAnd / compileOr -/

theorem noSetAll_compileIf {t₁ r : Term} {R₂ R₃ : Except SymCC.Error Term} (h1 : t₁.NoSetAll = true)
    (h2 : ∀ t₂, R₂ = .ok t₂ → t₂.NoSetAll = true) (h3 : ∀ t₃, R₃ = .ok t₃ → t₃.NoSetAll = true)
    (hok : compileIf t₁ R₂ R₃ = Except.ok r) : r.NoSetAll = true := by
  rw [compileIf.eq_def] at hok
  split at hok
  · exact h2 r hok
  · exact h3 r hok
  · cases he2 : R₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    cases he3 : R₃ <;> simp only [he3, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂ t₃
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    exact noSetAll_ifSome h1 (noSetAll_ite (noSetAll_option_get h1) (h2 t₂ he2) (h3 t₃ he3))
  · simp only [reduceCtorEq] at hok
theorem anyAllItTyped_compileIf {ety : TermType} {t₁ r : Term} {R₂ R₃ : Except SymCC.Error Term}
    (h1 : t₁.anyAllItTyped ety = true)
    (h2 : ∀ t₂, R₂ = .ok t₂ → t₂.anyAllItTyped ety = true)
    (h3 : ∀ t₃, R₃ = .ok t₃ → t₃.anyAllItTyped ety = true)
    (hok : compileIf t₁ R₂ R₃ = Except.ok r) : r.anyAllItTyped ety = true := by
  rw [compileIf.eq_def] at hok
  split at hok
  · exact h2 r hok
  · exact h3 r hok
  · cases he2 : R₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    cases he3 : R₃ <;> simp only [he3, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂ t₃
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    exact anyAllItTyped_ifSome h1 (anyAllItTyped_ite (anyAllItTyped_option_get h1) (h2 t₂ he2) (h3 t₃ he3))
  · simp only [reduceCtorEq] at hok

theorem noSetAll_compileAnd {t₁ r : Term} {R₂ : Except SymCC.Error Term} (h1 : t₁.NoSetAll = true)
    (h2 : ∀ t₂, R₂ = .ok t₂ → t₂.NoSetAll = true) (hok : compileAnd t₁ R₂ = Except.ok r) : r.NoSetAll = true := by
  rw [compileAnd.eq_def] at hok
  split at hok
  · simp only [Except.ok.injEq] at hok; subst hok; exact h1
  · cases he2 : R₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    exact noSetAll_ifSome h1 (noSetAll_ite (noSetAll_option_get h1) (h2 t₂ he2) (noSetAll_someOf (by simp [Term.NoSetAll])))
  · simp only [reduceCtorEq] at hok
theorem anyAllItTyped_compileAnd {ety : TermType} {t₁ r : Term} {R₂ : Except SymCC.Error Term}
    (h1 : t₁.anyAllItTyped ety = true) (h2 : ∀ t₂, R₂ = .ok t₂ → t₂.anyAllItTyped ety = true)
    (hok : compileAnd t₁ R₂ = Except.ok r) : r.anyAllItTyped ety = true := by
  rw [compileAnd.eq_def] at hok
  split at hok
  · simp only [Except.ok.injEq] at hok; subst hok; exact h1
  · cases he2 : R₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    exact anyAllItTyped_ifSome h1 (anyAllItTyped_ite (anyAllItTyped_option_get h1) (h2 t₂ he2) (anyAllItTyped_someOf (by simp [Term.anyAllItTyped])))
  · simp only [reduceCtorEq] at hok

theorem noSetAll_compileOr {t₁ r : Term} {R₂ : Except SymCC.Error Term} (h1 : t₁.NoSetAll = true)
    (h2 : ∀ t₂, R₂ = .ok t₂ → t₂.NoSetAll = true) (hok : compileOr t₁ R₂ = Except.ok r) : r.NoSetAll = true := by
  rw [compileOr.eq_def] at hok
  split at hok
  · simp only [Except.ok.injEq] at hok; subst hok; exact h1
  · cases he2 : R₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    exact noSetAll_ifSome h1 (noSetAll_ite (noSetAll_option_get h1) (noSetAll_someOf (by simp [Term.NoSetAll])) (h2 t₂ he2))
  · simp only [reduceCtorEq] at hok
theorem anyAllItTyped_compileOr {ety : TermType} {t₁ r : Term} {R₂ : Except SymCC.Error Term}
    (h1 : t₁.anyAllItTyped ety = true) (h2 : ∀ t₂, R₂ = .ok t₂ → t₂.anyAllItTyped ety = true)
    (hok : compileOr t₁ R₂ = Except.ok r) : r.anyAllItTyped ety = true := by
  rw [compileOr.eq_def] at hok
  split at hok
  · simp only [Except.ok.injEq] at hok; subst hok; exact h1
  · cases he2 : R₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    exact anyAllItTyped_ifSome h1 (anyAllItTyped_ite (anyAllItTyped_option_get h1) (anyAllItTyped_someOf (by simp [Term.anyAllItTyped])) (h2 t₂ he2))
  · simp only [reduceCtorEq] at hok

/-! ### anyNone / ifAllSome / compileRecord -/

theorem noSetAll_foldl_or {f : Term → Term} {ts : List Term} {acc : Term}
    (hf : ∀ t ∈ ts, (f t).NoSetAll = true) (hacc : acc.NoSetAll = true) :
    (ts.foldl (λ acc t => Factory.or (f t) acc) acc).NoSetAll = true := by
  induction ts generalizing acc with
  | nil => simpa using hacc
  | cons a rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun t ht => hf t (List.mem_cons_of_mem a ht))
    exact noSetAll_or (hf a (List.mem_cons_self ..)) hacc
theorem anyAllItTyped_foldl_or {ety : TermType} {f : Term → Term} {ts : List Term} {acc : Term}
    (hf : ∀ t ∈ ts, (f t).anyAllItTyped ety = true) (hacc : acc.anyAllItTyped ety = true) :
    (ts.foldl (λ acc t => Factory.or (f t) acc) acc).anyAllItTyped ety = true := by
  induction ts generalizing acc with
  | nil => simpa using hacc
  | cons a rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun t ht => hf t (List.mem_cons_of_mem a ht))
    exact anyAllItTyped_or (hf a (List.mem_cons_self ..)) hacc

theorem noSetAll_anyNone {gs : List Term} (hf : ∀ g ∈ gs, g.NoSetAll = true) : (Factory.anyNone gs).NoSetAll = true := by
  unfold Factory.anyNone Factory.anyTrue
  exact noSetAll_foldl_or (fun g hg => noSetAll_isNone (hf g hg)) (by simp [Term.NoSetAll])
theorem anyAllItTyped_anyNone {ety : TermType} {gs : List Term} (hf : ∀ g ∈ gs, g.anyAllItTyped ety = true) : (Factory.anyNone gs).anyAllItTyped ety = true := by
  unfold Factory.anyNone Factory.anyTrue
  exact anyAllItTyped_foldl_or (fun g hg => anyAllItTyped_isNone (hf g hg)) (by simp [Term.anyAllItTyped])

theorem noSetAll_ifAllSome {gs : List Term} {t : Term} (hg : ∀ g ∈ gs, g.NoSetAll = true) (ht : t.NoSetAll = true) : (Factory.ifAllSome gs t).NoSetAll = true := by
  unfold Factory.ifAllSome; split
  · exact noSetAll_ite (noSetAll_anyNone hg) noSetAll_noneOf ht
  · exact noSetAll_ifFalse (noSetAll_anyNone hg) ht
theorem anyAllItTyped_ifAllSome {ety : TermType} {gs : List Term} {t : Term} (hg : ∀ g ∈ gs, g.anyAllItTyped ety = true) (ht : t.anyAllItTyped ety = true) : (Factory.ifAllSome gs t).anyAllItTyped ety = true := by
  unfold Factory.ifAllSome; split
  · exact anyAllItTyped_ite (anyAllItTyped_anyNone hg) anyAllItTyped_noneOf ht
  · exact anyAllItTyped_ifFalse (anyAllItTyped_anyNone hg) ht

theorem noSetAll_compileRecord {ats : List (Attr × Term)} (h : ∀ p ∈ ats, p.2.NoSetAll = true) :
    (compileRecord ats).NoSetAll = true := by
  unfold compileRecord
  apply noSetAll_ifAllSome
  · intro g hg; simp only [List.mem_map] at hg; obtain ⟨p, hp, rfl⟩ := hg; exact h p hp
  · apply noSetAll_someOf; apply noSetAll_recordOf
    intro p hp; simp only [List.mem_map, Prod.map] at hp; obtain ⟨q, hq, rfl⟩ := hp
    exact noSetAll_option_get (h q hq)
theorem anyAllItTyped_compileRecord {ety : TermType} {ats : List (Attr × Term)}
    (h : ∀ p ∈ ats, p.2.anyAllItTyped ety = true) : (compileRecord ats).anyAllItTyped ety = true := by
  unfold compileRecord
  apply anyAllItTyped_ifAllSome
  · intro g hg; simp only [List.mem_map] at hg; obtain ⟨p, hp, rfl⟩ := hg; exact h p hp
  · apply anyAllItTyped_someOf; apply anyAllItTyped_recordOf
    intro p hp; simp only [List.mem_map, Prod.map] at hp; obtain ⟨q, hq, rfl⟩ := hp
    exact anyAllItTyped_option_get (h q hq)

end Cedar.Thm
