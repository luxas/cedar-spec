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
import all Cedar.SymCC.ExtFun
import all Cedar.SymCC.Factory
import all Cedar.Thm.SymCC.Term.Interpret.SubstAnyAllIt
import all Cedar.Thm.SymCC.Compiler.SetAllWF
import Cedar.Thm.SymCC.Data.Basic
import all Cedar.Thm.Data.Map
import all Cedar.Thm.SymCC.Compiler.Invert
import all Cedar.Thm.SymCC.Compiler.ExtHasAttrRec
import Cedar.Thm.SymCC.Env.WF
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

/-! ### compilePrim / compileVar (base cases) -/

theorem compilePrim_pres {p : Prim} {r : Term} {εs : SymEntities} (hok : compilePrim p εs = Except.ok r) :
    r.NoSetAll = true ∧ ∀ ety, r.anyAllItTyped ety = true := by
  unfold compilePrim at hok
  split at hok <;> try split at hok
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at hok
  all_goals subst hok
  all_goals exact ⟨noSetAll_someOf (by simp [Term.NoSetAll]), fun ety => anyAllItTyped_someOf (by simp [Term.anyAllItTyped])⟩

theorem compileVar_pres {v : Var} {r : Term} {req : SymRequest} {εs : SymEntities}
    (hwf : req.WellFormed εs) (hok : compileVar v req = Except.ok r) :
    r.NoSetAll = true ∧ ∀ ety, r.anyAllItTyped ety = true := by
  have ⟨_,_,hpn,hps,_,_,han,has,_,_,hrn,hrs,_,_,hcn,hcs⟩ := hwf
  unfold compileVar at hok
  split at hok <;> split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok <;> subst hok
  all_goals refine ⟨noSetAll_someOf ?_, fun ety => anyAllItTyped_someOf ?_⟩
  all_goals first
    | exact hps | exact has | exact hrs | exact hcs
    | exact noAnyAllItVar_anyAllItTyped _ hpn | exact noAnyAllItVar_anyAllItTyped _ han
    | exact noAnyAllItVar_anyAllItTyped _ hrn | exact noAnyAllItVar_anyAllItTyped _ hcn

/-! ### Factory.app on a well-formed UnaryFunction (uuf or udf; udf tables are literal) -/

theorem noSetAll_udf_fold {t : Term} {tbl : List (Term × Term)} {dflt : Term}
    (ht : t.NoSetAll = true) (hd : dflt.NoSetAll = true)
    (htbl : ∀ p ∈ tbl, p.1.NoSetAll = true ∧ p.2.NoSetAll = true) :
    (tbl.foldr (λ (p : Term × Term) t₃ => Factory.ite (Factory.eq t p.1) p.2 t₃) dflt).NoSetAll = true := by
  induction tbl with
  | nil => simpa using hd
  | cons a rest ih =>
    simp only [List.foldr_cons]
    have ⟨ha1, ha2⟩ := htbl a (List.mem_cons_self ..)
    exact noSetAll_ite (noSetAll_eq ht ha1) ha2 (ih (fun p hp => htbl p (List.mem_cons_of_mem a hp)))
theorem anyAllItTyped_udf_fold {ety : TermType} {t : Term} {tbl : List (Term × Term)} {dflt : Term}
    (ht : t.anyAllItTyped ety = true) (hd : dflt.anyAllItTyped ety = true)
    (htbl : ∀ p ∈ tbl, p.1.anyAllItTyped ety = true ∧ p.2.anyAllItTyped ety = true) :
    (tbl.foldr (λ (p : Term × Term) t₃ => Factory.ite (Factory.eq t p.1) p.2 t₃) dflt).anyAllItTyped ety = true := by
  induction tbl with
  | nil => simpa using hd
  | cons a rest ih =>
    simp only [List.foldr_cons]
    have ⟨ha1, ha2⟩ := htbl a (List.mem_cons_self ..)
    exact anyAllItTyped_ite (anyAllItTyped_eq ht ha1) ha2 (ih (fun p hp => htbl p (List.mem_cons_of_mem a hp)))

theorem noSetAll_app_uf {uf : UnaryFunction} {t : Term} {εs : SymEntities}
    (hwf : uf.WellFormed εs) (h : t.NoSetAll = true) : (Factory.app uf t).NoSetAll = true := by
  unfold Factory.app
  split
  · exact noSetAll_app1 (op := Op.uuf _) (by intro h; cases h) h
  · simp only [UnaryFunction.WellFormed, UDF.WellFormed] at hwf
    split
    · split
      · rename_i t' hfind
        exact isLiteral_noSetAll _ (hwf.right.right.right t t' (Map.find?_mem_toList hfind)).right.right.left.right
      · exact isLiteral_noSetAll _ hwf.left.right
    · apply noSetAll_udf_fold h (isLiteral_noSetAll _ hwf.left.right)
      intro p hp
      have := hwf.right.right.right p.1 p.2 (by cases p; exact hp)
      exact ⟨isLiteral_noSetAll _ this.left.right, isLiteral_noSetAll _ this.right.right.left.right⟩
theorem anyAllItTyped_app_uf {ety : TermType} {uf : UnaryFunction} {t : Term} {εs : SymEntities}
    (hwf : uf.WellFormed εs) (h : t.anyAllItTyped ety = true) : (Factory.app uf t).anyAllItTyped ety = true := by
  unfold Factory.app
  split
  · exact anyAllItTyped_app1 (op := Op.uuf _) h
  · simp only [UnaryFunction.WellFormed, UDF.WellFormed] at hwf
    split
    · split
      · rename_i t' hfind
        exact isLiteral_anyAllItTyped _ (hwf.right.right.right t t' (Map.find?_mem_toList hfind)).right.right.left.right
      · exact isLiteral_anyAllItTyped _ hwf.left.right
    · apply anyAllItTyped_udf_fold h (isLiteral_anyAllItTyped _ hwf.left.right)
      intro p hp
      have := hwf.right.right.right p.1 p.2 (by cases p; exact hp)
      exact ⟨isLiteral_anyAllItTyped _ this.left.right, isLiteral_anyAllItTyped _ this.right.right.left.right⟩

/-! ### compileAttrsOf / compileHasAttr / compileGetAttr -/

theorem noSetAll_compileAttrsOf {t r : Term} {εs : SymEntities} (hwε : εs.WellFormed)
    (h : t.NoSetAll = true) (hok : compileAttrsOf t εs = Except.ok r) : r.NoSetAll = true := by
  rcases compileAttrsOf_ok_implies hok with ⟨rty, _, rfl⟩ | ⟨ety, fₐ, _, hf, rfl⟩
  · exact h
  · exact noSetAll_app_uf (wf_εs_implies_wf_attrs hwε hf).left h
theorem anyAllItTyped_compileAttrsOf {ety' : TermType} {t r : Term} {εs : SymEntities} (hwε : εs.WellFormed)
    (h : t.anyAllItTyped ety' = true) (hok : compileAttrsOf t εs = Except.ok r) : r.anyAllItTyped ety' = true := by
  rcases compileAttrsOf_ok_implies hok with ⟨rty, _, rfl⟩ | ⟨ety, fₐ, _, hf, rfl⟩
  · exact h
  · exact anyAllItTyped_app_uf (wf_εs_implies_wf_attrs hwε hf).left h

theorem noSetAll_compileHasAttr {t r : Term} {a : Attr} {εs : SymEntities} (hwε : εs.WellFormed)
    (h : t.NoSetAll = true) (hok : compileHasAttr t a εs = Except.ok r) : r.NoSetAll = true := by
  obtain ⟨t₂, rty, hA, hR⟩ := compileHasAttr_ok_implies hok
  have h2 := noSetAll_compileAttrsOf hwε h hA
  unfold RecordHasAttr at hR
  obtain ⟨_, hR⟩ := hR
  split at hR <;> subst hR
  · exact noSetAll_someOf (noSetAll_isSome (noSetAll_record_get h2))
  · exact noSetAll_someOf (by simp [Term.NoSetAll])
  · exact noSetAll_someOf (by simp [Term.NoSetAll])
theorem anyAllItTyped_compileHasAttr {ety' : TermType} {t r : Term} {a : Attr} {εs : SymEntities} (hwε : εs.WellFormed)
    (h : t.anyAllItTyped ety' = true) (hok : compileHasAttr t a εs = Except.ok r) : r.anyAllItTyped ety' = true := by
  obtain ⟨t₂, rty, hA, hR⟩ := compileHasAttr_ok_implies hok
  have h2 := anyAllItTyped_compileAttrsOf hwε h hA
  unfold RecordHasAttr at hR
  obtain ⟨_, hR⟩ := hR
  split at hR <;> subst hR
  · exact anyAllItTyped_someOf (anyAllItTyped_isSome (anyAllItTyped_record_get h2))
  · exact anyAllItTyped_someOf (by simp [Term.anyAllItTyped])
  · exact anyAllItTyped_someOf (by simp [Term.anyAllItTyped])

theorem noSetAll_compileGetAttr {t r : Term} {a : Attr} {εs : SymEntities} (hwε : εs.WellFormed)
    (h : t.NoSetAll = true) (hok : compileGetAttr t a εs = Except.ok r) : r.NoSetAll = true := by
  obtain ⟨t₂, rty, hA, hR⟩ := compileGetAttr_ok_implies hok
  have h2 := noSetAll_compileAttrsOf hwε h hA
  unfold RecordGetAttr at hR
  obtain ⟨_, tyₐ, _, hR⟩ := hR
  split at hR <;> subst hR
  · exact noSetAll_record_get h2
  · exact noSetAll_someOf (noSetAll_record_get h2)
theorem anyAllItTyped_compileGetAttr {ety' : TermType} {t r : Term} {a : Attr} {εs : SymEntities} (hwε : εs.WellFormed)
    (h : t.anyAllItTyped ety' = true) (hok : compileGetAttr t a εs = Except.ok r) : r.anyAllItTyped ety' = true := by
  obtain ⟨t₂, rty, hA, hR⟩ := compileGetAttr_ok_implies hok
  have h2 := anyAllItTyped_compileAttrsOf hwε h hA
  unfold RecordGetAttr at hR
  obtain ⟨_, tyₐ, _, hR⟩ := hR
  split at hR <;> subst hR
  · exact anyAllItTyped_record_get h2
  · exact anyAllItTyped_someOf (anyAllItTyped_record_get h2)

/-! ### compileApp₂ helpers: ifTrue, tagOf, SymTags.hasTag/getTag, compileInₑ/ₛ, compileHasTag/GetTag -/

theorem noSetAll_ifTrue {g t : Term} (hg : g.NoSetAll = true) (ht : t.NoSetAll = true) : (Factory.ifTrue g t).NoSetAll = true := by
  unfold Factory.ifTrue; exact noSetAll_ite hg (noSetAll_someOf ht) noSetAll_noneOf
theorem anyAllItTyped_ifTrue {ety : TermType} {g t : Term} (hg : g.anyAllItTyped ety = true) (ht : t.anyAllItTyped ety = true) : (Factory.ifTrue g t).anyAllItTyped ety = true := by
  unfold Factory.ifTrue; exact anyAllItTyped_ite hg (anyAllItTyped_someOf ht) anyAllItTyped_noneOf

theorem noSetAll_tagOf {e tg : Term} (he : e.NoSetAll = true) (ht : tg.NoSetAll = true) : (Factory.tagOf e tg).NoSetAll = true := by
  simp only [Factory.tagOf, EntityTag.mk, Term.NoSetAll, List.all_attach₂_snd, List.all_eq_true, Prod.forall, Map.toList]
  intro a t hmem; simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
theorem anyAllItTyped_tagOf {ety : TermType} {e tg : Term} (he : e.anyAllItTyped ety = true) (ht : tg.anyAllItTyped ety = true) : (Factory.tagOf e tg).anyAllItTyped ety = true := by
  simp only [Factory.tagOf, EntityTag.mk, Term.anyAllItTyped, List.all_attach₂_snd, List.all_eq_true, Prod.forall, Map.toList]
  intro a t hmem; simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption

theorem noSetAll_symTags_hasTag {τs : SymTags} {e tg : Term} {εs : SymEntities} {ety : EntityType}
    (hwτ : τs.WellFormed εs ety) (he : e.NoSetAll = true) (ht : tg.NoSetAll = true) : (τs.hasTag e tg).NoSetAll = true := by
  unfold SymTags.hasTag; exact noSetAll_set_member ht (noSetAll_app_uf hwτ.left he)
theorem anyAllItTyped_symTags_hasTag {ety' : TermType} {τs : SymTags} {e tg : Term} {εs : SymEntities} {ety : EntityType}
    (hwτ : τs.WellFormed εs ety) (he : e.anyAllItTyped ety' = true) (ht : tg.anyAllItTyped ety' = true) : (τs.hasTag e tg).anyAllItTyped ety' = true := by
  unfold SymTags.hasTag; exact anyAllItTyped_set_member ht (anyAllItTyped_app_uf hwτ.left he)

theorem noSetAll_symTags_getTag {τs : SymTags} {e tg : Term} {εs : SymEntities} {ety : EntityType}
    (hwτ : τs.WellFormed εs ety) (he : e.NoSetAll = true) (ht : tg.NoSetAll = true) : (τs.getTag e tg).NoSetAll = true := by
  unfold SymTags.getTag SymTags.getTag!
  exact noSetAll_ifTrue (noSetAll_symTags_hasTag hwτ he ht) (noSetAll_app_uf hwτ.right.right.right.left (noSetAll_tagOf he ht))
theorem anyAllItTyped_symTags_getTag {ety' : TermType} {τs : SymTags} {e tg : Term} {εs : SymEntities} {ety : EntityType}
    (hwτ : τs.WellFormed εs ety) (he : e.anyAllItTyped ety' = true) (ht : tg.anyAllItTyped ety' = true) : (τs.getTag e tg).anyAllItTyped ety' = true := by
  unfold SymTags.getTag SymTags.getTag!
  exact anyAllItTyped_ifTrue (anyAllItTyped_symTags_hasTag hwτ he ht) (anyAllItTyped_app_uf hwτ.right.right.right.left (anyAllItTyped_tagOf he ht))

theorem noSetAll_compileInₑ {t₁ t₂ : Term} {ancs? : Option UnaryFunction} {εs : SymEntities} {ety₁ ety₂ : EntityType}
    (ha : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) (hwε : εs.WellFormed) (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (compileInₑ t₁ t₂ ancs?).NoSetAll = true := by
  simp only [compileInₑ]
  apply noSetAll_or
  · delta SymCC.compileInₑ.isEq; split <;> first | exact noSetAll_eq h1 h2 | simp [Term.NoSetAll]
  · delta SymCC.compileInₑ.isIn; split
    · exact noSetAll_set_member h2 (noSetAll_app_uf (wf_εs_implies_wf_ancs hwε ha.symm).left h1)
    · simp [Term.NoSetAll]
theorem anyAllItTyped_compileInₑ {ety' : TermType} {t₁ t₂ : Term} {ancs? : Option UnaryFunction} {εs : SymEntities} {ety₁ ety₂ : EntityType}
    (ha : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) (hwε : εs.WellFormed) (h1 : t₁.anyAllItTyped ety' = true) (h2 : t₂.anyAllItTyped ety' = true) : (compileInₑ t₁ t₂ ancs?).anyAllItTyped ety' = true := by
  simp only [compileInₑ]
  apply anyAllItTyped_or
  · delta SymCC.compileInₑ.isEq; split <;> first | exact anyAllItTyped_eq h1 h2 | simp [Term.anyAllItTyped]
  · delta SymCC.compileInₑ.isIn; split
    · exact anyAllItTyped_set_member h2 (anyAllItTyped_app_uf (wf_εs_implies_wf_ancs hwε ha.symm).left h1)
    · simp [Term.anyAllItTyped]

theorem noSetAll_compileInₛ {t ts : Term} {ancs? : Option UnaryFunction} {εs : SymEntities} {ety₁ ety₂ : EntityType}
    (ha : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) (hwε : εs.WellFormed) (h1 : t.NoSetAll = true) (h2 : ts.NoSetAll = true) : (compileInₛ t ts ancs?).NoSetAll = true := by
  simp only [compileInₛ]
  apply noSetAll_or
  · delta SymCC.compileInₛ.isIn₁; split <;> first | exact noSetAll_set_member h1 h2 | simp [Term.NoSetAll]
  · delta SymCC.compileInₛ.isIn₂; split
    · exact noSetAll_set_intersects h2 (noSetAll_app_uf (wf_εs_implies_wf_ancs hwε ha.symm).left h1)
    · simp [Term.NoSetAll]
theorem anyAllItTyped_compileInₛ {ety' : TermType} {t ts : Term} {ancs? : Option UnaryFunction} {εs : SymEntities} {ety₁ ety₂ : EntityType}
    (ha : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) (hwε : εs.WellFormed) (h1 : t.anyAllItTyped ety' = true) (h2 : ts.anyAllItTyped ety' = true) : (compileInₛ t ts ancs?).anyAllItTyped ety' = true := by
  simp only [compileInₛ]
  apply anyAllItTyped_or
  · delta SymCC.compileInₛ.isIn₁; split <;> first | exact anyAllItTyped_set_member h1 h2 | simp [Term.anyAllItTyped]
  · delta SymCC.compileInₛ.isIn₂; split
    · exact anyAllItTyped_set_intersects h2 (anyAllItTyped_app_uf (wf_εs_implies_wf_ancs hwε ha.symm).left h1)
    · simp [Term.anyAllItTyped]

theorem noSetAll_compileHasTag {e tg r : Term} {τs? : Option (Option SymTags)} {εs : SymEntities} {ety : EntityType}
    (hτ : τs? = εs.tags ety) (hwε : εs.WellFormed) (he : e.NoSetAll = true) (ht : tg.NoSetAll = true)
    (hok : compileHasTag e tg τs? = Except.ok r) : r.NoSetAll = true := by
  unfold compileHasTag at hok
  split at hok <;> simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok <;> subst hok
  · exact noSetAll_someOf (by simp [Term.NoSetAll])
  · rename_i τs
    exact noSetAll_someOf (noSetAll_symTags_hasTag (wf_εs_implies_wf_tags hwε (by rw [← hτ])) he ht)
theorem anyAllItTyped_compileHasTag {ety' : TermType} {e tg r : Term} {τs? : Option (Option SymTags)} {εs : SymEntities} {ety : EntityType}
    (hτ : τs? = εs.tags ety) (hwε : εs.WellFormed) (he : e.anyAllItTyped ety' = true) (ht : tg.anyAllItTyped ety' = true)
    (hok : compileHasTag e tg τs? = Except.ok r) : r.anyAllItTyped ety' = true := by
  unfold compileHasTag at hok
  split at hok <;> simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok <;> subst hok
  · exact anyAllItTyped_someOf (by simp [Term.anyAllItTyped])
  · rename_i τs
    exact anyAllItTyped_someOf (anyAllItTyped_symTags_hasTag (wf_εs_implies_wf_tags hwε (by rw [← hτ])) he ht)

theorem noSetAll_compileGetTag {e tg r : Term} {τs? : Option (Option SymTags)} {εs : SymEntities} {ety : EntityType}
    (hτ : τs? = εs.tags ety) (hwε : εs.WellFormed) (he : e.NoSetAll = true) (ht : tg.NoSetAll = true)
    (hok : compileGetTag e tg τs? = Except.ok r) : r.NoSetAll = true := by
  unfold compileGetTag at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok <;> subst hok
  rename_i τs
  exact noSetAll_symTags_getTag (wf_εs_implies_wf_tags hwε (by rw [← hτ])) he ht
theorem anyAllItTyped_compileGetTag {ety' : TermType} {e tg r : Term} {τs? : Option (Option SymTags)} {εs : SymEntities} {ety : EntityType}
    (hτ : τs? = εs.tags ety) (hwε : εs.WellFormed) (he : e.anyAllItTyped ety' = true) (ht : tg.anyAllItTyped ety' = true)
    (hok : compileGetTag e tg τs? = Except.ok r) : r.anyAllItTyped ety' = true := by
  unfold compileGetTag at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok <;> subst hok
  rename_i τs
  exact anyAllItTyped_symTags_getTag (wf_εs_implies_wf_tags hwε (by rw [← hτ])) he ht

/-! ### compileApp₂ -/

theorem noSetAll_compileApp₂ {op₂ : BinaryOp} {t₁ t₂ r : Term} {εs : SymEntities}
    (hwε : εs.WellFormed) (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true)
    (hok : compileApp₂ op₂ t₁ t₂ εs = Except.ok r) : r.NoSetAll = true := by
  unfold compileApp₂ at hok
  split at hok
  all_goals (try simp only [bind, Except.bind, someOf, Except.ok.injEq, reduceCtorEq] at hok)
  all_goals (try (exact noSetAll_compileHasTag rfl hwε h1 h2 hok))
  all_goals (try (exact noSetAll_compileGetTag rfl hwε h1 h2 hok))
  all_goals (try (first
    | (cases hre : reducibleEq t₁.typeOf t₂.typeOf <;>
        simp only [hre, bind, Except.bind, pure, someOf, Except.ok.injEq, reduceCtorEq] at hok <;>
        (try split at hok) <;> simp only [Except.ok.injEq, reduceCtorEq] at hok <;> subst hok <;>
        first | exact noSetAll_someOf (noSetAll_eq h1 h2) | exact noSetAll_someOf (by simp [Term.NoSetAll]))
    | (split at hok <;> simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok <;> subst hok <;>
        first | exact noSetAll_someOf (noSetAll_set_member h2 h1)
              | exact noSetAll_someOf (noSetAll_set_subset h2 h1)
              | exact noSetAll_someOf (noSetAll_set_intersects h1 h2))
    | (subst hok; first
        | exact noSetAll_someOf (noSetAll_bvslt h1 h2)
        | exact noSetAll_someOf (noSetAll_bvsle h1 h2)
        | exact noSetAll_someOf (noSetAll_bvslt (noSetAll_ext_datetime_val h1) (noSetAll_ext_datetime_val h2))
        | exact noSetAll_someOf (noSetAll_bvsle (noSetAll_ext_datetime_val h1) (noSetAll_ext_datetime_val h2))
        | exact noSetAll_someOf (noSetAll_bvslt (noSetAll_ext_duration_val h1) (noSetAll_ext_duration_val h2))
        | exact noSetAll_someOf (noSetAll_bvsle (noSetAll_ext_duration_val h1) (noSetAll_ext_duration_val h2))
        | exact noSetAll_ifFalse (noSetAll_bvsaddo h1 h2) (noSetAll_bvadd h1 h2)
        | exact noSetAll_ifFalse (noSetAll_bvssubo h1 h2) (noSetAll_bvsub h1 h2)
        | exact noSetAll_ifFalse (noSetAll_bvsmulo h1 h2) (noSetAll_bvmul h1 h2)
        | exact noSetAll_someOf (noSetAll_compileInₑ rfl hwε h1 h2)
        | exact noSetAll_someOf (noSetAll_compileInₛ rfl hwε h1 h2))))
  all_goals (exact absurd hok (by simp [reduceCtorEq]))
theorem anyAllItTyped_compileApp₂ {ety' : TermType} {op₂ : BinaryOp} {t₁ t₂ r : Term} {εs : SymEntities}
    (hwε : εs.WellFormed) (h1 : t₁.anyAllItTyped ety' = true) (h2 : t₂.anyAllItTyped ety' = true)
    (hok : compileApp₂ op₂ t₁ t₂ εs = Except.ok r) : r.anyAllItTyped ety' = true := by
  unfold compileApp₂ at hok
  split at hok
  all_goals (try simp only [bind, Except.bind, someOf, Except.ok.injEq, reduceCtorEq] at hok)
  all_goals (try (exact anyAllItTyped_compileHasTag rfl hwε h1 h2 hok))
  all_goals (try (exact anyAllItTyped_compileGetTag rfl hwε h1 h2 hok))
  all_goals (try (first
    | (cases hre : reducibleEq t₁.typeOf t₂.typeOf <;>
        simp only [hre, bind, Except.bind, pure, someOf, Except.ok.injEq, reduceCtorEq] at hok <;>
        (try split at hok) <;> simp only [Except.ok.injEq, reduceCtorEq] at hok <;> subst hok <;>
        first | exact anyAllItTyped_someOf (anyAllItTyped_eq h1 h2) | exact anyAllItTyped_someOf (by simp [Term.anyAllItTyped]))
    | (split at hok <;> simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok <;> subst hok <;>
        first | exact anyAllItTyped_someOf (anyAllItTyped_set_member h2 h1)
              | exact anyAllItTyped_someOf (anyAllItTyped_set_subset h2 h1)
              | exact anyAllItTyped_someOf (anyAllItTyped_set_intersects h1 h2))
    | (subst hok; first
        | exact anyAllItTyped_someOf (anyAllItTyped_bvslt h1 h2)
        | exact anyAllItTyped_someOf (anyAllItTyped_bvsle h1 h2)
        | exact anyAllItTyped_someOf (anyAllItTyped_bvslt (anyAllItTyped_ext_datetime_val h1) (anyAllItTyped_ext_datetime_val h2))
        | exact anyAllItTyped_someOf (anyAllItTyped_bvsle (anyAllItTyped_ext_datetime_val h1) (anyAllItTyped_ext_datetime_val h2))
        | exact anyAllItTyped_someOf (anyAllItTyped_bvslt (anyAllItTyped_ext_duration_val h1) (anyAllItTyped_ext_duration_val h2))
        | exact anyAllItTyped_someOf (anyAllItTyped_bvsle (anyAllItTyped_ext_duration_val h1) (anyAllItTyped_ext_duration_val h2))
        | exact anyAllItTyped_ifFalse (anyAllItTyped_bvsaddo h1 h2) (anyAllItTyped_bvadd h1 h2)
        | exact anyAllItTyped_ifFalse (anyAllItTyped_bvssubo h1 h2) (anyAllItTyped_bvsub h1 h2)
        | exact anyAllItTyped_ifFalse (anyAllItTyped_bvsmulo h1 h2) (anyAllItTyped_bvmul h1 h2)
        | exact anyAllItTyped_someOf (anyAllItTyped_compileInₑ rfl hwε h1 h2)
        | exact anyAllItTyped_someOf (anyAllItTyped_compileInₛ rfl hwε h1 h2))))
  all_goals (exact absurd hok (by simp [reduceCtorEq]))

/-! ### ext encoders (NoSetAll) -/

private theorem lit_ns {t : Term} (h : t.isLiteral = true) : t.NoSetAll = true := isLiteral_noSetAll t h

theorem ns_Decimal_lessThan {t₁ t₂ : Term} (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (Decimal.lessThan t₁ t₂).NoSetAll = true := by
  unfold Decimal.lessThan; exact noSetAll_bvslt (noSetAll_ext_decimal_val h1) (noSetAll_ext_decimal_val h2)
theorem ns_Decimal_lessThanOrEqual {t₁ t₂ : Term} (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (Decimal.lessThanOrEqual t₁ t₂).NoSetAll = true := by
  unfold Decimal.lessThanOrEqual; exact noSetAll_bvsle (noSetAll_ext_decimal_val h1) (noSetAll_ext_decimal_val h2)
theorem ns_Decimal_greaterThan {t₁ t₂ : Term} (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (Decimal.greaterThan t₁ t₂).NoSetAll = true := by
  unfold Decimal.greaterThan; exact ns_Decimal_lessThan h2 h1
theorem ns_Decimal_greaterThanOrEqual {t₁ t₂ : Term} (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (Decimal.greaterThanOrEqual t₁ t₂).NoSetAll = true := by
  unfold Decimal.greaterThanOrEqual; exact ns_Decimal_lessThanOrEqual h2 h1

theorem ns_IPAddr_isIpv4 {t : Term} (h : t.NoSetAll = true) : (IPAddr.isIpv4 t).NoSetAll = true := by
  unfold IPAddr.isIpv4; exact noSetAll_ext_ipaddr_isV4 h
theorem ns_IPAddr_isIpv6 {t : Term} (h : t.NoSetAll = true) : (IPAddr.isIpv6 t).NoSetAll = true := by
  unfold IPAddr.isIpv6; exact noSetAll_not (noSetAll_ext_ipaddr_isV4 h)
theorem ns_IPAddr_subnetWidth {w : Nat} {ipPre : Term} (h : ipPre.NoSetAll = true) : (IPAddr.subnetWidth w ipPre).NoSetAll = true := by
  unfold IPAddr.subnetWidth
  exact noSetAll_ite (noSetAll_isNone h) (lit_ns (by simp [Term.isLiteral])) (noSetAll_bvsub (lit_ns (by simp [Term.isLiteral])) (noSetAll_zero_extend (noSetAll_option_get h)))
theorem ns_IPAddr_range {w : Nat} {ipAddr ipPre : Term} (ha : ipAddr.NoSetAll = true) (hp : ipPre.NoSetAll = true) :
    (IPAddr.range w ipAddr ipPre).1.NoSetAll = true ∧ (IPAddr.range w ipAddr ipPre).2.NoSetAll = true := by
  unfold IPAddr.range
  have hw := ns_IPAddr_subnetWidth (w := w) hp
  have hlo : (Factory.bvshl (Factory.bvlshr ipAddr (IPAddr.subnetWidth w ipPre)) (IPAddr.subnetWidth w ipPre)).NoSetAll = true :=
    noSetAll_bvshl (noSetAll_bvlshr ha hw) hw
  exact ⟨hlo, noSetAll_bvsub (noSetAll_bvadd hlo (noSetAll_bvshl (lit_ns (by simp [Term.isLiteral])) hw)) (lit_ns (by simp [Term.isLiteral]))⟩
theorem ns_IPAddr_inRange {rng : Term → Term × Term} {t₁ t₂ : Term}
    (hr : ∀ t, t.NoSetAll = true → (rng t).1.NoSetAll = true ∧ (rng t).2.NoSetAll = true)
    (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (IPAddr.inRange rng t₁ t₂).NoSetAll = true := by
  unfold IPAddr.inRange
  exact noSetAll_and (noSetAll_bvule (hr t₁ h1).2 (hr t₂ h2).2) (noSetAll_bvule (hr t₂ h2).1 (hr t₁ h1).1)
theorem ns_IPAddr_inRangeV {isIp : Term → Term} {rng : Term → Term × Term} {t₁ t₂ : Term}
    (hip : ∀ t, t.NoSetAll = true → (isIp t).NoSetAll = true)
    (hr : ∀ t, t.NoSetAll = true → (rng t).1.NoSetAll = true ∧ (rng t).2.NoSetAll = true)
    (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (IPAddr.inRangeV isIp rng t₁ t₂).NoSetAll = true := by
  unfold IPAddr.inRangeV
  exact noSetAll_and (hip t₁ h1) (noSetAll_and (hip t₂ h2) (ns_IPAddr_inRange hr h1 h2))
theorem ns_IPAddr_rangeV4 {t : Term} (h : t.NoSetAll = true) : (IPAddr.rangeV4 t).1.NoSetAll = true ∧ (IPAddr.rangeV4 t).2.NoSetAll = true := by
  unfold IPAddr.rangeV4; exact ns_IPAddr_range (noSetAll_ext_ipaddr_addrV4 h) (noSetAll_ext_ipaddr_prefixV4 h)
theorem ns_IPAddr_rangeV6 {t : Term} (h : t.NoSetAll = true) : (IPAddr.rangeV6 t).1.NoSetAll = true ∧ (IPAddr.rangeV6 t).2.NoSetAll = true := by
  unfold IPAddr.rangeV6; exact ns_IPAddr_range (noSetAll_ext_ipaddr_addrV6 h) (noSetAll_ext_ipaddr_prefixV6 h)
theorem ns_IPAddr_isInRange {t₁ t₂ : Term} (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) : (IPAddr.isInRange t₁ t₂).NoSetAll = true := by
  unfold IPAddr.isInRange
  exact noSetAll_or (ns_IPAddr_inRangeV (fun _ h => ns_IPAddr_isIpv4 h) (fun _ h => ns_IPAddr_rangeV4 h) h1 h2)
                    (ns_IPAddr_inRangeV (fun _ h => ns_IPAddr_isIpv6 h) (fun _ h => ns_IPAddr_rangeV6 h) h1 h2)
theorem ns_IPAddr_ipTerm {ip} : (IPAddr.ipTerm ip).NoSetAll = true := by unfold IPAddr.ipTerm; simp [Term.NoSetAll]
theorem ns_IPAddr_inRangeLit {t : Term} {c4 c6} (h : t.NoSetAll = true) : (IPAddr.inRangeLit t c4 c6).NoSetAll = true := by
  unfold IPAddr.inRangeLit
  exact noSetAll_ite (ns_IPAddr_isIpv4 h) (ns_IPAddr_inRange (fun _ h => ns_IPAddr_rangeV4 h) h ns_IPAddr_ipTerm) (ns_IPAddr_inRange (fun _ h => ns_IPAddr_rangeV6 h) h ns_IPAddr_ipTerm)
theorem ns_IPAddr_isLoopback {t : Term} (h : t.NoSetAll = true) : (IPAddr.isLoopback t).NoSetAll = true := by
  unfold IPAddr.isLoopback; exact ns_IPAddr_inRangeLit h
theorem ns_IPAddr_isMulticast {t : Term} (h : t.NoSetAll = true) : (IPAddr.isMulticast t).NoSetAll = true := by
  unfold IPAddr.isMulticast; exact ns_IPAddr_inRangeLit h

theorem ns_Duration_toMilliseconds {t : Term} (h : t.NoSetAll = true) : (Duration.toMilliseconds t).NoSetAll = true := by
  unfold Duration.toMilliseconds; exact noSetAll_ext_duration_val h
theorem ns_Duration_toSeconds {t : Term} (h : t.NoSetAll = true) : (Duration.toSeconds t).NoSetAll = true := by
  unfold Duration.toSeconds; exact noSetAll_bvsdiv (ns_Duration_toMilliseconds h) (lit_ns (by simp [Term.isLiteral]))
theorem ns_Duration_toMinutes {t : Term} (h : t.NoSetAll = true) : (Duration.toMinutes t).NoSetAll = true := by
  unfold Duration.toMinutes; exact noSetAll_bvsdiv (ns_Duration_toSeconds h) (lit_ns (by simp [Term.isLiteral]))
theorem ns_Duration_toHours {t : Term} (h : t.NoSetAll = true) : (Duration.toHours t).NoSetAll = true := by
  unfold Duration.toHours; exact noSetAll_bvsdiv (ns_Duration_toMinutes h) (lit_ns (by simp [Term.isLiteral]))
theorem ns_Duration_toDays {t : Term} (h : t.NoSetAll = true) : (Duration.toDays t).NoSetAll = true := by
  unfold Duration.toDays; exact noSetAll_bvsdiv (ns_Duration_toHours h) (lit_ns (by simp [Term.isLiteral]))

theorem ns_Datetime_offset {dt dur : Term} (h1 : dt.NoSetAll = true) (h2 : dur.NoSetAll = true) : (Datetime.offset dt dur).NoSetAll = true := by
  unfold Datetime.offset
  exact noSetAll_ifFalse (noSetAll_bvsaddo (noSetAll_ext_datetime_val h1) (noSetAll_ext_duration_val h2)) (noSetAll_ext_datetime_ofBitVec (noSetAll_bvadd (noSetAll_ext_datetime_val h1) (noSetAll_ext_duration_val h2)))
theorem ns_Datetime_durationSince {dt₁ dt₂ : Term} (h1 : dt₁.NoSetAll = true) (h2 : dt₂.NoSetAll = true) : (Datetime.durationSince dt₁ dt₂).NoSetAll = true := by
  unfold Datetime.durationSince
  exact noSetAll_ifFalse (noSetAll_bvssubo (noSetAll_ext_datetime_val h1) (noSetAll_ext_datetime_val h2)) (noSetAll_ext_duration_ofBitVec (noSetAll_bvsub (noSetAll_ext_datetime_val h1) (noSetAll_ext_datetime_val h2)))
theorem ns_Datetime_toDate {dt : Term} (h : dt.NoSetAll = true) : (Datetime.toDate dt).NoSetAll = true := by
  unfold Datetime.toDate
  have hv := noSetAll_ext_datetime_val h
  have hms : (Term.prim (TermPrim.bitvec (Int64.toBitVec 86400000))).NoSetAll = true := by simp [Term.NoSetAll]
  exact noSetAll_ifFalse (noSetAll_bvssubo hv (noSetAll_bvsmod hv hms)) (noSetAll_ext_datetime_ofBitVec (noSetAll_bvsub hv (noSetAll_bvsmod hv hms)))
theorem ns_Datetime_toTime {dt : Term} (h : dt.NoSetAll = true) : (Datetime.toTime dt).NoSetAll = true := by
  unfold Datetime.toTime
  apply noSetAll_ext_duration_ofBitVec
  have hv := noSetAll_ext_datetime_val h
  have hz : (Term.prim (TermPrim.bitvec (Int64.toBitVec 0))).NoSetAll = true := by simp [Term.NoSetAll]
  have hms : (Term.prim (TermPrim.bitvec (Int64.toBitVec 86400000))).NoSetAll = true := by simp [Term.NoSetAll]
  exact noSetAll_ite (noSetAll_bvsle hz hv) (noSetAll_bvsrem hv hms) (noSetAll_ite (noSetAll_eq (noSetAll_bvsrem hv hms) hz) hz (noSetAll_bvadd (noSetAll_bvsrem hv hms) hms))

/-! ### compileCall wrappers + compileCall (NoSetAll) -/

theorem noSetAll_compileCall₀ {α} [Coe α Ext] {mk : String → Option α} {t r : Term} (hok : compileCall₀ mk t = Except.ok r) : r.NoSetAll = true := by
  unfold compileCall₀ at hok
  split at hok <;> try split at hok
  all_goals simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok
  all_goals (subst hok; exact noSetAll_someOf (by simp [Term.NoSetAll]))
theorem noSetAll_ccwe1 {xty enc} {t₁ r : Term} (henc : ∀ x, x.NoSetAll = true → (enc x).NoSetAll = true) (h1 : t₁.NoSetAll = true) (hok : compileCallWithError₁ xty enc t₁ = Except.ok r) : r.NoSetAll = true := by
  unfold compileCallWithError₁ at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
  subst hok; exact noSetAll_ifSome h1 (henc _ (noSetAll_option_get h1))
theorem noSetAll_ccwe2 {xty₁ xty₂ enc} {t₁ t₂ r : Term} (henc : ∀ x y, x.NoSetAll = true → y.NoSetAll = true → (enc x y).NoSetAll = true) (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) (hok : compileCallWithError₂ xty₁ xty₂ enc t₁ t₂ = Except.ok r) : r.NoSetAll = true := by
  unfold compileCallWithError₂ at hok
  simp only [] at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
  subst hok; exact noSetAll_ifSome h1 (noSetAll_ifSome h2 (henc _ _ (noSetAll_option_get h1) (noSetAll_option_get h2)))
theorem noSetAll_cc1 {xty enc} {t₁ r : Term} (henc : ∀ x, x.NoSetAll = true → (enc x).NoSetAll = true) (h1 : t₁.NoSetAll = true) (hok : compileCall₁ xty enc t₁ = Except.ok r) : r.NoSetAll = true := by
  unfold compileCall₁ at hok; exact noSetAll_ccwe1 (fun x hx => noSetAll_someOf (henc x hx)) h1 hok
theorem noSetAll_cc2 {xty enc} {t₁ t₂ r : Term} (henc : ∀ x y, x.NoSetAll = true → y.NoSetAll = true → (enc x y).NoSetAll = true) (h1 : t₁.NoSetAll = true) (h2 : t₂.NoSetAll = true) (hok : compileCall₂ xty enc t₁ t₂ = Except.ok r) : r.NoSetAll = true := by
  unfold compileCall₂ at hok; exact noSetAll_ccwe2 (fun x y hx hy => noSetAll_someOf (henc x y hx hy)) h1 h2 hok

set_option maxHeartbeats 1000000 in
theorem noSetAll_compileCall {xfn : ExtFun} {ts : List Term} {r : Term}
    (hts : ∀ t ∈ ts, t.NoSetAll = true) (hok : compileCall xfn ts = Except.ok r) : r.NoSetAll = true := by
  unfold compileCall at hok
  split at hok <;>
    rename_i heq <;>
    first
    | exact noSetAll_compileCall₀ hok
    | ( -- unary (compileCall₁ / WithError₁): ts = [t₁]
        first
        | exact noSetAll_cc1 (fun x hx => ns_IPAddr_isIpv4 hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_IPAddr_isIpv6 hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_IPAddr_isLoopback hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_IPAddr_isMulticast hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_ccwe1 (fun x hx => ns_Datetime_toDate hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_Datetime_toTime hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_Duration_toMilliseconds hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_Duration_toSeconds hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_Duration_toMinutes hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_Duration_toHours hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc1 (fun x hx => ns_Duration_toDays hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok )
    | ( -- binary (compileCall₂ / WithError₂): ts = [t₁, t₂]
        first
        | exact noSetAll_cc2 (fun x y hx hy => ns_Decimal_lessThan hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc2 (fun x y hx hy => ns_Decimal_lessThanOrEqual hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc2 (fun x y hx hy => ns_Decimal_greaterThan hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc2 (fun x y hx hy => ns_Decimal_greaterThanOrEqual hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_cc2 (fun x y hx hy => ns_IPAddr_isInRange hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_ccwe2 (fun x y hx hy => ns_Datetime_offset hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact noSetAll_ccwe2 (fun x y hx hy => ns_Datetime_durationSince hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok )
    | exact absurd hok (by simp [reduceCtorEq])
/-! ### ext encoders (anyAllItTyped) -/

private theorem lit_aa {ety : TermType} {t : Term} (h : t.isLiteral = true) : t.anyAllItTyped ety = true := isLiteral_anyAllItTyped t h

theorem aa_Decimal_lessThan {t₁ t₂ : Term} (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) : (Decimal.lessThan t₁ t₂).anyAllItTyped ety = true := by
  unfold Decimal.lessThan; exact anyAllItTyped_bvslt (anyAllItTyped_ext_decimal_val h1) (anyAllItTyped_ext_decimal_val h2)
theorem aa_Decimal_lessThanOrEqual {t₁ t₂ : Term} (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) : (Decimal.lessThanOrEqual t₁ t₂).anyAllItTyped ety = true := by
  unfold Decimal.lessThanOrEqual; exact anyAllItTyped_bvsle (anyAllItTyped_ext_decimal_val h1) (anyAllItTyped_ext_decimal_val h2)
theorem aa_Decimal_greaterThan {t₁ t₂ : Term} (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) : (Decimal.greaterThan t₁ t₂).anyAllItTyped ety = true := by
  unfold Decimal.greaterThan; exact aa_Decimal_lessThan h2 h1
theorem aa_Decimal_greaterThanOrEqual {t₁ t₂ : Term} (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) : (Decimal.greaterThanOrEqual t₁ t₂).anyAllItTyped ety = true := by
  unfold Decimal.greaterThanOrEqual; exact aa_Decimal_lessThanOrEqual h2 h1

theorem aa_IPAddr_isIpv4 {t : Term} (h : t.anyAllItTyped ety = true) : (IPAddr.isIpv4 t).anyAllItTyped ety = true := by
  unfold IPAddr.isIpv4; exact anyAllItTyped_ext_ipaddr_isV4 h
theorem aa_IPAddr_isIpv6 {t : Term} (h : t.anyAllItTyped ety = true) : (IPAddr.isIpv6 t).anyAllItTyped ety = true := by
  unfold IPAddr.isIpv6; exact anyAllItTyped_not (anyAllItTyped_ext_ipaddr_isV4 h)
theorem aa_IPAddr_subnetWidth {w : Nat} {ipPre : Term} (h : ipPre.anyAllItTyped ety = true) : (IPAddr.subnetWidth w ipPre).anyAllItTyped ety = true := by
  unfold IPAddr.subnetWidth
  exact anyAllItTyped_ite (anyAllItTyped_isNone h) (lit_aa (by simp [Term.isLiteral])) (anyAllItTyped_bvsub (lit_aa (by simp [Term.isLiteral])) (anyAllItTyped_zero_extend (anyAllItTyped_option_get h)))
theorem aa_IPAddr_range {w : Nat} {ipAddr ipPre : Term} (ha : ipAddr.anyAllItTyped ety = true) (hp : ipPre.anyAllItTyped ety = true) :
    (IPAddr.range w ipAddr ipPre).1.anyAllItTyped ety = true ∧ (IPAddr.range w ipAddr ipPre).2.anyAllItTyped ety = true := by
  unfold IPAddr.range
  have hw := aa_IPAddr_subnetWidth (w := w) hp
  have hlo : (Factory.bvshl (Factory.bvlshr ipAddr (IPAddr.subnetWidth w ipPre)) (IPAddr.subnetWidth w ipPre)).anyAllItTyped ety = true :=
    anyAllItTyped_bvshl (anyAllItTyped_bvlshr ha hw) hw
  exact ⟨hlo, anyAllItTyped_bvsub (anyAllItTyped_bvadd hlo (anyAllItTyped_bvshl (lit_aa (by simp [Term.isLiteral])) hw)) (lit_aa (by simp [Term.isLiteral]))⟩
theorem aa_IPAddr_inRange {rng : Term → Term × Term} {t₁ t₂ : Term}
    (hr : ∀ t, t.anyAllItTyped ety = true → (rng t).1.anyAllItTyped ety = true ∧ (rng t).2.anyAllItTyped ety = true)
    (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) : (IPAddr.inRange rng t₁ t₂).anyAllItTyped ety = true := by
  unfold IPAddr.inRange
  exact anyAllItTyped_and (anyAllItTyped_bvule (hr t₁ h1).2 (hr t₂ h2).2) (anyAllItTyped_bvule (hr t₂ h2).1 (hr t₁ h1).1)
theorem aa_IPAddr_inRangeV {isIp : Term → Term} {rng : Term → Term × Term} {t₁ t₂ : Term}
    (hip : ∀ t, t.anyAllItTyped ety = true → (isIp t).anyAllItTyped ety = true)
    (hr : ∀ t, t.anyAllItTyped ety = true → (rng t).1.anyAllItTyped ety = true ∧ (rng t).2.anyAllItTyped ety = true)
    (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) : (IPAddr.inRangeV isIp rng t₁ t₂).anyAllItTyped ety = true := by
  unfold IPAddr.inRangeV
  exact anyAllItTyped_and (hip t₁ h1) (anyAllItTyped_and (hip t₂ h2) (aa_IPAddr_inRange hr h1 h2))
theorem aa_IPAddr_rangeV4 {t : Term} (h : t.anyAllItTyped ety = true) : (IPAddr.rangeV4 t).1.anyAllItTyped ety = true ∧ (IPAddr.rangeV4 t).2.anyAllItTyped ety = true := by
  unfold IPAddr.rangeV4; exact aa_IPAddr_range (anyAllItTyped_ext_ipaddr_addrV4 h) (anyAllItTyped_ext_ipaddr_prefixV4 h)
theorem aa_IPAddr_rangeV6 {t : Term} (h : t.anyAllItTyped ety = true) : (IPAddr.rangeV6 t).1.anyAllItTyped ety = true ∧ (IPAddr.rangeV6 t).2.anyAllItTyped ety = true := by
  unfold IPAddr.rangeV6; exact aa_IPAddr_range (anyAllItTyped_ext_ipaddr_addrV6 h) (anyAllItTyped_ext_ipaddr_prefixV6 h)
theorem aa_IPAddr_isInRange {t₁ t₂ : Term} (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) : (IPAddr.isInRange t₁ t₂).anyAllItTyped ety = true := by
  unfold IPAddr.isInRange
  exact anyAllItTyped_or (aa_IPAddr_inRangeV (fun _ h => aa_IPAddr_isIpv4 h) (fun _ h => aa_IPAddr_rangeV4 h) h1 h2)
                    (aa_IPAddr_inRangeV (fun _ h => aa_IPAddr_isIpv6 h) (fun _ h => aa_IPAddr_rangeV6 h) h1 h2)
theorem aa_IPAddr_ipTerm {ip} : (IPAddr.ipTerm ip).anyAllItTyped ety = true := by unfold IPAddr.ipTerm; simp [Term.anyAllItTyped]
theorem aa_IPAddr_inRangeLit {t : Term} {c4 c6} (h : t.anyAllItTyped ety = true) : (IPAddr.inRangeLit t c4 c6).anyAllItTyped ety = true := by
  unfold IPAddr.inRangeLit
  exact anyAllItTyped_ite (aa_IPAddr_isIpv4 h) (aa_IPAddr_inRange (fun _ h => aa_IPAddr_rangeV4 h) h aa_IPAddr_ipTerm) (aa_IPAddr_inRange (fun _ h => aa_IPAddr_rangeV6 h) h aa_IPAddr_ipTerm)
theorem aa_IPAddr_isLoopback {t : Term} (h : t.anyAllItTyped ety = true) : (IPAddr.isLoopback t).anyAllItTyped ety = true := by
  unfold IPAddr.isLoopback; exact aa_IPAddr_inRangeLit h
theorem aa_IPAddr_isMulticast {t : Term} (h : t.anyAllItTyped ety = true) : (IPAddr.isMulticast t).anyAllItTyped ety = true := by
  unfold IPAddr.isMulticast; exact aa_IPAddr_inRangeLit h

theorem aa_Duration_toMilliseconds {t : Term} (h : t.anyAllItTyped ety = true) : (Duration.toMilliseconds t).anyAllItTyped ety = true := by
  unfold Duration.toMilliseconds; exact anyAllItTyped_ext_duration_val h
theorem aa_Duration_toSeconds {t : Term} (h : t.anyAllItTyped ety = true) : (Duration.toSeconds t).anyAllItTyped ety = true := by
  unfold Duration.toSeconds; exact anyAllItTyped_bvsdiv (aa_Duration_toMilliseconds h) (lit_aa (by simp [Term.isLiteral]))
theorem aa_Duration_toMinutes {t : Term} (h : t.anyAllItTyped ety = true) : (Duration.toMinutes t).anyAllItTyped ety = true := by
  unfold Duration.toMinutes; exact anyAllItTyped_bvsdiv (aa_Duration_toSeconds h) (lit_aa (by simp [Term.isLiteral]))
theorem aa_Duration_toHours {t : Term} (h : t.anyAllItTyped ety = true) : (Duration.toHours t).anyAllItTyped ety = true := by
  unfold Duration.toHours; exact anyAllItTyped_bvsdiv (aa_Duration_toMinutes h) (lit_aa (by simp [Term.isLiteral]))
theorem aa_Duration_toDays {t : Term} (h : t.anyAllItTyped ety = true) : (Duration.toDays t).anyAllItTyped ety = true := by
  unfold Duration.toDays; exact anyAllItTyped_bvsdiv (aa_Duration_toHours h) (lit_aa (by simp [Term.isLiteral]))

theorem aa_Datetime_offset {dt dur : Term} (h1 : dt.anyAllItTyped ety = true) (h2 : dur.anyAllItTyped ety = true) : (Datetime.offset dt dur).anyAllItTyped ety = true := by
  unfold Datetime.offset
  exact anyAllItTyped_ifFalse (anyAllItTyped_bvsaddo (anyAllItTyped_ext_datetime_val h1) (anyAllItTyped_ext_duration_val h2)) (anyAllItTyped_ext_datetime_ofBitVec (anyAllItTyped_bvadd (anyAllItTyped_ext_datetime_val h1) (anyAllItTyped_ext_duration_val h2)))
theorem aa_Datetime_durationSince {dt₁ dt₂ : Term} (h1 : dt₁.anyAllItTyped ety = true) (h2 : dt₂.anyAllItTyped ety = true) : (Datetime.durationSince dt₁ dt₂).anyAllItTyped ety = true := by
  unfold Datetime.durationSince
  exact anyAllItTyped_ifFalse (anyAllItTyped_bvssubo (anyAllItTyped_ext_datetime_val h1) (anyAllItTyped_ext_datetime_val h2)) (anyAllItTyped_ext_duration_ofBitVec (anyAllItTyped_bvsub (anyAllItTyped_ext_datetime_val h1) (anyAllItTyped_ext_datetime_val h2)))
theorem aa_Datetime_toDate {dt : Term} (h : dt.anyAllItTyped ety = true) : (Datetime.toDate dt).anyAllItTyped ety = true := by
  unfold Datetime.toDate
  have hv := anyAllItTyped_ext_datetime_val h
  have hms : (Term.prim (TermPrim.bitvec (Int64.toBitVec 86400000))).anyAllItTyped ety = true := by simp [Term.anyAllItTyped]
  exact anyAllItTyped_ifFalse (anyAllItTyped_bvssubo hv (anyAllItTyped_bvsmod hv hms)) (anyAllItTyped_ext_datetime_ofBitVec (anyAllItTyped_bvsub hv (anyAllItTyped_bvsmod hv hms)))
theorem aa_Datetime_toTime {dt : Term} (h : dt.anyAllItTyped ety = true) : (Datetime.toTime dt).anyAllItTyped ety = true := by
  unfold Datetime.toTime
  apply anyAllItTyped_ext_duration_ofBitVec
  have hv := anyAllItTyped_ext_datetime_val h
  have hz : (Term.prim (TermPrim.bitvec (Int64.toBitVec 0))).anyAllItTyped ety = true := by simp [Term.anyAllItTyped]
  have hms : (Term.prim (TermPrim.bitvec (Int64.toBitVec 86400000))).anyAllItTyped ety = true := by simp [Term.anyAllItTyped]
  exact anyAllItTyped_ite (anyAllItTyped_bvsle hz hv) (anyAllItTyped_bvsrem hv hms) (anyAllItTyped_ite (anyAllItTyped_eq (anyAllItTyped_bvsrem hv hms) hz) hz (anyAllItTyped_bvadd (anyAllItTyped_bvsrem hv hms) hms))

/-! ### compileCall wrappers + compileCall (anyAllItTyped) -/

theorem anyAllItTyped_compileCall₀ {α} [Coe α Ext] {mk : String → Option α} {t r : Term} (hok : compileCall₀ mk t = Except.ok r) : r.anyAllItTyped ety = true := by
  unfold compileCall₀ at hok
  split at hok <;> try split at hok
  all_goals simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok
  all_goals (subst hok; exact anyAllItTyped_someOf (by simp [Term.anyAllItTyped]))
theorem anyAllItTyped_ccwe1 {xty enc} {t₁ r : Term} (henc : ∀ x, x.anyAllItTyped ety = true → (enc x).anyAllItTyped ety = true) (h1 : t₁.anyAllItTyped ety = true) (hok : compileCallWithError₁ xty enc t₁ = Except.ok r) : r.anyAllItTyped ety = true := by
  unfold compileCallWithError₁ at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
  subst hok; exact anyAllItTyped_ifSome h1 (henc _ (anyAllItTyped_option_get h1))
theorem anyAllItTyped_ccwe2 {xty₁ xty₂ enc} {t₁ t₂ r : Term} (henc : ∀ x y, x.anyAllItTyped ety = true → y.anyAllItTyped ety = true → (enc x y).anyAllItTyped ety = true) (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) (hok : compileCallWithError₂ xty₁ xty₂ enc t₁ t₂ = Except.ok r) : r.anyAllItTyped ety = true := by
  unfold compileCallWithError₂ at hok
  simp only [] at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
  subst hok; exact anyAllItTyped_ifSome h1 (anyAllItTyped_ifSome h2 (henc _ _ (anyAllItTyped_option_get h1) (anyAllItTyped_option_get h2)))
theorem anyAllItTyped_cc1 {xty enc} {t₁ r : Term} (henc : ∀ x, x.anyAllItTyped ety = true → (enc x).anyAllItTyped ety = true) (h1 : t₁.anyAllItTyped ety = true) (hok : compileCall₁ xty enc t₁ = Except.ok r) : r.anyAllItTyped ety = true := by
  unfold compileCall₁ at hok; exact anyAllItTyped_ccwe1 (fun x hx => anyAllItTyped_someOf (henc x hx)) h1 hok
theorem anyAllItTyped_cc2 {xty enc} {t₁ t₂ r : Term} (henc : ∀ x y, x.anyAllItTyped ety = true → y.anyAllItTyped ety = true → (enc x y).anyAllItTyped ety = true) (h1 : t₁.anyAllItTyped ety = true) (h2 : t₂.anyAllItTyped ety = true) (hok : compileCall₂ xty enc t₁ t₂ = Except.ok r) : r.anyAllItTyped ety = true := by
  unfold compileCall₂ at hok; exact anyAllItTyped_ccwe2 (fun x y hx hy => anyAllItTyped_someOf (henc x y hx hy)) h1 h2 hok

set_option maxHeartbeats 1000000 in
theorem anyAllItTyped_compileCall {xfn : ExtFun} {ts : List Term} {r : Term}
    (hts : ∀ t ∈ ts, t.anyAllItTyped ety = true) (hok : compileCall xfn ts = Except.ok r) : r.anyAllItTyped ety = true := by
  unfold compileCall at hok
  split at hok <;>
    rename_i heq <;>
    first
    | exact anyAllItTyped_compileCall₀ hok
    | ( -- unary (compileCall₁ / WithError₁): ts = [t₁]
        first
        | exact anyAllItTyped_cc1 (fun x hx => aa_IPAddr_isIpv4 hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_IPAddr_isIpv6 hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_IPAddr_isLoopback hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_IPAddr_isMulticast hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_ccwe1 (fun x hx => aa_Datetime_toDate hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_Datetime_toTime hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_Duration_toMilliseconds hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_Duration_toSeconds hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_Duration_toMinutes hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_Duration_toHours hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc1 (fun x hx => aa_Duration_toDays hx) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok )
    | ( -- binary (compileCall₂ / WithError₂): ts = [t₁, t₂]
        first
        | exact anyAllItTyped_cc2 (fun x y hx hy => aa_Decimal_lessThan hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc2 (fun x y hx hy => aa_Decimal_lessThanOrEqual hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc2 (fun x y hx hy => aa_Decimal_greaterThan hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc2 (fun x y hx hy => aa_Decimal_greaterThanOrEqual hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_cc2 (fun x y hx hy => aa_IPAddr_isInRange hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_ccwe2 (fun x y hx hy => aa_Datetime_offset hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok
        | exact anyAllItTyped_ccwe2 (fun x y hx hy => aa_Datetime_durationSince hx hy) (hts _ (by simp [List.mem_cons, List.mem_singleton])) (hts _ (by simp [List.mem_cons, List.mem_singleton])) hok )
    | exact absurd hok (by simp [reduceCtorEq])
/-! ### compileExtHasAttr (via ExtHasAttrRec) -/

theorem noSetAll_compileExtHasAttrRec {t r : Term} {ats : List Attr} {εs} (hwε : εs.WellFormed) (h : t.NoSetAll = true)
    (hok : compileExtHasAttrRec t ats εs = Except.ok r) : r.NoSetAll = true := by
  induction ats generalizing t r with
  | nil =>
    rw [compileExtHasAttrRec] at hok
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hok; subst hok
    exact noSetAll_someOf (by simp [Term.NoSetAll])
  | cons a ats₁ ih =>
    cases hats : ats₁ with
    | nil =>
      subst hats
      simp only [compileExtHasAttrRec] at hok
      cases hH : compileHasAttr (option.get t) a εs <;>
        simp only [hH, bind, Except.bind, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
      simp only [Except.ok.injEq] at hok; subst hok
      exact noSetAll_ifSome h (noSetAll_compileHasAttr hwε (noSetAll_option_get h) hH)
    | cons b rest =>
      subst hats
      simp only [compileExtHasAttrRec] at hok
      cases hH : compileHasAttr (option.get t) a εs <;>
        simp only [hH, bind, Except.bind, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
      rename_i t₀
      have hhas : (ifSome t t₀).NoSetAll = true := noSetAll_ifSome h (noSetAll_compileHasAttr hwε (noSetAll_option_get h) hH)
      split at hok
      · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hok; subst hok; exact hhas
      · split at hok
        · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hok; subst hok; exact hhas
        · simp only [reduceCtorEq] at hok
        · rename_i t₂ hG
          cases hRec : compileExtHasAttrRec (ifSome t t₂) (b :: rest) εs with
          | error e => simp only [hRec, bind, Except.bind, Except.bind_err, reduceCtorEq] at hok
          | ok t₄ =>
            simp only [hRec, bind, Except.bind, Except.bind_ok] at hok
            have hrec := ih (t := ifSome t t₂) (noSetAll_ifSome h (noSetAll_compileGetAttr hwε (noSetAll_option_get h) hG)) hRec
            exact noSetAll_compileAnd hhas (fun t₄' he => by simp only [Except.ok.injEq] at he; subst he; exact hrec) hok

theorem anyAllItTyped_compileExtHasAttrRec {ety : TermType} {t r : Term} {ats : List Attr} {εs} (hwε : εs.WellFormed) (h : t.anyAllItTyped ety = true)
    (hok : compileExtHasAttrRec t ats εs = Except.ok r) : r.anyAllItTyped ety = true := by
  induction ats generalizing t r with
  | nil =>
    rw [compileExtHasAttrRec] at hok
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hok; subst hok
    exact anyAllItTyped_someOf (by simp [Term.anyAllItTyped])
  | cons a ats₁ ih =>
    cases hats : ats₁ with
    | nil =>
      subst hats
      simp only [compileExtHasAttrRec] at hok
      cases hH : compileHasAttr (option.get t) a εs <;>
        simp only [hH, bind, Except.bind, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
      simp only [Except.ok.injEq] at hok; subst hok
      exact anyAllItTyped_ifSome h (anyAllItTyped_compileHasAttr hwε (anyAllItTyped_option_get h) hH)
    | cons b rest =>
      subst hats
      simp only [compileExtHasAttrRec] at hok
      cases hH : compileHasAttr (option.get t) a εs <;>
        simp only [hH, bind, Except.bind, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
      rename_i t₀
      have hhas : (ifSome t t₀).anyAllItTyped ety = true := anyAllItTyped_ifSome h (anyAllItTyped_compileHasAttr hwε (anyAllItTyped_option_get h) hH)
      split at hok
      · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hok; subst hok; exact hhas
      · split at hok
        · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hok; subst hok; exact hhas
        · simp only [reduceCtorEq] at hok
        · rename_i t₂ hG
          cases hRec : compileExtHasAttrRec (ifSome t t₂) (b :: rest) εs with
          | error e => simp only [hRec, bind, Except.bind, Except.bind_err, reduceCtorEq] at hok
          | ok t₄ =>
            simp only [hRec, bind, Except.bind, Except.bind_ok] at hok
            have hrec := ih (t := ifSome t t₂) (anyAllItTyped_ifSome h (anyAllItTyped_compileGetAttr hwε (anyAllItTyped_option_get h) hG)) hRec
            exact anyAllItTyped_compileAnd hhas (fun t₄' he => by simp only [Except.ok.injEq] at he; subst he; exact hrec) hok


theorem noSetAll_compileExtHasAttr {t r : Term} {ats : List Attr} {εs : SymEntities} (hwε : εs.WellFormed)
    (h : t.NoSetAll = true) (hok : compileExtHasAttr t ats εs = Except.ok r) : r.NoSetAll = true := by
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  exact noSetAll_compileExtHasAttrRec hwε h hok
theorem anyAllItTyped_compileExtHasAttr {ety : TermType} {t r : Term} {ats : List Attr} {εs : SymEntities} (hwε : εs.WellFormed)
    (h : t.anyAllItTyped ety = true) (hok : compileExtHasAttr t ats εs = Except.ok r) : r.anyAllItTyped ety = true := by
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  exact anyAllItTyped_compileExtHasAttrRec hwε h hok

end Cedar.Thm
