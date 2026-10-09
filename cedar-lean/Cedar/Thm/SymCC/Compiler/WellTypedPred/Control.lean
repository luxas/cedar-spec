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

import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.ofType

/-!
D-73 option B, step (2): the `.and`/`.or`/`.ite` arms of `compilePred_well_typed`, as
standalone lemmas under the `Normal` premise (both operands `.bool`-typed). Because the
predicate is normalized (`typeOfAll` stores `normalize p …`), no dead short-circuit survives,
so every `.and`/`.or`/`.ite` sub-term has both operands compiling to `.option .bool`; the
`compile{And,Or,If}` factory then succeeds with a `.option .bool` result.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open SymCC

/-- `typeOfAnd` of two `.bool`-typed operands yields a `.bool`-typed result. -/
theorem typeOfAnd_bool_result {ty₁ ty₂ typ : TypedExpr} {b₁ b₂ : BoolType} {c₁ c₂ c' : Capabilities}
    (hb₁ : ty₁.typeOf = .bool b₁) (hb₂ : ty₂.typeOf = .bool b₂)
    (htp : typeOfAnd (ty₁, c₁) (.ok (ty₂, c₂)) = .ok (typ, c')) : ∃ b, typ.typeOf = .bool b := by
  cases b₁ <;> cases b₂ <;>
    simp only [typeOfAnd, hb₁, hb₂, Validation.ok, bind, Except.bind, Except.ok.injEq,
      Prod.mk.injEq, reduceCtorEq] at htp <;>
    (obtain ⟨h, -⟩ := htp; subst h;
     first | exact ⟨_, hb₁⟩ | exact ⟨_, rfl⟩)

/-- `typeOfOr` of two `.bool`-typed operands yields a `.bool`-typed result. -/
theorem typeOfOr_bool_result {ty₁ ty₂ typ : TypedExpr} {b₁ b₂ : BoolType} {c₁ c₂ c' : Capabilities}
    (hb₁ : ty₁.typeOf = .bool b₁) (hb₂ : ty₂.typeOf = .bool b₂)
    (htp : typeOfOr (ty₁, c₁) (.ok (ty₂, c₂)) = .ok (typ, c')) : ∃ b, typ.typeOf = .bool b := by
  cases b₁ <;> cases b₂ <;>
    simp only [typeOfOr, hb₁, hb₂, Validation.ok, bind, Except.bind, Except.ok.injEq,
      Prod.mk.injEq, reduceCtorEq] at htp <;>
    (obtain ⟨h, -⟩ := htp; subst h;
     first | exact ⟨_, hb₁⟩ | exact ⟨_, hb₂⟩ | exact ⟨_, rfl⟩)

/-- `typeOfIf` of a `.bool` condition and two `.bool`-typed branches yields a `.bool` result. -/
theorem typeOfIf_bool_result {tyc ty₂ ty₃ typ : TypedExpr} {bc b₂ b₃ : BoolType}
    {cc c₂ c₃ c' : Capabilities}
    (hbc : tyc.typeOf = .bool bc) (hb₂ : ty₂.typeOf = .bool b₂) (hb₃ : ty₃.typeOf = .bool b₃)
    (htp : typeOfIf (tyc, cc) (.ok (ty₂, c₂)) (.ok (ty₃, c₃)) = .ok (typ, c')) :
    ∃ b, typ.typeOf = .bool b := by
  cases bc <;> cases b₂ <;> cases b₃ <;>
    simp only [typeOfIf, hbc, hb₂, hb₃, Validation.ok, bind, Except.bind, Except.ok.injEq,
      Prod.mk.injEq, reduceCtorEq, lub?, lubBool] at htp <;>
    (first
      | (obtain ⟨h, -⟩ := htp; subst h; exact ⟨_, rfl⟩)
      | exact htp.elim)

/-- `compileAnd` of two WF `.option .bool` operands succeeds with a `.option .bool` term. -/
theorem compileAnd_bool_ok {εs : SymEntities} {t₁ t₂ : Term}
    (hw₁ : t₁.WellFormed εs) (hw₂ : t₂.WellFormed εs)
    (hty₁ : t₁.typeOf = .option .bool) (hty₂ : t₂.typeOf = .option .bool) :
    ∃ t, compileAnd t₁ (.ok t₂) = .ok t ∧ t.typeOf = .option .bool := by
  simp only [compileAnd, bind, Except.bind]
  split
  · exact ⟨_, rfl, hty₁⟩
  · simp only [hty₂, if_true, Except.ok.injEq, exists_eq_left']
    have hwo₁ := wf_option_get hw₁ hty₁
    have hwfalse : (Factory.someOf (.prim (.bool false))).WellFormed εs := Term.WellFormed.some_wf wf_bool
    have htyfalse : (Factory.someOf (.prim (.bool false))).typeOf = .option .bool := by
      simp only [Factory.someOf, typeOf_term_some, Term.typeOf, typeOf_bool]
    have hwi := wf_ite hwo₁.left hw₂ hwfalse hwo₁.right (by simp only [hty₂, htyfalse])
    rw [hty₂] at hwi
    exact (wf_ifSome_option hw₁ hwi.left hwi.right).right
  · rename_i hne; exact absurd hty₁ (by simp_all)

/-- `compileOr` of two WF `.option .bool` operands succeeds with a `.option .bool` term. -/
theorem compileOr_bool_ok {εs : SymEntities} {t₁ t₂ : Term}
    (hw₁ : t₁.WellFormed εs) (hw₂ : t₂.WellFormed εs)
    (hty₁ : t₁.typeOf = .option .bool) (hty₂ : t₂.typeOf = .option .bool) :
    ∃ t, compileOr t₁ (.ok t₂) = .ok t ∧ t.typeOf = .option .bool := by
  simp only [compileOr, bind, Except.bind]
  split
  · exact ⟨_, rfl, hty₁⟩
  · simp only [hty₂, if_true, Except.ok.injEq, exists_eq_left']
    have hwo₁ := wf_option_get hw₁ hty₁
    have hwtrue : (Factory.someOf (.prim (.bool true))).WellFormed εs := Term.WellFormed.some_wf wf_bool
    have htytrue : (Factory.someOf (.prim (.bool true))).typeOf = .option .bool := by
      simp only [Factory.someOf, typeOf_term_some, Term.typeOf, typeOf_bool]
    have hwi := wf_ite hwo₁.left hwtrue hw₂ hwo₁.right (by simp only [hty₂, htytrue])
    rw [htytrue] at hwi
    exact (wf_ifSome_option hw₁ hwi.left hwi.right).right
  · rename_i hne; exact absurd hty₁ (by simp_all)

/-- `compileIf` with a WF `.option .bool` condition and two WF equal-typed `.option .bool`
branches succeeds with a `.option .bool` term. -/
theorem compileIf_bool_ok {εs : SymEntities} {t₁ t₂ t₃ : Term}
    (hw₁ : t₁.WellFormed εs) (hw₂ : t₂.WellFormed εs) (hw₃ : t₃.WellFormed εs)
    (hty₁ : t₁.typeOf = .option .bool) (hty₂ : t₂.typeOf = .option .bool)
    (hty₃ : t₃.typeOf = .option .bool) :
    ∃ t, compileIf t₁ (.ok t₂) (.ok t₃) = .ok t ∧ t.typeOf = .option .bool := by
  simp only [compileIf, bind, Except.bind]
  split
  · exact ⟨_, rfl, hty₂⟩
  · exact ⟨_, rfl, hty₃⟩
  · simp only [hty₂, hty₃, if_true, Except.ok.injEq, exists_eq_left']
    have hwo₁ := wf_option_get hw₁ hty₁
    have hwi := wf_ite hwo₁.left hw₂ hw₃ hwo₁.right (by simp only [hty₂, hty₃])
    rw [hty₂] at hwi
    exact (wf_ifSome_option hw₁ hwi.left hwi.right).right
  · rename_i hne; exact absurd hty₁ (by simp_all)

/-- `.and` arm of `compilePred_well_typed`, under the `Normal`-provided premise that both
operands are `.bool`-typed (`ty₁.typeOf = .bool _`, `ty₂.typeOf = .bool _`). -/
theorem compilePred_well_typed_and
    {x₁ x₂ : Cedar.Spec.PredExpr} {ty₁ ty₂ typ : TypedExpr} {b₁ b₂ : BoolType}
    {elemTy : TermType} {c₁ c₂ c' : Capabilities} {Γ : TypeEnv} {it t₁ t₂ : Term}
    (hwε : (SymEnv.ofEnv Γ).WellFormed)
    (hitw : it.WellFormed (SymEnv.ofEnv Γ).entities)
    (hitty : it.typeOf = .option elemTy)
    (hok₁ : compilePred x₁ it (SymEnv.ofEnv Γ) = .ok t₁)
    (hty₁ : t₁.typeOf = .option (TermType.ofType ty₁.typeOf))
    (hok₂ : compilePred x₂ it (SymEnv.ofEnv Γ) = .ok t₂)
    (hty₂ : t₂.typeOf = .option (TermType.ofType ty₂.typeOf))
    (hb₁ : ty₁.typeOf = .bool b₁) (hb₂ : ty₂.typeOf = .bool b₂)
    (htp : typeOfAnd (ty₁, c₁) (.ok (ty₂, c₂)) = .ok (typ, c')) :
    ∃ t, compilePred (.and x₁ x₂) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType typ.typeOf) := by
  have ⟨hwf₁, _, _⟩ := compilePred_wf hwε hitw hitty hok₁
  have ⟨hwf₂, _, _⟩ := compilePred_wf hwε hitw hitty hok₂
  rw [hb₁, TermType.ofType] at hty₁
  rw [hb₂, TermType.ofType] at hty₂
  have ⟨t, hca, hcty⟩ := compileAnd_bool_ok hwf₁ hwf₂ hty₁ hty₂
  obtain ⟨b, htyp⟩ := typeOfAnd_bool_result hb₁ hb₂ htp
  refine ⟨t, by simp only [compilePred, hok₁, hok₂, Except.bind_ok, hca], ?_⟩
  rw [hcty, htyp, TermType.ofType]

/-- `.or` arm of `compilePred_well_typed`, under the `Normal` bool-operand premise. -/
theorem compilePred_well_typed_or
    {x₁ x₂ : Cedar.Spec.PredExpr} {ty₁ ty₂ typ : TypedExpr} {b₁ b₂ : BoolType}
    {elemTy : TermType} {c₁ c₂ c' : Capabilities} {Γ : TypeEnv} {it t₁ t₂ : Term}
    (hwε : (SymEnv.ofEnv Γ).WellFormed)
    (hitw : it.WellFormed (SymEnv.ofEnv Γ).entities)
    (hitty : it.typeOf = .option elemTy)
    (hok₁ : compilePred x₁ it (SymEnv.ofEnv Γ) = .ok t₁)
    (hty₁ : t₁.typeOf = .option (TermType.ofType ty₁.typeOf))
    (hok₂ : compilePred x₂ it (SymEnv.ofEnv Γ) = .ok t₂)
    (hty₂ : t₂.typeOf = .option (TermType.ofType ty₂.typeOf))
    (hb₁ : ty₁.typeOf = .bool b₁) (hb₂ : ty₂.typeOf = .bool b₂)
    (htp : typeOfOr (ty₁, c₁) (.ok (ty₂, c₂)) = .ok (typ, c')) :
    ∃ t, compilePred (.or x₁ x₂) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType typ.typeOf) := by
  have ⟨hwf₁, _, _⟩ := compilePred_wf hwε hitw hitty hok₁
  have ⟨hwf₂, _, _⟩ := compilePred_wf hwε hitw hitty hok₂
  rw [hb₁, TermType.ofType] at hty₁
  rw [hb₂, TermType.ofType] at hty₂
  have ⟨t, hco, hcty⟩ := compileOr_bool_ok hwf₁ hwf₂ hty₁ hty₂
  obtain ⟨b, htyp⟩ := typeOfOr_bool_result hb₁ hb₂ htp
  refine ⟨t, by simp only [compilePred, hok₁, hok₂, Except.bind_ok, hco], ?_⟩
  rw [hcty, htyp, TermType.ofType]

/-- `.ite` arm of `compilePred_well_typed`. Under `Normal` the stored predicate's branches
are the duplicated live branch (both `.bool`-typed and equal), and the condition is
`.bool`-typed, so `compileIf` succeeds with `.option .bool`. -/
theorem compilePred_well_typed_ite
    {x₁ x₂ x₃ : Cedar.Spec.PredExpr} {tyc ty₂ ty₃ typ : TypedExpr} {bc b₂ b₃ : BoolType}
    {elemTy : TermType} {cc c₂ c₃ c' : Capabilities} {Γ : TypeEnv} {it tc t₂ t₃ : Term}
    (hwε : (SymEnv.ofEnv Γ).WellFormed)
    (hitw : it.WellFormed (SymEnv.ofEnv Γ).entities)
    (hitty : it.typeOf = .option elemTy)
    (hokc : compilePred x₁ it (SymEnv.ofEnv Γ) = .ok tc)
    (htyc : tc.typeOf = .option (TermType.ofType tyc.typeOf))
    (hok₂ : compilePred x₂ it (SymEnv.ofEnv Γ) = .ok t₂)
    (hty₂ : t₂.typeOf = .option (TermType.ofType ty₂.typeOf))
    (hok₃ : compilePred x₃ it (SymEnv.ofEnv Γ) = .ok t₃)
    (hty₃ : t₃.typeOf = .option (TermType.ofType ty₃.typeOf))
    (hbc : tyc.typeOf = .bool bc) (hb₂ : ty₂.typeOf = .bool b₂) (hb₃ : ty₃.typeOf = .bool b₃)
    (htp : typeOfIf (tyc, cc) (.ok (ty₂, c₂)) (.ok (ty₃, c₃)) = .ok (typ, c')) :
    ∃ t, compilePred (.ite x₁ x₂ x₃) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType typ.typeOf) := by
  have ⟨hwfc, _, _⟩ := compilePred_wf hwε hitw hitty hokc
  have ⟨hwf₂, _, _⟩ := compilePred_wf hwε hitw hitty hok₂
  have ⟨hwf₃, _, _⟩ := compilePred_wf hwε hitw hitty hok₃
  rw [hbc, TermType.ofType] at htyc
  rw [hb₂, TermType.ofType] at hty₂
  rw [hb₃, TermType.ofType] at hty₃
  have ⟨t, hci, hcty⟩ := compileIf_bool_ok hwfc hwf₂ hwf₃ htyc hty₂ hty₃
  obtain ⟨b, htyp⟩ := typeOfIf_bool_result hbc hb₂ hb₃ htp
  refine ⟨t, by simp only [compilePred, hokc, hok₂, hok₃, Except.bind_ok, hci], ?_⟩
  rw [hcty, htyp, TermType.ofType]

end Cedar.Thm
