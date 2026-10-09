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
import all Cedar.SymCC.Compiler -- proving things about internals of the compiler
import Cedar.Thm.SymCC.Compiler.Basic
public import Cedar.Thm.SymCC.Compiler.ExtHasAttrRec
import all Cedar.Thm.SymCC.Compiler.Invert -- we require some lemmas from Compiler.Invert that are about private compiler internals
public import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.TypeOf
import Cedar.Thm.SymCC.Term.WF
import all Cedar.Thm.SymCC.Compiler.SetAllWF
import all Cedar.Thm.SymCC.Compiler.CompilePredWF

/-!
This file proves that both `compile` and `evaluate` preserve well-formedness.
--/

-- We're disabling the linter on this file because it erroneously claims
-- that a used variable is unused in Lean 4.19.
-- TODO: Remove this option when the linter is fixed.
set_option linter.unusedVariables false

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

---------- Compile is well-formed ----------

private def CompileWF (x : Expr)  : Prop :=
  ∀ {εnv : SymEnv} {t : Term},
    εnv.WellFormedFor x →
    compile x εnv = .ok t →
    (t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty)

private theorem typeOf_term_some_is_option {t : Term} :
  ∃ ty, Term.typeOf (Term.some t) = TermType.option ty
:= by
  exists t.typeOf
  simp

private theorem compile_lit_wf {p: Prim} {εnv : SymEnv} {t : Term}
  (hok : compile (Expr.lit p) εnv = Except.ok t) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  rw [compile.eq_def] at hok
  simp only [compilePrim] at hok
  cases p <;>
  simp only [Except.ok.injEq, someOf] at * <;>
  first | subst hok | skip
  case bool =>
    simp only [and_self, typeOf_term_some_is_option, Term.WellFormed.some_wf wf_bool]
  case int =>
    simp only [and_self, typeOf_term_some_is_option, Term.WellFormed.some_wf wf_bv]
  case string =>
    simp only [and_self, typeOf_term_some_is_option, Term.WellFormed.some_wf (Term.WellFormed.prim_wf TermPrim.WellFormed.string_wf)]
  case entityUID =>
    split at hok <;>
    simp only [Except.ok.injEq, reduceCtorEq] at hok
    rename_i h
    subst hok
    simp only [typeOf_term_some_is_option, and_true]
    exact Term.WellFormed.some_wf (Term.WellFormed.prim_wf (TermPrim.WellFormed.entity_wf h))

private theorem compile_var_wf {v : Var} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.var v))
  (hok : compile (Expr.var v) εnv = Except.ok t) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  simp [SymEnv.WellFormedFor, SymEnv.WellFormed, SymRequest.WellFormed] at hwf
  replace hwf := hwf.left.left
  rw [compile.eq_def] at hok
  simp only [compileVar] at hok
  split at hok <;>
  split at hok <;>
  simp only [Except.ok.injEq, someOf, reduceCtorEq] at hok <;>
  subst hok <;>
  rename_i h <;>
  simp only [typeOf_term_some_is_option, and_true] <;>
  apply Term.WellFormed.some_wf <;>
  simp only [hwf]

private theorem compile_ite_wf {x₁ x₂ x₃: Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.ite x₁ x₂ x₃))
  (hok : compile (Expr.ite x₁ x₂ x₃) εnv = Except.ok t)
  (ih₁ : CompileWF x₁)
  (ih₂ : CompileWF x₂)
  (ih₃ : CompileWF x₃) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwφ₁, hwφ₂, hwφ₃⟩ := wf_εnv_for_ite_implies hwf
  replace ⟨t₁, hr₁, hok⟩ := compile_ite_ok_implies hok
  split at hok
  case h_1 =>
    cases hr₂ : compile x₂ εnv <;>
    simp [hr₂] at hok
    subst hok
    exact ih₂ hwφ₂ hr₂
  case h_2 =>
    cases hr₃ : compile x₃ εnv <;>
    simp [hr₃] at hok
    subst hok
    exact ih₃ hwφ₃ hr₃
  case h_3 =>
    replace ⟨hb, t₂, t₃, hr₂, hr₃, ht, hok⟩ := hok
    subst hok
    replace ih₁ := (ih₁ hwφ₁ hr₁).left
    replace ih₂ := ih₂ hwφ₂ hr₂
    replace ih₃ := ih₃ hwφ₃ hr₃
    have h₁ := wf_option_get ih₁ hb
    have h₂ := wf_ite h₁.left ih₂.left ih₃.left h₁.right ht
    replace ⟨ty, ih₂⟩ := ih₂.right
    simp only [ih₂] at h₂
    have h₃ := wf_ifSome_option ih₁ h₂.left h₂.right
    simp only [h₃.left, true_and]
    exists ty
    exact h₃.right

private theorem compile_and_wf {x₁ x₂: Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.and x₁ x₂))
  (hok : compile (Expr.and x₁ x₂) εnv = Except.ok t)
  (ih₁ : CompileWF x₁)
  (ih₂ : CompileWF x₂) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_and_implies hwf
  replace ⟨t₁, hr₁, hok⟩ := compile_and_ok_implies hok
  split at hok
  case h_1 =>
    subst hok
    simp only [Term.WellFormed.some_wf wf_bool, true_and]
    exists .bool
    simp only [typeOf_term_some, typeOf_bool]
  case h_2 =>
    replace ⟨ht₁, t₂, hr₂, ht₂, hok⟩ := hok
    subst hok
    replace ih₁ := (ih₁ hwφ₁ hr₁).left
    replace ih₂ := (ih₂ hwφ₂ hr₂).left
    have h₁ := wf_option_get ih₁ ht₁
    have h₂ := @wf_ite εnv.entities
      (option.get t₁) t₂ (Term.some (Term.prim (TermPrim.bool false)))
      h₁.left ih₂ (Term.WellFormed.some_wf wf_bool)
      h₁.right (by simp only [ht₂, typeOf_term_some, typeOf_bool])
    rw [ht₂] at h₂
    have h₃ := wf_ifSome_option ih₁ h₂.left h₂.right
    simp only [h₃.left, true_and]
    exists .bool
    exact h₃.right

private theorem compile_or_wf {x₁ x₂: Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.or x₁ x₂))
  (hok : compile (Expr.or x₁ x₂) εnv = Except.ok t)
  (ih₁ : CompileWF x₁)
  (ih₂ : CompileWF x₂) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_or_implies hwf
  replace ⟨t₁, hr₁, hok⟩ := compile_or_ok_implies hok
  split at hok
  case h_1 =>
    subst hok
    simp only [Term.WellFormed.some_wf wf_bool, true_and]
    exists .bool
    simp only [typeOf_term_some, typeOf_bool]
  case h_2 =>
    replace ⟨ht₁, t₂, hr₂, ht₂, hok⟩ := hok
    subst hok
    replace ih₁ := (ih₁ hwφ₁ hr₁).left
    replace ih₂ := (ih₂ hwφ₂ hr₂).left
    have h₁ := wf_option_get ih₁ ht₁
    have h₂ := @wf_ite εnv.entities
      (option.get t₁) (Term.some (Term.prim (TermPrim.bool true))) t₂
      h₁.left (Term.WellFormed.some_wf wf_bool) ih₂ h₁.right
      (by simp only [typeOf_term_some, typeOf_bool, ← ht₂])
    simp only [typeOf_term_some, typeOf_bool] at h₂
    have h₃ := wf_ifSome_option ih₁ h₂.left h₂.right
    simp only [h₃.left, true_and]
    exists .bool
    exact h₃.right

public theorem compileAttrsOf_wf {t t₁: Term} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileAttrsOf t₁ εs = Except.ok t)  :
  t.WellFormed εs ∧
  ∃ rty, t.typeOf = .record rty ∧
  (t₁.typeOf = .record rty ∨
   ∃ ety fₐ,
    t₁.typeOf = .entity ety ∧ εs.attrs ety = .some fₐ ∧
    fₐ.outType = .record rty)
:= by
  replace hok := compileAttrsOf_ok_implies hok
  rcases hok with ⟨rty, hty, ht⟩ | ⟨ety, fₐ, hty, hf, ht⟩ <;>
  subst ht
  case inl =>
    simp only [hw₁, exists_and_left, true_and]
    exists rty
    simp only [hty, false_and, exists_const, or_false, and_self, reduceCtorEq]
  case inr =>
    have hwf := wf_εs_implies_wf_attrs hwε hf
    rw [← hty] at hwf
    have ha := wf_app hw₁ (by simp only [hwf.right.left]) hwf.left
    simp only [ha.left, exists_and_left, true_and]
    have ⟨rty, hrty⟩ := isCedarRecordType_implies_term_record_type hwf.right.right
    exists rty
    simp only [ha.right, hrty, true_and]
    apply Or.inr
    exists ety
    simp only [hty, true_and]
    exists fₐ

public theorem compileHasAttr_wf {t t₁: Term} {a : Attr} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileHasAttr t₁ a εs = Except.ok t)  :
  t.WellFormed εs ∧ t.typeOf = .option .bool
:= by
  replace ⟨t₂, rty, hok, ha, ha'⟩ := compileHasAttr_ok_implies hok
  split at ha' <;> subst ha'
  case h_1 heq =>
    have ⟨hw₂, rty, hty⟩ := compileAttrsOf_wf hwε hw₁ hok
    simp [hty] at ha ; subst ha
    replace ⟨h, hty⟩ := wf_isSome (wf_record_get hw₂ hty.left heq).left
    constructor
    · exact Term.WellFormed.some_wf h
    · simp only [typeOf_term_some, hty]
  case h_2 | h_3 =>
    simp only [typeOf_term_some, typeOf_bool, and_true]
    exact Term.WellFormed.some_wf wf_bool

public theorem compileAnd_preserves_wf {εs : SymEntities} {t₁ t : Term} {r₂ : SymCC.Result Term}
  (hw₁ : t₁.WellFormed εs)
  (hty₁ : t₁.typeOf = .option .bool)
  (hr₂ : ∀ t₂, r₂ = .ok t₂ → t₂.WellFormed εs ∧ t₂.typeOf = .option .bool)
  (hok : compileAnd t₁ r₂ = .ok t) :
  t.WellFormed εs ∧ t.typeOf = .option .bool
:= by
  simp only [compileAnd] at hok
  split at hok
  case h_1 =>
    simp only [Except.ok.injEq] at hok
    subst hok
    exact ⟨hw₁, hty₁⟩
  case h_2 heq _ =>
    simp only [bind, Except.bind] at hok
    split at hok
    · simp at hok
    · rename_i hr₂' t₂
      have ⟨hw₂, hty₂⟩ := hr₂ t₂ (by rfl)
      split at hok
      · simp only [Except.ok.injEq] at hok
        subst hok
        have hopt := wf_option_get hw₁ hty₁
        have hw₃ : (Term.some (Term.prim (TermPrim.bool false))).WellFormed εs :=
          Term.WellFormed.some_wf (wf_bool (b := false))
        have hite := wf_ite hopt.left hw₂ hw₃
          hopt.right (by simp only [hty₂, typeOf_term_some, typeOf_bool])
        rw [hty₂] at hite
        have h := wf_ifSome_option hw₁ hite.left hite.right
        exact ⟨h.left, h.right⟩
      · rename_i hne
        exact absurd hty₂ hne
  case h_3 =>
    rw [hty₁] at *
    contradiction

private theorem compile_hasAttr_wf {x₁ : Expr} {a : Attr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.hasAttr x₁ a))
  (hok : compile (Expr.hasAttr x₁ a) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have hwφ₁ := wf_εnv_for_hasAttr_implies hwf
  replace ⟨t₂, t₃, hok, ha, ht⟩ := compile_hasAttr_ok_implies hok
  subst ht
  replace ⟨ih₁, ty, hty⟩ := ih₁ hwφ₁ hok
  have hopt := wf_option_get ih₁ hty
  replace ha := compileHasAttr_wf hwφ₁.left.right hopt.left ha
  have h := wf_ifSome_option ih₁ ha.left ha.right
  simp only [h.left, true_and]
  exists .bool
  exact h.right

public theorem compileGetAttr_wf {t t₁: Term} {a : Attr} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileGetAttr t₁ a εs = Except.ok t)  :
  t.WellFormed εs ∧ ∃ tyₐ, t.typeOf = .option tyₐ
:= by
  replace ⟨t₂, rty, hok, ha, tyₐ, hf, ha'⟩ := compileGetAttr_ok_implies hok
  have ⟨hw₂, rty, hty⟩ := compileAttrsOf_wf hwε hw₁ hok
  simp [hty] at ha ; subst ha
  replace ⟨hwf, hty⟩ := wf_record_get hw₂ hty.left hf
  split at ha' <;> subst ha'
  case h_1 tyₐ =>
    constructor
    · exact hwf
    · exists tyₐ
  case h_2 tyₐ =>
    simp only [typeOf_term_some, TermType.option.injEq, exists_eq', and_true]
    exact Term.WellFormed.some_wf hwf

private theorem compile_getAttr_wf {x₁ : Expr} {a : Attr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.getAttr x₁ a))
  (hok : compile (Expr.getAttr x₁ a) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have hwφ₁ := wf_εnv_for_getAttr_implies hwf
  replace ⟨t₂, t₃, hok, ha, ht⟩ := compile_getAttr_ok_implies hok
  subst ht
  replace ⟨ih₁, ty, hty⟩ := ih₁ hwφ₁ hok
  have hopt := wf_option_get ih₁ hty
  replace ⟨ha, tyₐ, ha'⟩ := compileGetAttr_wf hwφ₁.left.right hopt.left ha
  have h := wf_ifSome_option ih₁ ha ha'
  simp only [h.left, true_and]
  exists tyₐ
  exact h.right

public theorem compileExtHasAttrRec_wf {t₁ : Term} {attrs : List Attr} {εs : SymEntities} {t : Term}
  (hwε : εs.WellFormed)
  (hw₁ : t₁.WellFormed εs) (hty₁ : ∃ ty, t₁.typeOf = .option ty)
  (hok : compileExtHasAttrRec t₁ attrs εs = .ok t) :
  t.WellFormed εs ∧ t.typeOf = .option .bool := by
  induction attrs generalizing t₁ t with
  | nil =>
    simp [compileExtHasAttrRec, pure, Except.pure] at hok
    rw [← hok]
    exact ⟨Term.WellFormed.some_wf wf_bool, by simp [typeOf_bool]⟩
  | cons a rest ih =>
    cases rest with
    | nil =>
      -- Single attr case: ifSome t₁ (compileHasAttr ...)
      simp only [compileExtHasAttrRec, bind, Except.bind] at hok
      split at hok
      case h_1 => simp at hok
      case h_2 t_ha hok_ha =>
      simp only [Except.ok.injEq] at hok; subst hok
      have hwo := wf_option_get hw₁ hty₁.choose_spec
      have hwha := compileHasAttr_wf hwε hwo.left hok_ha
      have h := wf_ifSome_option hw₁ hwha.left hwha.right
      exact ⟨h.left, h.right⟩
    | cons b rest' =>
      -- Multi attr case
      simp only [compileExtHasAttrRec, bind, Except.bind] at hok
      split at hok
      case h_1 => simp at hok
      case h_2 t_ha hok_ha =>
      split at hok
      case h_1 =>
        simp only [pure, Except.pure, Except.ok.injEq] at hok
        subst t
        have hwo := wf_option_get hw₁ hty₁.choose_spec
        have hwha := compileHasAttr_wf hwε hwo.left hok_ha
        exact wf_ifSome_option hw₁ hwha.left hwha.right
      case h_2 t_ga hok_ga =>
      split at hok
      case h_1 =>
        simp only [pure, Except.pure, Except.ok.injEq] at hok
        subst t
        have hwo := wf_option_get hw₁ hty₁.choose_spec
        have hwha := compileHasAttr_wf hwε hwo.left hok_ha
        exact wf_ifSome_option hw₁ hwha.left hwha.right
      case h_2 => simp at hok
      case h_3 =>
        rename_i t_ga hga
        have hwo := wf_option_get hw₁ hty₁.choose_spec
        have hwha := compileHasAttr_wf hwε hwo.left hok_ha
        have hwtHas := wf_ifSome_option hw₁ hwha.left hwha.right
        have ⟨hwga, tyga, htyga⟩ := compileGetAttr_wf hwε hwo.left hga
        have hwtNext := wf_ifSome_option hw₁ hwga htyga
        simp_do_let (compileExtHasAttrRec (ifSome t₁ t_ga) (b :: rest') εs) at hok
        rename_i t_rest hrest
        have ⟨hwrest, htyrest⟩ := ih hwtNext.left ⟨tyga, hwtNext.right⟩ hrest
        exact compileAnd_preserves_wf hwtHas.left hwtHas.right
          (fun t₂ h => by
            simp only [Except.ok.injEq] at h
            subst h
            exact ⟨hwrest, htyrest⟩)
          hok

private theorem compile_extHasAttr_wf' {x₁ : Expr} {a : Attr} {l : List Attr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.extHasAttr x₁ a l))
  (hok : compile (Expr.extHasAttr x₁ a l) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ t.typeOf = .option .bool
:= by
  have hwφ₁ := wf_εnv_for_extHasAttr_implies hwf
  rw [compile.eq_def] at hok
  simp only at hok
  simp_do_let (compile x₁ εnv) at hok
  rename_i t₁ hok₁
  have ⟨hwt₁, ty₁, hty₁⟩ := ih₁ hwφ₁ hok₁
  rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
  exact compileExtHasAttrRec_wf hwφ₁.left.right hwt₁ ⟨ty₁, hty₁⟩ hok

private theorem compile_extHasAttr_wf {x₁ : Expr} {a : Attr} {l : List Attr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.extHasAttr x₁ a l))
  (hok : compile (Expr.extHasAttr x₁ a l) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨h₁, h₂⟩ := compile_extHasAttr_wf' hwf hok ih₁
  exact ⟨h₁, .bool, h₂⟩

public theorem compileApp₁_wf_types {op₁ : UnaryOp} {t t₁: Term} {εs : SymEntities}
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileApp₁ op₁ t₁ = Except.ok t)  :
  t.WellFormed εs ∧
  match op₁ with
  | .neg => t.typeOf = .option (.bitvec 64)
  | _    => t.typeOf = .option .bool
:= by
  replace hok := compileApp₁_ok_implies hok
  split at hok <;> simp only
  case h_1 =>
    have hwf := wf_not hw₁ hok.left
    simp only [hok.right, typeOf_term_some, hwf.right, and_true]
    exact Term.WellFormed.some_wf hwf.left
  case h_2 =>
    have hwf₁ := wf_bvnego hw₁ hok.left
    have hwf₂ := wf_bvneg hw₁ hok.left
    have hwf₃ := wf_ifFalse hwf₁.left hwf₂.left hwf₁.right
    rw [hwf₂.right] at hwf₃
    simp only [hok.right, hwf₃, and_self]
  case h_3 p _ =>
    have hwf := @wf_string_like εs t₁ p hw₁ hok.left
    simp only [hok.right, typeOf_term_some, hwf.right, and_true]
    exact Term.WellFormed.some_wf hwf.left
  case h_4 =>
    replace ⟨_, hok⟩ := hok
    simp only [hok.right, typeOf_term_some, typeOf_bool, and_true]
    exact Term.WellFormed.some_wf wf_bool
  case h_5 =>
    replace ⟨⟨_, hty⟩, hok⟩ := hok
    have hwf := wf_set_isEmpty hw₁ hty
    simp only [hok, typeOf_term_some, hwf.right, and_true]
    exact Term.WellFormed.some_wf hwf.left

public theorem compileApp₁_wf {op₁ : UnaryOp} {t t₁: Term} {εs : SymEntities}
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileApp₁ op₁ t₁ = Except.ok t)  :
  t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwf, hty⟩ := compileApp₁_wf_types hw₁ hok
  simp only [hwf, true_and]
  split at hty <;>
  simp only [hty, TermType.option.injEq, exists_eq']

private theorem compile_unaryApp_wf {op₁ : UnaryOp} {x₁ : Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.unaryApp op₁ x₁))
  (hok : compile (Expr.unaryApp op₁ x₁) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have hwφ₁ := wf_εnv_for_unaryApp_implies hwf
  replace ⟨t₂, t₃, hok, ha, ht⟩ := compile_unaryApp_ok_implies hok
  subst ht
  replace ⟨ih₁, ty, hty⟩ := ih₁ hwφ₁ hok
  have hopt := wf_option_get ih₁ hty
  replace ⟨ha, _, ha'⟩ := compileApp₁_wf hopt.left ha
  have h := wf_ifSome_option ih₁ ha ha'
  simp only [h, TermType.option.injEq, exists_eq', and_self]

public theorem compileInₑ.isEq_wf {t₁ t₂ : Term} {εs : SymEntities}
  (hw₁  : Term.WellFormed εs t₁)
  (hw₂  : Term.WellFormed εs t₂) :
  (SymCC.compileInₑ.isEq t₁ t₂).WellFormed εs ∧ (SymCC.compileInₑ.isEq t₁ t₂).typeOf = .bool
:= by
  rw [SymCC.compileInₑ.isEq.eq_def]
  split
  · rename_i heq
    exact wf_eq hw₁ hw₂ heq
  · exact And.intro wf_bool typeOf_bool

public theorem compileInₑ.isIn_wf {t₁ t₂ : Term} {ancs? : Option UnaryFunction} {ety₁ ety₂ : EntityType} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : Term.WellFormed εs t₁)
  (hty₁ : t₁.typeOf = .entity ety₁)
  (hw₂  : Term.WellFormed εs t₂)
  (hty₂ : t₂.typeOf = .entity ety₂)
  (ha   : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) :
  (SymCC.compileInₑ.isIn t₁ t₂ ancs?).WellFormed εs ∧ (SymCC.compileInₑ.isIn t₁ t₂ ancs?).typeOf = .bool
:= by
  rw [SymCC.compileInₑ.isIn.eq_def]
  split
  · rename_i fₐ
    rw [eq_comm] at ha
    replace hwε := wf_εs_implies_wf_ancs hwε ha
    rw [eq_comm, ← hty₁] at hwε
    have happ := wf_app hw₁ hwε.right.left hwε.left
    rw [hwε.right.right, ← hty₂] at happ
    exact wf_set_member hw₂ happ.left happ.right
  · exact And.intro wf_bool typeOf_bool

public theorem compileInₑ_wf {t₁ t₂ : Term} {ancs? : Option UnaryFunction} {ety₁ ety₂ : EntityType} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : Term.WellFormed εs t₁)
  (hty₁ : t₁.typeOf = .entity ety₁)
  (hw₂  : Term.WellFormed εs t₂)
  (hty₂ : t₂.typeOf = .entity ety₂)
  (ha   : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) :
  (SymCC.compileInₑ t₁ t₂ ancs?).WellFormed εs ∧ (SymCC.compileInₑ t₁ t₂ ancs?).typeOf = .bool
:= by
  have heq := compileInₑ.isEq_wf hw₁ hw₂
  have hin := compileInₑ.isIn_wf hwε hw₁ hty₁ hw₂ hty₂ ha
  rw [compileInₑ_def, compileInₑ.isEq_def, compileInₑ.isIn_def]
  exact wf_or heq.left hin.left heq.right hin.right

public theorem compileInₛ.isIn₁_wf {t ts : Term} {εs : SymEntities}
  (hw₁  : Term.WellFormed εs t)
  (hw₂  : Term.WellFormed εs ts) :
  (SymCC.compileInₛ.isIn₁ t ts).WellFormed εs ∧ (SymCC.compileInₛ.isIn₁ t ts).typeOf = .bool
:= by
  rw [SymCC.compileInₛ.isIn₁.eq_def]
  split
  · rename_i heq
    exact wf_set_member hw₁ hw₂ heq
  · exact And.intro wf_bool typeOf_bool

public theorem compileInₛ.isIn₂_wf {t ts : Term} {ancs? : Option UnaryFunction} {ety₁ ety₂ : EntityType} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : Term.WellFormed εs t)
  (hty₁ : t.typeOf = .entity ety₁)
  (hw₂  : Term.WellFormed εs ts)
  (hty₂ : ts.typeOf = .set (.entity ety₂))
  (ha   : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) :
  (SymCC.compileInₛ.isIn₂ t ts ancs?).WellFormed εs ∧ (SymCC.compileInₛ.isIn₂ t ts ancs?).typeOf = .bool
:= by
  rw [SymCC.compileInₛ.isIn₂.eq_def]
  split
  · rename_i fₐ
    rw [eq_comm] at ha
    replace hwε := wf_εs_implies_wf_ancs hwε ha
    rw [eq_comm, ← hty₁] at hwε
    have happ := wf_app hw₁ hwε.right.left hwε.left
    rw [hwε.right.right] at happ
    exact wf_set_intersects hw₂ happ.left hty₂ happ.right
  · exact And.intro wf_bool typeOf_bool

public theorem compileInₛ_wf {t ts : Term} {ancs? : Option UnaryFunction} {ety₁ ety₂ : EntityType} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : Term.WellFormed εs t)
  (hty₁ : t.typeOf = .entity ety₁)
  (hw₂  : Term.WellFormed εs ts)
  (hty₂ : ts.typeOf = .set (.entity ety₂))
  (ha   : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) :
  (SymCC.compileInₛ t ts ancs?).WellFormed εs ∧ (SymCC.compileInₛ t ts ancs?).typeOf = .bool
:= by
  have hin₁ := compileInₛ.isIn₁_wf hw₁ hw₂
  have hin₂ := compileInₛ.isIn₂_wf hwε hw₁ hty₁ hw₂ hty₂ ha
  rw [compileInₛ_def, compileInₛ.isIn₁_def, compileInₛ.isIn₂_def]
  exact wf_or hin₁.left hin₂.left hin₁.right hin₂.right

public theorem compileApp₂_wf_types {op₂ : BinaryOp} {t t₁ t₂: Term} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hw₂ : Term.WellFormed εs t₂)
  (hok : compileApp₂ op₂ t₁ t₂ εs = Except.ok t)  :
  t.WellFormed εs ∧
  match op₂ with
  | .add | .sub | .mul => t.typeOf = .option (.bitvec 64)
  | .getTag            => ∃ ety τs, t₁.typeOf = .entity ety ∧ εs.tags ety = some (some τs) ∧ t.typeOf = τs.vals.outType.option
  | _                  => t.typeOf = .option .bool
:= by
  cases op₂ <;> simp only
  case eq =>
    have ht := compileApp₂_eq_ok_implies hok
    rcases ht with ⟨hty, ht⟩ | ⟨_, ht⟩ <;>
    simp only [ht, typeOf_term_some]
    · replace ⟨hwf, hty⟩ := wf_eq hw₁ hw₂ (reducibleEq_ok_true_implies hty)
      simp only [Term.WellFormed.some_wf hwf, hty, and_self]
    · simp only [Term.WellFormed.some_wf wf_bool, typeOf_bool, and_self]
  case mem =>
    replace ⟨ety₁, ety₂, hty₁, hok⟩ := compileApp₂_mem_ok_implies hok
    rcases hok with ⟨hty₂, ht⟩ | ⟨hty₂, ht⟩ <;>
    simp only [ht, typeOf_term_some, TermType.option.injEq]
    · have hwf := compileInₑ_wf hwε hw₁ hty₁ hw₂ hty₂ rfl
      exact And.intro (Term.WellFormed.some_wf hwf.left) hwf.right
    · have hwf := compileInₛ_wf hwε hw₁ hty₁ hw₂ hty₂ rfl
      exact And.intro (Term.WellFormed.some_wf hwf.left) hwf.right
  case less =>
    have ht := compileApp₂_less_ok_implies hok
    rcases ht with ⟨hty₁, hty₂, ht⟩ | ⟨hty₁, hty₂, ht⟩ | ⟨hty₁, hty₂, ht⟩
    case _ =>
      have ⟨hwf, hty⟩ := wf_bvslt hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
    case _ =>
      have ⟨hw₁, hty₁⟩ := wf_ext_duration_val hw₁ hty₁
      have ⟨hw₂, hty₂⟩ := wf_ext_duration_val hw₂ hty₂
      have ⟨hwf, hty⟩ := wf_bvslt hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
    case _ =>
      have ⟨hw₁, hty₁⟩ := wf_ext_datetime_val hw₁ hty₁
      have ⟨hw₂, hty₂⟩ := wf_ext_datetime_val hw₂ hty₂
      have ⟨hwf, hty⟩ := wf_bvslt hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case lessEq =>
    have ht := compileApp₂_lessEq_ok_implies hok
    rcases ht with ⟨hty₁, hty₂, ht⟩ | ⟨hty₁, hty₂, ht⟩ | ⟨hty₁, hty₂, ht⟩
    case _ =>
      have ⟨hwf, hty⟩ := wf_bvsle hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
    case _ =>
      have ⟨hw₁, hty₁⟩ := wf_ext_duration_val hw₁ hty₁
      have ⟨hw₂, hty₂⟩ := wf_ext_duration_val hw₂ hty₂
      have ⟨hwf, hty⟩ := wf_bvsle hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
    case _ =>
      have ⟨hw₁, hty₁⟩ := wf_ext_datetime_val hw₁ hty₁
      have ⟨hw₂, hty₂⟩ := wf_ext_datetime_val hw₂ hty₂
      have ⟨hwf, hty⟩ := wf_bvsle hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case add =>
    have ⟨hty₁, hty₂, ht⟩ := compileApp₂_add_ok_implies hok
    have hwt := wf_bvadd hw₁ hw₂ hty₁ hty₂
    have hwg := wf_bvsaddo hw₁ hw₂ hty₁ hty₂
    simp only [ht, wf_ifFalse hwg.left hwt.left hwg.right, hwt, and_self]
  case sub =>
    have ⟨hty₁, hty₂, ht⟩ := compileApp₂_sub_ok_implies hok
    have hwt := wf_bvsub hw₁ hw₂ hty₁ hty₂
    have hwg := wf_bvssubo hw₁ hw₂ hty₁ hty₂
    simp only [ht, wf_ifFalse hwg.left hwt.left hwg.right, hwt, and_self]
  case mul =>
    have ⟨hty₁, hty₂, ht⟩ := compileApp₂_mul_ok_implies hok
    have hwt := wf_bvmul hw₁ hw₂ hty₁ hty₂
    have hwg := wf_bvsmulo hw₁ hw₂ hty₁ hty₂
    simp only [ht, wf_ifFalse hwg.left hwt.left hwg.right, hwt, and_self]
  case contains =>
    have ⟨hty, ht⟩ := compileApp₂_contains_ok_implies hok
    replace ⟨hwf, hty⟩ := wf_set_member hw₂ hw₁ hty
    simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case containsAll =>
    have ⟨_, hty₁, hty₂, ht⟩ := compileApp₂_containsAll_ok_implies hok
    have ⟨hwf, hty⟩ := wf_set_subset hw₂ hw₁ hty₂ hty₁
    simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case containsAny =>
    have ⟨_, hty₁, hty₂, ht⟩ := compileApp₂_containsAny_ok_implies hok
    have ⟨hwf, hty⟩ := wf_set_intersects hw₁ hw₂ hty₁ hty₂
    simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case hasTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_hasTag_ok_implies hok
    replace hok := compileHasTag_ok_implies hok
    rcases hok with ⟨_, hok⟩ | ⟨τs, hτs, hok⟩ <;> subst hok
    · simp only [Term.WellFormed.some_wf wf_bool, typeOf_term_some, typeOf_bool, and_self]
    · have hwτ := wf_tags_hasTag (wf_εs_implies_wf_tags hwε hτs) hw₁ hw₂ hty₁ hty₂
      simp only [Term.WellFormed.some_wf hwτ.left, typeOf_term_some, hwτ.right, and_self]
  case getTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_getTag_ok_implies hok
    replace ⟨τs, hτs, hok⟩ := compileGetTag_ok_implies hok
    subst hok
    have hwτ := wf_tags_getTag (wf_εs_implies_wf_tags hwε hτs) hw₁ hw₂ hty₁ hty₂
    simp only [hwτ, hty₁, TermType.prim.injEq, TermPrimType.entity.injEq, TermType.option.injEq,
      exists_and_left, exists_eq_left', hτs, Option.some.injEq, and_self]

public theorem compileApp₂_wf {op₂ : BinaryOp} {t t₁ t₂: Term} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hw₂ : Term.WellFormed εs t₂)
  (hok : compileApp₂ op₂ t₁ t₂ εs = Except.ok t)  :
  t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwf, hty⟩ := compileApp₂_wf_types hwε hw₁ hw₂ hok
  simp only [hwf, true_and]
  split at hty
  any_goals (simp only [hty, TermType.option.injEq, exists_eq'])
  replace ⟨_, _, hty⟩ := hty
  simp only [hty, TermType.option.injEq, exists_eq']

private theorem compile_binaryApp_wf {op₂ : BinaryOp} {x₁ x₂ : Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.binaryApp op₂ x₁ x₂))
  (hok : compile (Expr.binaryApp op₂ x₁ x₂) εnv = Except.ok t)
  (ih₁ : CompileWF x₁)
  (ih₂ : CompileWF x₂) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_binaryApp_implies hwf
  replace ⟨t₁, t₂, t₃, hok₁, hok₂, hok, ht⟩ := compile_binaryApp_ok_implies hok
  subst ht
  replace ⟨ih₁, ty₁, hty₁⟩ := ih₁ hwφ₁ hok₁
  replace ⟨ih₂, ty₂, hty₂⟩ := ih₂ hwφ₂ hok₂
  have hopt₁ := wf_option_get ih₁ hty₁
  have hopt₂ := wf_option_get ih₂ hty₂
  have ⟨ih₃, ty, hty₃⟩ := compileApp₂_wf hwf.left.right hopt₁.left hopt₂.left hok
  have h := wf_ifSome_option ih₂ ih₃ hty₃
  replace h := wf_ifSome_option ih₁ h.left h.right
  simp only [h, TermType.option.injEq, exists_eq', and_self]

private theorem compile_set_wf {xs : List Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.set xs))
  (hok : compile (Expr.set xs) εnv = Except.ok t)
  (ih  : ∀ x ∈ xs, CompileWF x) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  replace hwf := wf_εnv_for_set_implies hwf
  replace ⟨ts, heq, hok⟩ := compile_set_ok_implies hok
  have ⟨ty, hd, tl, hcons, hty, ht⟩ := compileSet_ok_implies hok
  subst ht
  replace heq := List.forall₂_implies_all_right heq
  replace hwf : ∀ t ∈ ts, t.WellFormed εnv.entities := by
    intro t h
    replace ⟨x, heq⟩ := heq t h
    simp only [ih x heq.left (hwf x heq.left) heq.right]
  have hwo := wf_option_get_mem_of_type hwf hty
  have hwty := typeOf_option_wf_terms_is_wf hcons hwf hty
  have hwfs := wf_some_setOf_map hwo hwty
  have hwa := wf_ifAllSome hwf hwfs.left hwfs.right
  simp only [hwa, TermType.option.injEq, exists_eq', and_self]

private theorem compile_record_wf {axs : List (Attr × Expr)} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.record axs))
  (hok : compile (Expr.record axs) εnv = Except.ok t)
  (ih  : ∀ (aᵢ : Attr) (xᵢ : Expr), (aᵢ, xᵢ) ∈ axs → CompileWF xᵢ) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  replace hwf := wf_εnv_for_record_implies hwf
  replace ⟨ats, heq, hok⟩ := compile_record_ok_implies hok
  subst hok
  replace heq := List.forall₂_implies_all_right heq
  simp only [compileRecord]
  replace ih : ∀ a t, (a, t) ∈ ats → t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty := by
    intro a t h
    replace ⟨(_, x), h', ha, heq⟩ := heq (a, t) h
    simp only at ha heq
    rw [eq_comm] at ha ; subst ha
    simp only [ih a x h' (hwf (a, x) h') heq, and_self]
  replace hwf := wf_prods_option_implies_wf_prods ih
  have hwg := wf_prods_implies_wf_map_snd hwf
  have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd ih)
  have hwa := wf_ifAllSome hwg hwo hty
  simp only [someOf, hwa, TermType.option.injEq, exists_eq', and_self]

local macro "simp_compileCall₁'_wf" hwf:ident hok:ident compile_call_thm:ident wf_call_thm:ident : tactic => do
  `(tactic| (
    have ⟨t₁, hts, hty, ht⟩ := $compile_call_thm $hok
    subst hts ht
    replace $hwf := wf_arg' $hwf
    have h₁ := $wf_call_thm (wf_option_get $hwf hty)
    exact wf_ifSome_option $hwf h₁.left h₁.right
  ))

local macro "simp_compileCall₁_wf" hwf:ident hok:ident compile_call_thm:ident wf_call_thm:ident : tactic => do
  `(tactic| (
    have ⟨t₁, hts, hty, ht⟩ := $compile_call_thm $hok
    subst hts ht
    replace $hwf := wf_arg' $hwf
    have h₁ := $wf_call_thm (wf_option_get $hwf hty)
    have h₂ := Term.WellFormed.some_wf h₁.left
    have h₃ := wf_ifSome_option $hwf h₂ typeOf_term_some
    rw [h₁.right] at h₃
    exact h₃
  ))

local macro "simp_compileCall₂'_wf" hwf:ident hok:ident compile_call_thm:ident wf_call_thm:ident : tactic => do
 `(tactic| (
    have ⟨t₁, t₂, hts, hty₁, hty₂, ht⟩ := $compile_call_thm $hok
    subst hts ht
    replace $hwf := wf_args' $hwf
    have h₁ := wf_option_get ($hwf).left hty₁
    have h₂ := wf_option_get ($hwf).right hty₂
    have h₃ := $wf_call_thm h₁ h₂
    have h₄ := wf_ifSome_option ($hwf).right h₃.left h₃.right
    exact wf_ifSome_option ($hwf).left h₄.left h₄.right
  ))

local macro "simp_compileCall₂_wf" hwf:ident hok:ident compile_call_thm:ident wf_call_thm:ident : tactic => do
 `(tactic| (
    have ⟨t₁, t₂, hts, hty₁, hty₂, ht⟩ := $compile_call_thm $hok
    subst hts ht
    replace $hwf := wf_args' $hwf
    have h₁ := wf_option_get ($hwf).left hty₁
    have h₂ := wf_option_get ($hwf).right hty₂
    have h₃ := $wf_call_thm h₁ h₂
    have h₄ := Term.WellFormed.some_wf h₃.left
    have h₅ := wf_ifSome_option ($hwf).right h₄ typeOf_term_some
    rw [h₃.right] at h₅
    exact wf_ifSome_option ($hwf).left h₅.left h₅.right
  ))

local macro "simp_compileCall₀_wf" hok:ident compile_call_thm:ident typeOf_term_ext_thm:ident : tactic => do
`(tactic| (
    replace ⟨_, _, _, _, $hok⟩ := $compile_call_thm $hok
    simp only [$hok:ident, typeOf_term_some, $typeOf_term_ext_thm:ident, and_true]
    exact Term.WellFormed.some_wf (Term.WellFormed.prim_wf TermPrim.WellFormed.ext_wf)
))

public theorem compileCall_wf_types {f : ExtFun} {ts : List Term} {εs : SymEntities} {t : Term}
  (hwf : ∀ t ∈ ts, Term.WellFormed εs t)
  (hok : compileCall f ts = Except.ok t)  :
  t.WellFormed εs ∧
  match f with
  | .decimal         => t.typeOf = .option (.ext .decimal)
  | .ip              => t.typeOf = .option (.ext .ipAddr)
  | .datetime
  | .offset
  | .toDate          => t.typeOf = .option (.ext .datetime)
  | .toTime
  | .duration
  | .durationSince   => t.typeOf = .option (.ext .duration)
  | .toMilliseconds
  | .toSeconds
  | .toMinutes
  | .toHours
  | .toDays          => t.typeOf = .option (.bitvec 64)
  | _                => t.typeOf = .option .bool
:= by
  cases f <;> simp only
  case decimal =>
    simp_compileCall₀_wf hok compileCall_decimal_ok_implies typeOf_term_prim_ext_decimal
  case lessThan =>
    simp_compileCall₂_wf hwf hok compileCall_decimal_lessThan_ok_implies wf_decimal_lessThan
  case lessThanOrEqual =>
    simp_compileCall₂_wf hwf hok compileCall_decimal_lessThanOrEqual_ok_implies wf_decimal_lessThanOrEqual
  case greaterThan =>
    simp_compileCall₂_wf hwf hok compileCall_decimal_greaterThan_ok_implies wf_decimal_greaterThan
  case greaterThanOrEqual =>
    simp_compileCall₂_wf hwf hok compileCall_decimal_greaterThanOrEqual_ok_implies wf_decimal_greaterThanOrEqual
  case ip =>
    simp_compileCall₀_wf hok compileCall_ipAddr_ok_implies typeOf_term_prim_ext_ipaddr
  case isIpv4 =>
    simp_compileCall₁_wf hwf hok compileCall_ipAddr_isIpv4_ok_implies wf_ipaddr_isIpv4
  case isIpv6 =>
    simp_compileCall₁_wf hwf hok compileCall_ipAddr_isIpv6_ok_implies wf_ipaddr_isIpv6
  case isLoopback =>
    simp_compileCall₁_wf hwf hok compileCall_ipAddr_isLoopback_ok_implies wf_ipaddr_isLoopback
  case isMulticast =>
    simp_compileCall₁_wf hwf hok compileCall_ipAddr_isMulticast_ok_implies wf_ipaddr_isMulticast
  case isInRange =>
    simp_compileCall₂_wf hwf hok compileCall_ipAddr_isInRange_ok_implies wf_ipaddr_isInRange
  case datetime =>
    simp_compileCall₀_wf hok compileCall_datetime_ok_implies typeOf_term_prim_ext_datetime
  case duration =>
    simp_compileCall₀_wf hok compileCall_duration_ok_implies typeOf_term_prim_ext_duration
  case offset =>
    simp_compileCall₂'_wf hwf hok compileCall_datetime_offset_ok_implies wf_datetime_offset
  case durationSince =>
    simp_compileCall₂'_wf hwf hok compileCall_datetime_durationSince_ok_implies wf_datetime_durationSince
  case toDate =>
    simp_compileCall₁'_wf hwf hok compileCall_datetime_toDate_ok_implies wf_datetime_toDate
  case toTime =>
    simp_compileCall₁_wf hwf hok compileCall_datetime_toTime_ok_implies wf_datetime_toTime
  case toMilliseconds =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toMilliseconds_ok_implies wf_duration_toMilliseconds
  case toSeconds =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toSeconds_ok_implies wf_duration_toSeconds
  case toMinutes =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toMinutes_ok_implies wf_duration_toMinutes
  case toHours =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toHours_ok_implies wf_duration_toHours
  case toDays =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toDays_ok_implies wf_duration_toDays

public theorem compileCall_wf {f : ExtFun} {ts : List Term} {εs : SymEntities} {t : Term}
  (hwf : ∀ t ∈ ts, Term.WellFormed εs t)
  (hok : compileCall f ts = Except.ok t)  :
  t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty
:= by
  replace ⟨hwf, hty⟩ := compileCall_wf_types hwf hok
  simp only [hwf, true_and]
  split at hty <;> simp only [hty, TermType.option.injEq, exists_eq']

private theorem compile_call_wf {f : ExtFun} {xs : List Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.call f xs))
  (hok : compile (Expr.call f xs) εnv = Except.ok t)
  (ih  : ∀ x ∈ xs, CompileWF x) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  replace hwf := wf_εnv_for_call_implies hwf
  replace ⟨ts, heq, hok⟩ := compile_call_ok_implies hok
  apply compileCall_wf _ hok
  intro t ht
  replace ⟨x, hx, heq⟩ := List.forall₂_implies_all_right heq t ht
  simp only [@ih x hx εnv t (hwf x hx) heq]

public theorem compileIf_wf {εs : SymEntities} {t₁ t : Term} {r₂ r₃ : SymCC.Result Term}
  (hw₁ : t₁.WellFormed εs)
  (hr₂ : ∀ t₂, r₂ = .ok t₂ → t₂.WellFormed εs ∧ ∃ ty, t₂.typeOf = .option ty)
  (hr₃ : ∀ t₃, r₃ = .ok t₃ → t₃.WellFormed εs ∧ ∃ ty, t₃.typeOf = .option ty)
  (hok : compileIf t₁ r₂ r₃ = .ok t) : t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty := by
  rw [compileIf.eq_def] at hok
  split at hok
  · exact hr₂ t hok
  · exact hr₃ t hok
  · rename_i hguard
    cases he2 : r₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    cases he3 : r₃ <;> simp only [he3, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂ t₃
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    rename_i hteq
    have ⟨hw₂, ty₂, ht₂⟩ := hr₂ t₂ he2
    have ⟨hw₃, ty₃, ht₃⟩ := hr₃ t₃ he3
    have hg := wf_option_get hw₁ hguard
    have hite := wf_ite hg.left hw₂ hw₃ hg.right hteq
    have h := wf_ifSome_option hw₁ hite.left (by rw [hite.right]; exact ht₂)
    exact ⟨h.left, ty₂, h.right⟩
  · simp only [reduceCtorEq] at hok

public theorem compileOr_wf {εs : SymEntities} {t₁ t : Term} {r₂ : SymCC.Result Term}
  (hw₁ : t₁.WellFormed εs)
  (hr₂ : ∀ t₂, r₂ = .ok t₂ → t₂.WellFormed εs ∧ ∃ ty, t₂.typeOf = .option ty)
  (hok : compileOr t₁ r₂ = .ok t) : t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty := by
  rw [compileOr.eq_def] at hok
  split at hok
  · simp only [Except.ok.injEq] at hok; subst hok
    exact ⟨hw₁, .bool, by simp only [typeOf_term_some, typeOf_bool]⟩
  · rename_i hguard
    cases he2 : r₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    rename_i ht₂eq
    have ⟨hw₂, ty₂, ht₂⟩ := hr₂ t₂ he2
    have hg := wf_option_get hw₁ hguard
    have hite := wf_ite (t₂ := Term.some (Term.prim (TermPrim.bool true)))
      hg.left (Term.WellFormed.some_wf wf_bool) hw₂ hg.right
      (by simp only [typeOf_term_some, typeOf_bool, ← ht₂eq])
    simp only [typeOf_term_some, typeOf_bool] at hite
    have h := wf_ifSome_option hw₁ hite.left hite.right
    exact ⟨h.left, _, h.right⟩
  · simp only [reduceCtorEq] at hok

public theorem compileAnd_wf {εs : SymEntities} {t₁ t : Term} {r₂ : SymCC.Result Term}
  (hw₁ : t₁.WellFormed εs)
  (hr₂ : ∀ t₂, r₂ = .ok t₂ → t₂.WellFormed εs ∧ ∃ ty, t₂.typeOf = .option ty)
  (hok : compileAnd t₁ r₂ = .ok t) : t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty := by
  rw [compileAnd.eq_def] at hok
  split at hok
  · simp only [Except.ok.injEq] at hok; subst hok
    exact ⟨hw₁, .bool, by simp only [typeOf_term_some, typeOf_bool]⟩
  · rename_i hguard
    cases he2 : r₂ <;> simp only [he2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₂
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    rename_i ht₂eq
    have ⟨hw₂, ty₂, ht₂⟩ := hr₂ t₂ he2
    have hg := wf_option_get hw₁ hguard
    have hite := wf_ite (t₃ := Term.some (Term.prim (TermPrim.bool false)))
      hg.left hw₂ (Term.WellFormed.some_wf wf_bool) hg.right
      (by simp only [typeOf_term_some, typeOf_bool, ht₂eq])
    have h := wf_ifSome_option hw₁ hite.left (by rw [hite.right, ht₂eq])
    exact ⟨h.left, _, h.right⟩
  · simp only [reduceCtorEq] at hok

public theorem compileRecord_wf {εs : SymEntities} {ats : List (Attr × Term)}
  (ih : ∀ a t, (a, t) ∈ ats → t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty) :
  (compileRecord ats).WellFormed εs ∧ ∃ ty, (compileRecord ats).typeOf = .option ty := by
  simp only [compileRecord]
  have hwf := wf_prods_option_implies_wf_prods ih
  have hwg := wf_prods_implies_wf_map_snd hwf
  have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd ih)
  have hwa := wf_ifAllSome hwg hwo hty
  simp only [someOf, hwa, TermType.option.injEq, exists_eq', and_self]

public theorem compilePred_wf {p : PredExpr} {it r : Term} {εnv : SymEnv} {elemTy : TermType}
  (hwε : εnv.WellFormed) (hitw : it.WellFormed εnv.entities) (hitty : it.typeOf = .option elemTy)
  (hok : compilePred p it εnv = Except.ok r) : r.WellFormed εnv.entities ∧ ∃ ty, r.typeOf = .option ty := by
  match p with
  | .item =>
    simp only [compilePred, Except.ok.injEq] at hok; subst hok; exact ⟨hitw, elemTy, hitty⟩
  | .lit l =>
    simp only [compilePred, compilePrim] at hok
    cases l <;> simp only [Except.ok.injEq, someOf] at * <;> first | subst hok | skip
    · exact ⟨Term.WellFormed.some_wf wf_bool, typeOf_term_some_is_option⟩
    · exact ⟨Term.WellFormed.some_wf wf_bv, typeOf_term_some_is_option⟩
    · exact ⟨Term.WellFormed.some_wf (Term.WellFormed.prim_wf TermPrim.WellFormed.string_wf), typeOf_term_some_is_option⟩
    · split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
      rename_i h; subst hok
      exact ⟨Term.WellFormed.some_wf (Term.WellFormed.prim_wf (TermPrim.WellFormed.entity_wf h)), typeOf_term_some_is_option⟩
  | .var v =>
    simp only [compilePred, compileVar] at hok
    have hwf := hwε.left
    simp only [SymRequest.WellFormed] at hwf
    split at hok <;> split at hok <;> simp only [Except.ok.injEq, someOf, reduceCtorEq] at hok <;> subst hok <;>
      refine ⟨Term.WellFormed.some_wf ?_, typeOf_term_some_is_option⟩
    · exact hwf.left
    · exact hwf.right.right.right.right.left
    · exact hwf.right.right.right.right.right.right.right.right.left
    · exact hwf.right.right.right.right.right.right.right.right.right.right.right.right.left
  | .ite x₁ x₂ x₃ =>
    simp only [compilePred] at hok
    cases h1 : compilePred x₁ it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₁
    exact compileIf_wf (compilePred_wf hwε hitw hitty h1).left
      (fun t₂ he => compilePred_wf hwε hitw hitty he) (fun t₃ he => compilePred_wf hwε hitw hitty he) hok
  | .and x₁ x₂ =>
    simp only [compilePred] at hok
    cases h1 : compilePred x₁ it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₁
    exact compileAnd_wf (compilePred_wf hwε hitw hitty h1).left
      (fun t₂ he => compilePred_wf hwε hitw hitty he) hok
  | .or x₁ x₂ =>
    simp only [compilePred] at hok
    cases h1 : compilePred x₁ it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₁
    exact compileOr_wf (compilePred_wf hwε hitw hitty h1).left
      (fun t₂ he => compilePred_wf hwε hitw hitty he) hok
  | .unaryApp op₁ x₁ =>
    simp only [compilePred] at hok
    cases h1 : compilePred x₁ it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₁
    cases hA : compileApp₁ op₁ (option.get t₁) <;> simp only [hA, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    simp only [Except.ok.injEq] at hok; subst hok
    have ⟨ih1w, ty1, hty1⟩ := compilePred_wf hwε hitw hitty h1
    have hget := wf_option_get ih1w hty1
    have ⟨haw, tya, hat⟩ := compileApp₁_wf hget.left hA
    have h := wf_ifSome_option ih1w haw hat
    exact ⟨h.left, tya, h.right⟩
  | .binaryApp op₂ x₁ x₂ =>
    simp only [compilePred] at hok
    cases h1 : compilePred x₁ it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    cases h2 : compilePred x₂ it εnv <;> simp only [h2, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₁ t₂
    cases hA : compileApp₂ op₂ (option.get t₁) (option.get t₂) εnv.entities <;> simp only [hA, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    simp only [Except.ok.injEq] at hok; subst hok
    have ⟨ih1w, ty1, hty1⟩ := compilePred_wf hwε hitw hitty h1
    have ⟨ih2w, ty2, hty2⟩ := compilePred_wf hwε hitw hitty h2
    have hget1 := wf_option_get ih1w hty1
    have hget2 := wf_option_get ih2w hty2
    have ⟨haw, tya, hat⟩ := compileApp₂_wf hwε.right hget1.left hget2.left hA
    have hinner := wf_ifSome_option ih2w haw hat
    have h := wf_ifSome_option ih1w hinner.left hinner.right
    exact ⟨h.left, _, h.right⟩
  | .hasAttr x a =>
    simp only [compilePred] at hok
    cases h1 : compilePred x it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₁
    cases hH : compileHasAttr (option.get t₁) a εnv.entities <;> simp only [hH, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    simp only [Except.ok.injEq] at hok; subst hok
    have ⟨ih1w, ty1, hty1⟩ := compilePred_wf hwε hitw hitty h1
    have hget := wf_option_get ih1w hty1
    have ⟨haw, hat⟩ := compileHasAttr_wf hwε.right hget.left hH
    have h := wf_ifSome_option ih1w haw hat
    exact ⟨h.left, _, h.right⟩
  | .getAttr x a =>
    simp only [compilePred] at hok
    cases h1 : compilePred x it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₁
    cases hG : compileGetAttr (option.get t₁) a εnv.entities <;> simp only [hG, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    simp only [Except.ok.injEq] at hok; subst hok
    have ⟨ih1w, ty1, hty1⟩ := compilePred_wf hwε hitw hitty h1
    have hget := wf_option_get ih1w hty1
    have ⟨haw, tya, hat⟩ := compileGetAttr_wf hwε.right hget.left hG
    have h := wf_ifSome_option ih1w haw hat
    exact ⟨h.left, tya, h.right⟩
  | .extHasAttr x a ats =>
    simp only [compilePred] at hok
    cases h1 : compilePred x it εnv <;> simp only [h1, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
    rename_i t₁
    have ⟨ih1w, ty1, hty1⟩ := compilePred_wf hwε hitw hitty h1
    rw [compileExtHasAttr_eq_compileExtHasAttrRec] at hok
    have ⟨haw, hat⟩ := compileExtHasAttrRec_wf hwε.right ih1w ⟨ty1, hty1⟩ hok
    exact ⟨haw, _, hat⟩
  | .record axs =>
    simp only [compilePred] at hok
    simp_do_let (axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => do Except.ok (a₁, ← compilePred x₁ it εnv))) at hok
    rename_i ats hts
    simp only [List.mapM₂_eq_mapM λ (q : Attr × PredExpr) => do
        Except.ok (q.fst, ← compilePred q.snd it εnv),
      List.mapM_ok_iff_forall₂] at hts
    simp only [Except.ok.injEq] at hok; subst hok
    apply compileRecord_wf
    intro a t hmem
    have ⟨px, hpx, hp⟩ := List.forall₂_implies_all_right hts (a, t) hmem
    cases hxv : compilePred px.snd it εnv <;>
      simp only [hxv, Except.bind_err, Except.bind_ok, reduceCtorEq, Except.ok.injEq] at hp
    rename_i tv
    have hwv := compilePred_wf (p := px.snd) hwε hitw hitty hxv
    simp only [Prod.mk.injEq] at hp
    obtain ⟨_, rfl⟩ := hp
    exact hwv
  | .call xfn xs =>
    simp only [compilePred] at hok
    simp_do_let (xs.mapM₁ (λ ⟨x₁, _⟩ => compilePred x₁ it εnv)) at hok
    rename_i ts hts
    simp only [List.mapM₁_eq_mapM λ (q : PredExpr) => compilePred q it εnv,
      List.mapM_ok_iff_forall₂] at hts
    apply compileCall_wf _ hok
    intro t ht
    have ⟨px, hpx, hp⟩ := List.forall₂_implies_all_right hts t ht
    exact (compilePred_wf (p := px) hwε hitw hitty hp).left
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (have := List.sizeOf_snd_lt_sizeOf_list hpx; omega)
      | (have := List.sizeOf_lt_of_mem hpx; omega)

/-- Inner term of the compiler's literal-fold `.all` result (D-68): the `ite anyErr none (some conj)`
fold over Bool-option-typed `pts` is well-formed of type `.option .bool`. -/
public theorem compile_all_fold_inner_wf {εs : SymEntities} {pts : List Term}
  (hpts : ∀ pti ∈ pts, pti.WellFormed εs ∧ pti.typeOf = .option .bool) :
  (Factory.ite
        (pts.foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (pts.foldr (fun pti acc => Factory.and (option.get pti) acc) (true : Term)))).WellFormed εs ∧
  (Factory.ite
        (pts.foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (pts.foldr (fun pti acc => Factory.and (option.get pti) acc) (true : Term)))).typeOf = .option .bool := by
  -- conjunction (fold of `option.get pti`) is WF + bool
  have hconj := foldr_and_wf (εs := εs) (g := fun pti => option.get pti) pts (by
    intro pti hmem
    have ⟨hw, hty⟩ := hpts pti hmem
    exact wf_option_get hw hty)
  -- error disjunction (fold of `not (isSome pti)`) is WF + bool
  have hanyErr := foldr_or_wf (εs := εs) (g := fun pti => Factory.not (Factory.isSome pti)) pts (by
    intro pti hmem
    have hns := wf_isSome (hpts pti hmem).left
    exact wf_not hns.left hns.right)
  -- someOf conj
  have hsomew : (Factory.someOf (pts.foldr (fun pti acc => Factory.and (option.get pti) acc) (true : Term))).WellFormed εs :=
    Term.WellFormed.some_wf hconj.left
  have hsomety : (Factory.someOf (pts.foldr (fun pti acc => Factory.and (option.get pti) acc) (true : Term))).typeOf = .option .bool := by
    simp only [Factory.someOf, typeOf_term_some, hconj.right]
  -- noneOf .bool
  have hnonew : (Factory.noneOf .bool).WellFormed εs := Term.WellFormed.none_wf TermType.WellFormed.bool_wf
  have hnonety : (Factory.noneOf .bool).typeOf = .option .bool := by simp only [Factory.noneOf, typeOf_term_none]
  -- the inner ite
  have hite := wf_ite hanyErr.left hnonew hsomew hanyErr.right (by rw [hnonety, hsomety])
  rw [hnonety] at hite
  exact hite

/-- D-68: WF of the literal-fold result produced by the compiler's `.all` arm.
Each `pti ∈ pts` is a compiled per-element predicate whose `option.get` is
Bool-typed (the D-65 guard in the `mapM`); the fold builds a conjunction and an
error-disjunction, wrapped by `ite`/`ifSome`. -/
public theorem compile_all_fold_result_wf {εs : SymEntities} {t : Term} {ety : TermType} {pts : List Term}
  (htw : t.WellFormed εs) (htty : t.typeOf = .option (.set ety))
  (hpts : ∀ pti ∈ pts, pti.WellFormed εs ∧ pti.typeOf = .option .bool) :
  (Factory.ifSome t
      (Factory.ite
        (pts.foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (pts.foldr (fun pti acc => Factory.and (option.get pti) acc) (true : Term))))).WellFormed εs ∧
  (Factory.ifSome t
      (Factory.ite
        (pts.foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (pts.foldr (fun pti acc => Factory.and (option.get pti) acc) (true : Term))))).typeOf = .option .bool := by
  have hite := compile_all_fold_inner_wf hpts
  exact wf_ifSome_option htw hite.left hite.right

/-- Public twin of `compile_all_wf`'s symbolic sub-proof: the symbolic `.all` result term
(`ifSome t₁ (set.all (option.get t₁) (option.get pt) (not (isSome pt)))`) is well-formed of type
`.option .bool`, given a well-formed set-typed receiver and a Bool-typed compiled predicate. -/
public theorem compile_all_symbolic_inner_wf {p : PredExpr} {εnv : SymEnv} {t₁ pt : Term} {elemTy : TermType}
  (hwε : εnv.WellFormed)
  (hwt₁ : t₁.WellFormed εnv.entities) (hty₁ : t₁.typeOf = .option (.set elemTy))
  (hpt : compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv = Except.ok pt)
  (hpbool : (option.get pt).typeOf = .bool) :
  (Factory.set.all (option.get t₁) (option.get pt) (Factory.not (Factory.isSome pt))).WellFormed εnv.entities ∧
  (Factory.set.all (option.get t₁) (option.get pt) (Factory.not (Factory.isSome pt))).typeOf = .option .bool := by
  have hgt := wf_option_get hwt₁ hty₁
  have hel : TermType.WellFormed εnv.entities elemTy := by
    have hw := typeOf_wf_term_is_wf hgt.left
    rw [hgt.right] at hw
    cases hw with | set_wf h => exact h
  have hvarw : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).WellFormed εnv.entities :=
    Term.WellFormed.some_wf (Term.WellFormed.var_wf hel)
  have hvarty : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).typeOf = .option elemTy := by
    simp only [Factory.someOf, typeOf_term_some, typeOf_term_var, Factory.anyAllItVar]
  have hvarn : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).NoSetAll = true := by
    simp only [Factory.someOf, Term.NoSetAll]
  have hvara : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).anyAllItTyped elemTy = true := by
    simp [Factory.someOf, Term.anyAllItTyped, Factory.anyAllItVar]
  have ⟨hptw, pty, hptty⟩ := compilePred_wf hwε hvarw hvarty hpt
  have hptn := compilePred_noSetAll hwε hvarn hpt
  have hpta := compilePred_anyAllItTyped (elemTy := elemTy) hwε hvara hpt
  have hgp := wf_option_get hptw hptty
  rw [hpbool] at hgp
  have hgpn : (option.get pt).NoSetAll = true := noSetAll_option_get hptn
  have hgpa : (option.get pt).anyAllItTyped elemTy = true := anyAllItTyped_option_get hpta
  have hns := wf_isSome hptw
  have hnotw := wf_not hns.left hns.right
  have hnotn : (Factory.not (isSome pt)).NoSetAll = true := noSetAll_not (noSetAll_isSome hptn)
  have hnota : (Factory.not (isSome pt)).anyAllItTyped elemTy = true := anyAllItTyped_not (anyAllItTyped_isSome hpta)
  exact wf_set_all hgt.left hgt.right hgp.left hpbool hnotw.left hnotw.right hgpn hnotn hgpa hnota

private theorem compile_all_wf {x₁ : Expr} {p : PredExpr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.all x₁ p))
  (hok : compile (Expr.all x₁ p) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ t.typeOf = .option .bool := by
  have hwφ₁ : SymEnv.WellFormedFor εnv x₁ := by
    refine ⟨hwf.left, ?_⟩
    have hv := hwf.right
    cases hv with | all_valid hvx _ => exact hvx
  rw [compile.eq_def] at hok
  simp only [] at hok
  split at hok
  · simp only [reduceCtorEq] at hok   -- D-71 guard: ¬ NoItDependentIn ⇒ .error, contradicts hok
  simp_do_let (compile x₁ εnv) at hok
  rename_i t₁ hr₁
  have ⟨ih1w, ty1, hty1⟩ := ih₁ hwφ₁ hr₁
  split at hok
  · -- D-69: `.none ty` receiver
    rename_i ty
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    refine ⟨Term.WellFormed.none_wf TermType.WellFormed.bool_wf, ?_⟩
    simp only [Factory.noneOf, typeOf_term_none]
  · -- non-`.none` receiver: existing structure
    split at hok
    · rename_i elemTy helemq
      -- shared receiver facts (independent of the fold / symbolic split)
      have hgt := wf_option_get ih1w hty1
      have htys : ty1 = .set elemTy := by rw [← hgt.right]; exact helemq
      rw [htys] at hgt
      have hel : TermType.WellFormed εnv.entities elemTy := by
        have hw := typeOf_wf_term_is_wf hgt.left
        rw [hgt.right] at hw
        cases hw with | set_wf h => exact h
      -- symbolic path proof, reused by both symbolic sub-cases
      have symbolic :
        ∀ {pt : Term},
          compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv = Except.ok pt →
          (option.get pt).typeOf = .bool →
          (Factory.ifSome t₁ (Factory.set.all (option.get t₁) (option.get pt) (Factory.not (Factory.isSome pt)))).WellFormed εnv.entities ∧
          (Factory.ifSome t₁ (Factory.set.all (option.get t₁) (option.get pt) (Factory.not (Factory.isSome pt)))).typeOf = .option .bool := by
        intro pt hpt hpbool
        have hvarw : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).WellFormed εnv.entities :=
          Term.WellFormed.some_wf (Term.WellFormed.var_wf hel)
        have hvarty : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).typeOf = .option elemTy := by
          simp only [Factory.someOf, typeOf_term_some, typeOf_term_var, Factory.anyAllItVar]
        have hvarn : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).NoSetAll = true := by
          simp only [Factory.someOf, Term.NoSetAll]
        have hvara : (Factory.someOf (Term.var (Factory.anyAllItVar elemTy))).anyAllItTyped elemTy = true := by
          simp [Factory.someOf, Term.anyAllItTyped, Factory.anyAllItVar]
        have ⟨hptw, pty, hptty⟩ := compilePred_wf hwf.left hvarw hvarty hpt
        have hptn := compilePred_noSetAll hwf.left hvarn hpt
        have hpta := compilePred_anyAllItTyped (elemTy := elemTy) hwf.left hvara hpt
        have hgp := wf_option_get hptw hptty
        rw [hpbool] at hgp
        have hgpn : (option.get pt).NoSetAll = true := noSetAll_option_get hptn
        have hgpa : (option.get pt).anyAllItTyped elemTy = true := anyAllItTyped_option_get hpta
        have hns := wf_isSome hptw
        have hnotw := wf_not hns.left hns.right
        have hnotn : (Factory.not (isSome pt)).NoSetAll = true := noSetAll_not (noSetAll_isSome hptn)
        have hnota : (Factory.not (isSome pt)).anyAllItTyped elemTy = true := anyAllItTyped_not (anyAllItTyped_isSome hpta)
        have hsa := wf_set_all hgt.left hgt.right hgp.left hpbool hnotw.left hnotw.right hgpn hnotn hgpa hnota
        exact wf_ifSome_option ih1w hsa.left hsa.right
      -- now split on the inner `match option.get t₁`
      split at hok
      · rename_i vs ety' hvseq
        -- `option.get t₁ = .set (Set.mk vs) ety'`; so ety' = elemTy and the set is WF
        have htyeq : ety' = elemTy := by
          have := hgt.right
          rw [hvseq] at this
          simp only [Term.typeOf, TermType.set.injEq] at this
          exact this
        subst htyeq
        split at hok
        · -- literal fold path
          rename_i hlit
          simp only [List.all_eq_true] at hlit
          -- element facts from set-WF of (option.get t₁)
          have hsetw := hgt.left
          rw [hvseq] at hsetw
          have helts : ∀ vi ∈ vs, vi.WellFormed εnv.entities ∧ vi.typeOf = ety' := by
            cases hsetw with | set_wf h₁ h₂ _ _ =>
            intro vi hmem
            exact ⟨h₁ vi hmem, by rw [h₂ vi hmem]⟩
          -- extract pts from the mapM
          simp_do_let (vs.mapM (fun vi => do
            let pti ← compilePred p (Factory.someOf vi) εnv
            if (option.get pti).typeOf = TermType.bool then Except.ok pti else Except.error SymCC.Error.typeError)) at hok
          rename_i pts hpts
          simp only [Except.ok.injEq] at hok; subst hok
          rw [List.mapM_ok_iff_forall₂] at hpts
          -- per-element WF of pts entries
          have hptsfacts : ∀ pti ∈ pts, pti.WellFormed εnv.entities ∧ pti.typeOf = .option .bool := by
            intro pti hmem
            have ⟨vi, hvimem, hvi⟩ := List.forall₂_implies_all_right hpts pti hmem
            -- hvi : (do let p ← compilePred ...; if ... then .ok p else .error) = .ok pti
            cases hcp : compilePred p (Factory.someOf vi) εnv <;>
              simp only [hcp, Except.bind_err, Except.bind_ok, reduceCtorEq] at hvi
            rename_i cpt
            split at hvi <;> simp only [Except.ok.injEq, reduceCtorEq] at hvi
            rename_i hbool; subst hvi
            have ⟨hvw, hvty⟩ := helts vi hvimem
            have hviw : (Factory.someOf vi).WellFormed εnv.entities := Term.WellFormed.some_wf hvw
            have hvity : (Factory.someOf vi).typeOf = .option ety' := by
              simp only [Factory.someOf, typeOf_term_some, hvty]
            have ⟨hcpw, cty, hcpty⟩ := compilePred_wf hwf.left hviw hvity hcp
            -- (option.get cpt).typeOf = .bool and cpt.typeOf = .option cty ⇒ cty = .bool
            have hgcp := wf_option_get hcpw hcpty
            rw [hbool] at hgcp
            refine ⟨hcpw, ?_⟩
            rw [hcpty, hgcp.right]
          have hres := compile_all_fold_result_wf (ety := ety') ih1w (by rw [hty1, htys]) hptsfacts
          exact ⟨hres.left, hres.right⟩
        · -- inner symbolic path (else of the literal guard)
          rename_i hlit
          simp_do_let (compilePred p (Factory.someOf (.var (Factory.anyAllItVar ety'))) εnv) at hok
          rename_i pt hpt
          split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
          rename_i hpbool; subst hok
          have h := symbolic hpt hpbool
          exact ⟨h.left, h.right⟩
      · -- typeOf-symbolic path (option.get t₁ not a literal set)
        simp_do_let (compilePred p (Factory.someOf (.var (Factory.anyAllItVar elemTy))) εnv) at hok
        rename_i pt hpt
        split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
        rename_i hpbool; subst hok
        have h := symbolic hpt hpbool
        exact ⟨h.left, h.right⟩
    · simp only [reduceCtorEq] at hok

public theorem compile_wf {x : Expr} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedFor x →
  compile x εnv = .ok t →
  (t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty)
:= by
  intro hwf hok
  match x with
  | .lit _           => exact compile_lit_wf hok
  | .var v           => exact compile_var_wf hwf hok
  | .ite x₁ x₂ x₃    =>
    have ih₁ := @compile_wf x₁
    have ih₂ := @compile_wf x₂
    have ih₃ := @compile_wf x₃
    exact compile_ite_wf hwf hok ih₁ ih₂ ih₃
  | .and x₁ x₂       =>
    have ih₁ := @compile_wf x₁
    have ih₂ := @compile_wf x₂
    exact compile_and_wf hwf hok ih₁ ih₂
  | .or x₁ x₂        =>
    have ih₁ := @compile_wf x₁
    have ih₂ := @compile_wf x₂
    exact compile_or_wf hwf hok ih₁ ih₂
  | .unaryApp _ x₁ =>
    have ih₁ := @compile_wf x₁
    exact compile_unaryApp_wf hwf hok ih₁
  | .binaryApp _ x₁ x₂ =>
    have ih₁ := @compile_wf x₁
    have ih₂ := @compile_wf x₂
    exact compile_binaryApp_wf hwf hok ih₁ ih₂
  | .getAttr x₁ _    =>
    have ih₁ := @compile_wf x₁
    exact compile_getAttr_wf hwf hok ih₁
  | .hasAttr x₁ _    =>
    have ih₁ := @compile_wf x₁
    exact compile_hasAttr_wf hwf hok ih₁
  | .extHasAttr x₁ _ _ =>
    have ih₁ := @compile_wf x₁
    exact compile_extHasAttr_wf hwf hok ih₁
  | .set xs          =>
    have ih : ∀ xᵢ ∈ xs, CompileWF xᵢ := by
      intro xᵢ _
      exact @compile_wf xᵢ
    exact compile_set_wf hwf hok ih
  | .record axs      =>
    have ih : ∀ aᵢ xᵢ, (aᵢ, xᵢ) ∈ axs → CompileWF xᵢ := by
      intro aᵢ xᵢ h
      have _ : sizeOf xᵢ < 1 + sizeOf axs := List.sizeOf_snd_lt_sizeOf_list h
      exact @compile_wf xᵢ
    exact compile_record_wf hwf hok ih
  | .call _ xs       =>
    have ih : ∀ xᵢ ∈ xs, CompileWF xᵢ := by
      intro xᵢ _
      exact @compile_wf xᵢ
    exact compile_call_wf hwf hok ih
  | .all x₁ p        =>
    have ih₁ := @compile_wf x₁
    have h := compile_all_wf hwf hok ih₁
    exact ⟨h.1, .bool, h.2⟩

/-- The compiled `.all` term is well-formed of type `.option .bool`. -/
public theorem typeOf_compile_all_option_bool {x₁ : Expr} {p : PredExpr} {εnv : SymEnv} {t : Term}
    (hwf : SymEnv.WellFormedFor εnv (Expr.all x₁ p))
    (hok : compile (Expr.all x₁ p) εnv = Except.ok t) :
    t.typeOf = .option .bool :=
  (compile_all_wf hwf hok (fun h₁ h₂ => compile_wf h₁ h₂)).2

public theorem compile_extHasAttr_typeOf {x₁ : Expr} {a : Attr} {l : List Attr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.extHasAttr x₁ a l))
  (hok : compile (Expr.extHasAttr x₁ a l) εnv = Except.ok t) :
  t.typeOf = .option .bool
:= by
  have ih₁ : CompileWF x₁ := fun hwε hok => compile_wf hwε hok
  exact (compile_extHasAttr_wf' hwf hok ih₁).right

public theorem compile_option_get_wf {x : Expr} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedFor x →
  compile x εnv = .ok t →
  ∃ ty,
    (t.WellFormed εnv.entities ∧ t.typeOf = .option ty) ∧
    ((option.get t).WellFormed εnv.entities ∧ (option.get t).typeOf = ty)
:= by
  intro hwε hok
  replace ⟨hwt, ty, hty⟩ := compile_wf hwε hok
  have := wf_option_get hwt hty
  exists ty

---------- Evaluate is well-formed ----------

private def EvaluateWF (x : Expr)  : Prop :=
  ∀ {env : Env} {v : Value},
    env.WellFormedFor x →
    evaluate x env.request env.entities = .ok v →
    v.WellFormed env.entities

public theorem value_bool_wf {b : Bool} {es : Entities} :
  Value.WellFormed es (Value.prim (.bool b))
:= by exact Value.WellFormed.prim_wf (by simp only [Prim.WellFormed])

public theorem value_int_wf {i : Int64} {es : Entities} :
  Value.WellFormed es (Value.prim (.int i))
:= by exact Value.WellFormed.prim_wf (by simp only [Prim.WellFormed])

public theorem value_record_wf_implies_attr_value_wf {r : Map Attr Value} {a : Attr} {v : Value} {es : Entities} :
  Value.WellFormed es (Value.record r) →
  Map.find? r a = some v →
  Value.WellFormed es v
:= by
  intro hwf hf
  cases hwf
  rename_i hwf _
  exact hwf a v hf

private theorem evaluate_lit_wf {p: Prim} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.lit p))
  (hok : evaluate (Expr.lit p) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate.eq_def, Except.ok.injEq] at hok
  subst hok
  apply Value.WellFormed.prim_wf
  cases p <;> simp only [Prim.WellFormed]
  replace hwf := hwf.right
  cases hwf ; rename_i hwf
  simp only [Prim.ValidRef] at hwf
  exact hwf

private theorem evaluate_var_wf {xv : Var} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.var xv))
  (hok : evaluate (Expr.var xv) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate.eq_def] at hok
  replace hwf := hwf.left.left
  unfold Request.WellFormed at hwf
  split at hok <;>
  simp only [Except.ok.injEq] at hok <;>
  subst hok
  case h_4 => simp only [hwf]
  case h_1 | h_2 | h_3 =>
    apply Value.WellFormed.prim_wf
    simp only [Prim.WellFormed, hwf]

private theorem evaluate_ite_wf {x₁ x₂ x₃ : Expr} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.ite x₁ x₂ x₃))
  (hok : evaluate (Expr.ite x₁ x₂ x₃) env.request env.entities = Except.ok v)
  (ih₂ : EvaluateWF x₂)
  (ih₃ : EvaluateWF x₃) :
  Value.WellFormed env.entities v
:= by
  replace hwf := wf_env_for_ite_implies hwf
  rw [evaluate.eq_def] at hok
  simp only [Result.as] at hok
  simp_do_let (evaluate x₁ env.request env.entities) as hok₁ at hok
  rename_i v₁
  simp only [Coe.coe, Value.asBool] at hok
  split at hok <;>
  simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
  split at hok
  · exact ih₂ hwf.right.left hok
  · exact ih₃ hwf.right.right hok

private theorem evaluate_and_or_wf {x₁ x₂ : Expr} {env : Env} {v : Value} {shortCircuit : Bool}
  (hok: (do
    let b ← Result.as Bool (evaluate x₁ env.request env.entities)
    if b = shortCircuit
    then Except.ok (Value.prim (Prim.bool b))
    else Lean.Internal.coeM (Result.as Bool (evaluate x₂ env.request env.entities))) =
    Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [Result.as] at hok
  simp_do_let (evaluate x₁ env.request env.entities) as hok₁ at hok
  rename_i v₁
  simp only [Coe.coe, Value.asBool] at hok
  split at hok <;>
  simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
  cases hok₂ : evaluate x₂ env.request env.entities <;>
  simp only [Lean.Internal.coeM, hok₂, Except.bind_err] at hok
  case error =>
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    exact value_bool_wf
  case ok =>
    split at hok
    case isTrue =>
      simp only [Except.ok.injEq] at hok
      subst hok
      exact value_bool_wf
    case isFalse =>
      split at hok <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
      simp only [pure, Except.pure, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe,
        Coe.coe, Except.ok.injEq] at hok
      subst hok
      exact value_bool_wf

private theorem evaluate_and_wf {x₁ x₂ : Expr} {env : Env} {v : Value}
  (hok : evaluate (Expr.and x₁ x₂) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp only [Bool.not_eq_true'] at hok
  exact evaluate_and_or_wf hok

private theorem evaluate_all_wf {x₁ : Expr} {p : PredExpr} {env : Env} {v : Value}
  (hok : evaluate (Expr.all x₁ p) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp only at hok
  cases h₁ : Result.as (Set Value) (evaluate x₁ env.request env.entities) <;>
    simp only [h₁, Except.bind_err, Except.bind_ok, reduceCtorEq] at hok
  simp only [evalAll] at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
  subst hok
  exact value_bool_wf

private theorem evaluate_or_wf {x₁ x₂ : Expr} {env : Env} {v : Value}
  (hok : evaluate (Expr.or x₁ x₂) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  exact evaluate_and_or_wf hok

private theorem evaluate_hasAttr_wf {x : Expr} {a : Attr} {env : Env} {v : Value}
  (hok : evaluate (Expr.hasAttr x a) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp only [hasAttr, attrsOf] at hok
  simp_do_let (evaluate x env.request env.entities) at hok
  split at hok
  case h_3 => simp only [Except.bind_err, reduceCtorEq] at hok
  case h_1 | h_2 =>
    simp only [Except.bind_ok, Except.ok.injEq] at hok
    subst hok
    exact value_bool_wf

public theorem hasAttrs_loop_ok_is_bool {v : Value} {attrs : List Attr} {es : Entities} {r : Value} :
  hasAttrs.loop v attrs es = .ok r →
  ∃ b, r = Value.prim (.bool b)
:= by
  intro hok
  induction attrs generalizing v with
  | nil =>
    simp only [hasAttrs.loop, Except.ok.injEq] at hok
    exact ⟨true, hok.symm⟩
  | cons a rest ih =>
    simp only [hasAttrs.loop] at hok
    split at hok
    · split at hok
      · exact ih hok
      · simp only [Except.ok.injEq] at hok
        exact ⟨false, hok.symm⟩
    · simp at hok

public theorem hasAttrs_ok_is_bool {v : Value} {attr : Attr} {attrs : List Attr} {es : Entities} {r : Value} :
  hasAttrs v attr attrs es = .ok r →
  ∃ b, r = Value.prim (.bool b)
:= by
  intro hok
  simp only [hasAttrs] at hok
  exact hasAttrs_loop_ok_is_bool hok

private theorem evaluate_extHasAttr_wf {x : Expr} {a : Attr} {l : List Attr} {env : Env} {v : Value}
  (hok : evaluate (Expr.extHasAttr x a l) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp_do_let (evaluate x env.request env.entities) at hok
  have ⟨b, hb⟩ := hasAttrs_ok_is_bool hok
  subst hb
  exact value_bool_wf

private theorem evaluate_getAttr_wf {x : Expr} {a : Attr} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.getAttr x a))
  (hok : evaluate (Expr.getAttr x a) env.request env.entities = Except.ok v)
  (ih  : EvaluateWF x) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp only [getAttr, attrsOf] at hok
  simp_do_let (evaluate x env.request env.entities) at hok
  rename_i hok₁
  replace hwf := wf_env_for_getAttr_implies hwf
  specialize ih hwf hok₁
  split at hok
  case h_1 r =>
    simp only [Except.bind_ok, Map.findOrErr_ok_iff_find?_some] at hok
    rename_i v₁
    exact value_record_wf_implies_attr_value_wf ih hok
  case h_2 uid =>
    simp_do_let (Entities.attrs env.entities uid) at hok
    rename_i ha
    simp only [Map.findOrErr_ok_iff_find?_some] at hok
    rename_i r v₁
    simp only [Entities.attrs] at ha
    simp_do_let (Map.findOrErr env.entities uid Error.entityDoesNotExist) at ha
    rename_i d hd
    simp only [Except.ok.injEq] at ha
    subst ha
    apply value_record_wf_implies_attr_value_wf _ hok
    simp only [Map.findOrErr_ok_iff_find?_some] at hd
    exact (hwf.left.right.right uid d hd).left
  case h_3 =>
    simp only [Except.bind_err, reduceCtorEq] at hok

public theorem intOrErr_ok_wf {i : Option Int64} {v : Value} {es : Entities} :
  intOrErr i = Except.ok v → Value.WellFormed es v
:= by
  intro hok
  simp only [intOrErr] at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
  subst hok
  exact value_int_wf

private theorem evaluate_unaryApp_wf {op : UnaryOp} {x : Expr} {env : Env} {v : Value}
  (hok : evaluate (Expr.unaryApp op x) env.request env.entities = Except.ok v):
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp_do_let (evaluate x env.request env.entities) at hok
  simp only [apply₁] at hok
  split at hok <;> (try simp only [Except.ok.injEq, reduceCtorEq] at hok)
  case h_1 | h_3 | h_4 | h_5 =>
    subst hok
    exact value_bool_wf
  case h_2 =>
    exact intOrErr_ok_wf hok

public theorem inₛ_wf {uid : EntityUID} {vs : Set Value} {es : Entities} {v : Value} :
  inₛ uid vs es = Except.ok v → Value.WellFormed es v
:= by
  intro hok
  simp only [inₛ] at hok
  simp_do_let (Set.mapOrErr Value.asEntityUID vs Spec.Error.typeError) at hok
  simp only [Except.ok.injEq] at hok
  subst hok
  exact value_bool_wf

private theorem evaluate_binaryApp_wf {op : BinaryOp} {x₁ x₂ : Expr} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.binaryApp op x₁ x₂))
  (hok : evaluate (Expr.binaryApp op x₁ x₂) env.request env.entities = Except.ok v)
  (ih₁ : EvaluateWF x₁):
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp_do_let (evaluate x₁ env.request env.entities) at hok
  simp_do_let (evaluate x₂ env.request env.entities) at hok
  simp only [apply₂] at hok
  split at hok <;> (try simp only [Except.ok.injEq, hasTag, reduceCtorEq] at hok)
  any_goals (subst hok ; exact value_bool_wf)
  any_goals (exact intOrErr_ok_wf hok)
  exact inₛ_wf hok
  case _ uid tag h₁ h₂ => -- getTag
    simp only [getTag] at hok
    simp_do_let (env.entities.tags uid) at hok
    rename_i heq
    rw [Map.findOrErr_ok_iff_find?_some] at hok
    replace hwf := (wf_env_for_binaryApp_implies hwf).left
    specialize ih₁ hwf h₁
    replace hwf := hwf.left.right
    simp only [Entities.tags] at heq
    simp_do_let (Map.findOrErr env.entities uid Error.entityDoesNotExist) at heq
    rename_i d hd
    simp only [Except.ok.injEq] at heq
    subst heq
    rw [Map.findOrErr_ok_iff_find?_some] at hd
    replace hwf := hwf.2 uid d hd
    exact hwf.right.right.right.right tag v hok

private theorem evaluate_call_wf {xfn : ExtFun} {xs : List Expr} {env : Env} {v : Value}
  (hok : evaluate (Expr.call xfn xs) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp_do_let (List.mapM₁ xs fun x => evaluate x.val env.request env.entities) at hok
  simp only [call] at hok
  split at hok <;> (try simp only [Except.ok.injEq, reduceCtorEq] at hok)
  any_goals (subst hok ; exact value_bool_wf)
  any_goals (subst hok; exact value_int_wf)
  any_goals (subst hok; exact Value.WellFormed.ext_wf)
  all_goals {
    simp only [res] at hok
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    simp only [Coe.coe] at hok
    subst hok
    exact Value.WellFormed.ext_wf
  }

private theorem evaluate_set_wf {env : Env} {v : Value} {xs : List Expr}
  (hwf : Env.WellFormedFor env (Expr.set xs))
  (hok : evaluate (Expr.set xs) env.request env.entities = Except.ok v)
  (ih : ∀ (x : Expr), x ∈ xs → Cedar.Thm.EvaluateWF x) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp_do_let (List.mapM₁ xs fun x => evaluate x.val env.request env.entities) at hok
  rename_i vs hvs
  simp only [Except.ok.injEq] at hok
  subst hok
  simp only [List.mapM₁_eq_mapM (λ x => evaluate x env.request env.entities), ← List.mapM'_eq_mapM] at hvs
  apply Value.WellFormed.set_wf _ (Set.make_wf vs)
  intro v hv
  rw [Set.mem_make] at hv
  replace ⟨x, hx, hvs⟩ := List.mapM'_ok_implies_all_from_ok hvs v hv
  exact ih x hx (wf_env_for_set_implies hwf x hx) hvs

private theorem evaluate_record_wf {env : Env} {v : Value} {axs : List (Attr × Expr)}
  (hwf : Env.WellFormedFor env (Expr.record axs))
  (hok : evaluate (Expr.record axs) env.request env.entities = Except.ok v)
  (ih : ∀ (a : Attr) (x : Expr), (a, x) ∈ axs → Cedar.Thm.EvaluateWF x) :
  Value.WellFormed env.entities v
:= by
  rw [evaluate.eq_def] at hok
  simp_do_let ( List.mapM₂ axs fun x => bindAttr x.1.fst (evaluate x.1.snd env.request env.entities)) at hok
  rename_i vs hvs
  simp only [Except.ok.injEq] at hok
  subst hok
  simp only [List.mapM₂_eq_mapM λ (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd env.request env.entities)] at hvs
  rw [← List.mapM'_eq_mapM] at hvs
  apply Value.WellFormed.record_wf _ (Map.make_wf vs)
  intro a v hv
  replace hv := Map.find?_mem_toList hv
  replace hv := Map.mem_make_mem_list hv
  replace ⟨x, hx, hvs⟩ := List.mapM'_ok_implies_all_from_ok hvs (a, v) hv
  simp [bindAttr] at hvs
  simp_do_let (evaluate x.snd env.request env.entities) at hvs
    <;> simp [Functor.map, Except.map] at hvs
  rename_i v' hok
  replace ⟨hvs, hvs'⟩ := hvs
  subst hvs'
  have hx' : (a, x.snd) = x := by rw [← hvs]
  replace hx' : (a, x.snd) ∈ axs := by rw [hx'] ; exact hx
  exact ih a x.snd hx' (wf_env_for_record_implies hwf x hx) hok

public theorem evaluate_wf {x : Expr} {env : Env} {v : Value} :
  env.WellFormedFor x →
  evaluate x env.request env.entities = .ok v →
  v.WellFormed env.entities
:= by
  intro hwf hok
  match x with
  | .lit _            => exact evaluate_lit_wf hwf hok
  | .var _            => exact evaluate_var_wf hwf hok
  | .ite _ x₂ x₃      => exact evaluate_ite_wf hwf hok (@evaluate_wf x₂) (@evaluate_wf x₃)
  | .and _ _          => exact evaluate_and_wf hok
  | .or _ _           => exact evaluate_or_wf hok
  | .unaryApp _ _     => exact evaluate_unaryApp_wf hok
  | .binaryApp _ x₁ _ => exact evaluate_binaryApp_wf hwf hok (@evaluate_wf x₁)
  | .getAttr x₁ _     => exact evaluate_getAttr_wf hwf hok (@evaluate_wf x₁)
  | .hasAttr _ _      => exact evaluate_hasAttr_wf hok
  | .extHasAttr _ _ _ => exact evaluate_extHasAttr_wf hok
  | .set xs           =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → EvaluateWF xᵢ := by
      intro xᵢ _
      exact @evaluate_wf xᵢ
    exact evaluate_set_wf hwf hok ih
  | .record axs       =>
    have ih : ∀ aᵢ xᵢ, (aᵢ, xᵢ) ∈ axs → EvaluateWF xᵢ := by
      intro aᵢ xᵢ h
      have _ : sizeOf xᵢ < 1 + sizeOf axs := List.sizeOf_snd_lt_sizeOf_list h
      exact @evaluate_wf xᵢ
    exact evaluate_record_wf hwf hok ih
  | .call _ _         => exact evaluate_call_wf hok
  | .all _ _          => exact evaluate_all_wf hok
termination_by sizeOf x

public theorem wf_value_uid_implies_exists_entity_data {es : Entities} {uid : EntityUID}
  (hwf : Value.WellFormed es (Value.prim (Prim.entityUID uid))) :
  ∃ d, es.find? uid = some d
:= by
  cases hwf ; rename_i hwf
  simp only [Prim.WellFormed, Map.contains_iff_some_find?] at hwf
  exact hwf

/-- Public re-export of `compilePred_noSetAll` (D-68): a compiled predicate over a
`NoSetAll` `it` is itself `NoSetAll`. Needed by the non-module `AllInterpret`, which
cannot `import all` the module `CompilePredWF` where the original lives. -/
public theorem compilePred_noSetAll' {p : PredExpr} {it r : Term} {εnv : SymEnv}
    (hwε : εnv.WellFormed) (hit : it.NoSetAll = true) (hok : compilePred p it εnv = Except.ok r) :
    r.NoSetAll = true :=
  compilePred_noSetAll hwε hit hok

/-- Public re-export of `compilePred_anyAllItTyped` (D-68). See `compilePred_noSetAll'`. -/
public theorem compilePred_anyAllItTyped' {p : PredExpr} {it r : Term} {εnv : SymEnv} {elemTy : TermType}
    (hwε : εnv.WellFormed) (hit : it.anyAllItTyped elemTy = true) (hok : compilePred p it εnv = Except.ok r) :
    r.anyAllItTyped elemTy = true :=
  compilePred_anyAllItTyped hwε hit hok

/-- Public re-export of `wf_set_all` (D-68). See `compilePred_noSetAll'`. -/
public theorem wf_set_all' {εs : SymEntities} {S P E : Term} {ety : TermType}
    (hSwf : S.WellFormed εs) (hSty : S.typeOf = .set ety)
    (hPwf : P.WellFormed εs) (hPty : P.typeOf = .bool)
    (hEwf : E.WellFormed εs) (hEty : E.typeOf = .bool)
    (hPn : P.NoSetAll = true) (hEn : E.NoSetAll = true)
    (hPa : P.anyAllItTyped ety = true) (hEa : E.anyAllItTyped ety = true) :
    (Factory.set.all S P E).WellFormed εs ∧ (Factory.set.all S P E).typeOf = .option .bool :=
  wf_set_all hSwf hSty hPwf hPty hEwf hEty hPn hEn hPa hEa

end Cedar.Thm
