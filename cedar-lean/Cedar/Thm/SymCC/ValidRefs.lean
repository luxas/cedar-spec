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

import Cedar.Thm.SymbolicCompilation
import Cedar.Thm.Validation.SubstituteAction
import Cedar.Thm.Validation.Typechecker.Basic

/-! Facts about `Entities.ValidRefsFor`. -/

namespace Cedar.Thm

open Spec SymCC Validation Data

/-- Shorthand form of inductive hypotheses used in the following proofs. -/
abbrev typeOf_preserves_valid_refs_ih (Γ : TypeEnv) (entities : Entities) (e : Expr) : Prop
:= ∀ {tx c c'},
  typeOf e c Γ = Except.ok (tx, c') →
  Expr.ValidRefs (fun uid => Map.contains entities uid = true) e →
  Expr.ValidRefs (fun uid => Map.contains entities uid = true) tx.toExpr

theorem typeOf_preserves_valid_refs_lit
  {Γ : TypeEnv} (entities : Entities)
  {p : Prim} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.lit p) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.lit p)) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfLit] at hty
  cases p with
  | bool | int | string =>
    split at hty
    any_goals contradiction
    all_goals
      simp only [
        ok, List.empty_eq,
        Function.comp_apply,
        Except.ok.injEq,
        Prod.mk.injEq,
        List.nil_eq,
      ] at hty
      simp only [←hty.1, TypedExpr.toExpr]
      repeat constructor
  | entityUID uid =>
    split at hty
    any_goals contradiction
    all_goals
      split at hty
      · simp only [
          ok, List.empty_eq,
          Function.comp_apply,
          Except.ok.injEq,
          Prod.mk.injEq,
          List.nil_eq,
        ] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        cases hrefs
        assumption
      · contradiction

theorem typeOf_preserves_valid_refs_var
  {Γ : TypeEnv} (entities : Entities)
  {var : Var} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.var var) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.var var)) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfVar] at hty
  split at hty
  all_goals
    simp only [
      ok, List.empty_eq, Function.comp_apply,
      Except.ok.injEq, Prod.mk.injEq,
      List.nil_eq,
    ] at hty
    simp only [←hty.1, TypedExpr.toExpr]
    constructor

theorem typeOf_preserves_valid_refs_and
  {Γ : TypeEnv} (entities : Entities)
  {e₁ e₂ : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.and e₁ e₂) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.and e₁ e₂))
  (ih₁ : typeOf_preserves_valid_refs_ih Γ entities e₁)
  (ih₂ : typeOf_preserves_valid_refs_ih Γ entities e₂) :
  entities.ValidRefsFor tx.toExpr
:= by
  cases hrefs with | and_valid hrefs₁ hrefs₂ =>
  simp only [typeOf, typeOfAnd] at hty
  cases hty₁ : typeOf e₁ c₁ Γ with
  | error => simp [hty₁] at hty
  | ok r₁ =>
    have ⟨tx₁, c₃⟩ := r₁
    simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
    split at hty
    any_goals contradiction
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
      simp only [←hty.1]
      exact ih₁ hty₁ hrefs₁
    · cases hty₂ : typeOf e₂ (c₁ ∪ c₃) Γ with
      | error => simp [hty₂] at hty
      | ok r₂ =>
        have ⟨tx₂, c₄⟩ := r₂
        simp only [hty₂, Except.bind_ok] at hty
        split at hty
        any_goals contradiction
        all_goals
          simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          · exact ih₁ hty₁ hrefs₁
          · exact ih₂ hty₂ hrefs₂

theorem typeOf_preserves_valid_refs_or
  {Γ : TypeEnv} (entities : Entities)
  {e₁ e₂ : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.or e₁ e₂) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.or e₁ e₂))
  (ih₁ : typeOf_preserves_valid_refs_ih Γ entities e₁)
  (ih₂ : typeOf_preserves_valid_refs_ih Γ entities e₂) :
  entities.ValidRefsFor tx.toExpr
:= by
  cases hrefs with | or_valid hrefs₁ hrefs₂ =>
  simp only [typeOf, typeOfOr] at hty
  cases hty₁ : typeOf e₁ c₁ Γ with
  | error => simp [hty₁] at hty
  | ok r₁ =>
    have ⟨tx₁, c₃⟩ := r₁
    simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
    split at hty
    any_goals contradiction
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
      simp only [←hty.1]
      exact ih₁ hty₁ hrefs₁
    · cases hty₂ : typeOf e₂ c₁ Γ with
      | error => simp [hty₂] at hty
      | ok r₂ =>
        have ⟨tx₂, c₄⟩ := r₂
        simp only [hty₂, Except.bind_ok] at hty
        split at hty
        any_goals contradiction
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        · exact ih₁ hty₁ hrefs₁
        · exact ih₂ hty₂ hrefs₂
    · cases hty₂ : typeOf e₂ c₁ Γ with
      | error => simp [hty₂] at hty
      | ok r₂ =>
        have ⟨tx₂, c₄⟩ := r₂
        simp only [hty₂, Except.bind_ok] at hty
        split at hty
        any_goals contradiction
        all_goals
          simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          · exact ih₁ hty₁ hrefs₁
          · exact ih₂ hty₂ hrefs₂

theorem typeOf_preserves_valid_refs_ite
  {Γ : TypeEnv} (entities : Entities)
  {e₁ e₂ e₃ : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.ite e₁ e₂ e₃) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.ite e₁ e₂ e₃))
  (ih₁ : typeOf_preserves_valid_refs_ih Γ entities e₁)
  (ih₂ : typeOf_preserves_valid_refs_ih Γ entities e₂)
  (ih₃ : typeOf_preserves_valid_refs_ih Γ entities e₃) :
  entities.ValidRefsFor tx.toExpr
:= by
  cases hrefs with | ite_valid hrefs₁ hrefs₂ hrefs₃ =>
  simp only [typeOf, typeOfIf] at hty
  cases hty₁ : typeOf e₁ c₁ Γ with
  | error => simp [hty₁] at hty
  | ok r₁ =>
    have ⟨tx₁, c₃⟩ := r₁
    simp only [hty₁, Except.bind_ok] at hty
    split at hty
    any_goals contradiction
    · cases hty₂ : typeOf e₂ (c₁ ∪ c₃) Γ with
      | error => simp [hty₂] at hty
      | ok r₂ =>
        have ⟨tx₂, c₄⟩ := r₂
        simp only [hty₂, ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        · exact ih₁ hty₁ hrefs₁
        · exact ih₂ hty₂ hrefs₂
        · exact ih₂ hty₂ hrefs₂
    · cases hty₃ : typeOf e₃ c₁ Γ with
      | error => simp [hty₃] at hty
      | ok r₃ =>
        have ⟨tx₃, c₄⟩ := r₃
        simp only [hty₃, ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        · exact ih₁ hty₁ hrefs₁
        · exact ih₃ hty₃ hrefs₃
        · exact ih₃ hty₃ hrefs₃
    · cases hty₂ : typeOf e₂ (c₁ ∪ c₃) Γ with
      | error => simp [hty₂] at hty
      | ok r₂ =>
      cases hty₃ : typeOf e₃ c₁ Γ with
      | error => simp [hty₂, hty₃] at hty
      | ok r₃ =>
      have ⟨tx₂, c₄⟩ := r₂
      have ⟨tx₃, c₅⟩ := r₃
      simp only [hty₂, hty₃, ok, Except.bind_ok] at hty
      split at hty
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        · exact ih₁ hty₁ hrefs₁
        · exact ih₂ hty₂ hrefs₂
        · exact ih₃ hty₃ hrefs₃
      · contradiction

theorem typeOf_preserves_valid_refs_unaryApp
  {Γ : TypeEnv} (entities : Entities)
  {op : UnaryOp} {e : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.unaryApp op e) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.unaryApp op e))
  (ih : typeOf_preserves_valid_refs_ih Γ entities e) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfUnaryApp] at hty
  cases hrefs with | unaryApp_valid hrefs =>
  cases hty₁ : typeOf e c₁ Γ with
  | error => simp [hty₁] at hty
  | ok r₁ =>
    have ⟨tx₁, c₃⟩ := r₁
    simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
    split at hty
    any_goals contradiction
    all_goals
      simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
      simp only [←hty.1, TypedExpr.toExpr]
      constructor
      exact ih hty₁ hrefs

theorem typeOf_preserves_valid_refs_binaryApp
  {Γ : TypeEnv} (entities : Entities)
  {op : BinaryOp} {e₁ e₂ : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.binaryApp op e₁ e₂) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.binaryApp op e₁ e₂))
  (ih₁ : typeOf_preserves_valid_refs_ih Γ entities e₁)
  (ih₂ : typeOf_preserves_valid_refs_ih Γ entities e₂) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfBinaryApp] at hty
  cases hrefs with | binaryApp_valid hrefs₁ hrefs₂ =>
  cases hty₁ : typeOf e₁ c₁ Γ with
  | error => simp [hty₁] at hty
  | ok r₁ =>
  cases hty₂ : typeOf e₂ c₁ Γ with
  | error => simp [hty₁, hty₂] at hty
  | ok r₂ =>
    have ⟨tx₁, c₃⟩ := r₁
    have ⟨tx₂, c₄⟩ := r₂
    simp only [hty₁, hty₂, List.empty_eq, Except.bind_ok] at hty
    split at hty
    any_goals contradiction
    any_goals
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
      simp only [←hty.1, TypedExpr.toExpr]
      constructor
      exact ih₁ hty₁ hrefs₁
      exact ih₂ hty₂ hrefs₂
    any_goals
      simp only [bind, Except.bind] at hty
      split at hty
      any_goals contradiction
      all_goals
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        exact ih₁ hty₁ hrefs₁
        exact ih₂ hty₂ hrefs₂
    · simp only [typeOfEq] at hty
      split at hty
      · split at hty
        all_goals
          simp only [
            ok, List.empty_eq, Function.comp_apply,
            Except.ok.injEq, Prod.mk.injEq,
            List.nil_eq,
          ] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          exact ih₁ hty₁ hrefs₁
          exact ih₂ hty₂ hrefs₂
      · split at hty
        · simp only [
            ok, List.empty_eq, Function.comp_apply,
            Except.ok.injEq, Prod.mk.injEq,
            List.nil_eq,
          ] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          exact ih₁ hty₁ hrefs₁
          exact ih₂ hty₂ hrefs₂
        · split at hty
          · simp only [
              ok, List.empty_eq, Function.comp_apply,
              Except.ok.injEq, Prod.mk.injEq,
              List.nil_eq,
            ] at hty
            simp only [←hty.1, TypedExpr.toExpr]
            constructor
            exact ih₁ hty₁ hrefs₁
            exact ih₂ hty₂ hrefs₂
          · contradiction

theorem typeOf_preserves_valid_refs_getAttr
  {Γ : TypeEnv} (entities : Entities)
  {e : Expr} {attr : Attr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.getAttr e attr) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.getAttr e attr))
  (ih : typeOf_preserves_valid_refs_ih Γ entities e) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfGetAttr] at hty
  cases hrefs with | getAttr_valid hrefs =>
  cases hty₁ : typeOf e c₁ Γ with
  | error => simp [hty₁] at hty
  | ok r₁ =>
    have ⟨tx₁, c₃⟩ := r₁
    simp only [hty₁, Except.bind_ok] at hty
    split at hty
    any_goals contradiction
    · simp only [bind, Except.bind] at hty
      split at hty
      contradiction
      simp only [ok,Except.ok.injEq, Prod.mk.injEq] at hty
      simp only [←hty.1, TypedExpr.toExpr]
      constructor
      exact ih hty₁ hrefs
    · simp only [bind, Except.bind] at hty
      split at hty
      · split at hty
        contradiction
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        exact ih hty₁ hrefs
      · contradiction

theorem typeOf_preserves_valid_refs_hasAttr
  {Γ : TypeEnv} (entities : Entities)
  {e : Expr} {attr : Attr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.hasAttr e attr) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.hasAttr e attr))
  (ih : typeOf_preserves_valid_refs_ih Γ entities e) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfHasAttr] at hty
  cases hrefs with | hasAttr_valid hrefs =>
  cases hty₁ : typeOf e c₁ Γ with
  | error => simp [hty₁] at hty
  | ok r₁ =>
    have ⟨tx₁, c₃⟩ := r₁
    simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
    split at hty
    any_goals contradiction
    · simp only [bind, Except.bind] at hty
      split at hty
      contradiction
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
      simp only [←hty.1, TypedExpr.toExpr]
      constructor
      exact ih hty₁ hrefs
    · simp only [bind, Except.bind] at hty
      split at hty
      · split at hty
        contradiction
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        exact ih hty₁ hrefs
      · split at hty
        · simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          exact ih hty₁ hrefs
        · contradiction

theorem typeOf_preserves_valid_refs_set
  {Γ : TypeEnv} (entities : Entities)
  {s : List Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.set s) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.set s))
  (ih_xs : ∀ x ∈ s, typeOf_preserves_valid_refs_ih Γ entities x) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfSet] at hty
  cases hrefs with | set_valid hrefs =>
  simp only [bind, Except.bind] at hty
  split at hty
  contradiction
  rename_i s' hs'
  split at hty
  contradiction
  rename_i hd tl
  split at hty
  · rename_i ty _
    simp only [ok, List.empty_eq, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
    simp only [←hty.1, TypedExpr.toExpr]
    constructor
    intros x' hmem_x'
    simp only [List.map₁_eq_map] at hmem_x'
    have ⟨tx', hmem_tx', htx'⟩ := List.mem_map.mp hmem_x'
    simp only [List.mapM₁_eq_mapM (λ x => justType (typeOf x c₁ Γ)) _] at hs'
    have ⟨x, hmem_x, hx⟩ := List.mapM_ok_implies_all_from_ok hs' tx' hmem_tx'
    simp only [justType] at hx
    cases htyₓ : typeOf x c₁ Γ with
    | error => simp [htyₓ, Except.map] at hx
    | ok r =>
      have ⟨tx, c₄⟩ := r
      simp only [htyₓ, Except.map, Except.ok.injEq] at hx
      simp only [←htx', ←hx]
      specialize hrefs x hmem_x
      exact ih_xs x hmem_x htyₓ hrefs
  · contradiction

theorem typeOf_preserves_valid_refs_call
  {Γ : TypeEnv} (entities : Entities)
  {xfn : ExtFun} {args : List Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.call xfn args) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.call xfn args))
  (ih_args : ∀ arg ∈ args, typeOf_preserves_valid_refs_ih Γ entities arg) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfCall, bind, Except.bind] at hty
  cases hrefs with | call_valid hrefs =>
  split at hty
  contradiction
  rename_i txs htxs
  split at hty
  any_goals contradiction
  any_goals
    try split at hty
    try contradiction
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
    simp only [←hty.1, TypedExpr.toExpr]
    constructor
    intros x' hmem_x'
    simp only [List.map₁_eq_map] at hmem_x'
    have ⟨tx', hmem_tx', htx'⟩ := List.mem_map.mp hmem_x'
    simp only [List.mapM₁_eq_mapM (λ x => justType (typeOf x c₁ Γ)) _] at htxs
    have ⟨x, hmem_x, hx⟩ := List.mapM_ok_implies_all_from_ok htxs tx' hmem_tx'
    simp only [justType] at hx
    cases htyₓ : typeOf x c₁ Γ with
    | error => simp [htyₓ, Except.map] at hx
    | ok r =>
      have ⟨tx, c₄⟩ := r
      simp only [htyₓ, Except.map, Except.ok.injEq] at hx
      simp only [←htx', ←hx]
      specialize hrefs x hmem_x
      exact ih_args x hmem_x htyₓ hrefs

theorem typeOf_preserves_valid_refs_record
  {Γ : TypeEnv} (entities : Entities)
  {rec : List (Attr × Expr)} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.record rec) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.record rec))
  (ih_rec : ∀ attr ∈ rec, typeOf_preserves_valid_refs_ih Γ entities attr.snd) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, bind, Except.bind] at hty
  cases hrefs with | record_valid hrefs =>
  split at hty
  contradiction
  rename_i txs htxs
  simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
  simp only [←hty.1, TypedExpr.toExpr]
  constructor
  intros attr_expr' hmem_attr_expr'
  simp only [List.map₂_eq_map_snd] at hmem_attr_expr'
  have ⟨⟨attr, tx⟩, hmem_attr_tx, hattr_tx⟩ := List.mem_map.mp hmem_attr_expr'
  simp only at hattr_tx
  simp only [←hattr_tx]
  simp only [List.mapM₂_eq_mapM
    (λ x => Except.map (λ y => (x.fst, y.fst)) (typeOf x.snd c₁ Γ)) _] at htxs
  have ⟨⟨attr', x⟩, hmem_attr'_x, hattr'_x⟩ := List.mapM_ok_implies_all_from_ok htxs (attr, tx) hmem_attr_tx
  cases htyₓ : typeOf x c₁ Γ with
  | error => simp [htyₓ, Except.map] at hattr'_x
  | ok r =>
    have ⟨tx', c₄⟩ := r
    simp only [Except.map, htyₓ, Except.ok.injEq, Prod.mk.injEq] at hattr'_x
    simp only [←hattr'_x]
    specialize hrefs (attr', x) hmem_attr'_x
    exact ih_rec (attr', x) hmem_attr'_x htyₓ hrefs

/-- `PredExpr.normalize` preserves `PredExpr.ValidRefs`: it only folds dead
`.and`/`.or`/`.ite` branches and recurses, never introducing a new entity
literal (D-99 ripple — the typed `.all` node stores `normalize p`, so the valid-
refs obligation on its `toExpr` is about the normalized predicate). -/
theorem normalize_validRefs {validRef : EntityUID → Prop} {p : PredExpr}
    {itTy : CedarType} {c : Capabilities} {env : TypeEnv}
    (h : PredExpr.ValidRefs validRef p) :
    PredExpr.ValidRefs validRef (PredExpr.normalize p itTy c env) := by
  induction p, c using PredExpr.normalize.induct (itTy := itTy) (env := env) with
  | case1 c => simpa only [PredExpr.normalize] using h
  | case2 c l => simpa only [PredExpr.normalize] using h
  | case3 c v => simpa only [PredExpr.normalize] using h
  | case4 c cond t e tyc c₁ htc htt ihc iht =>
    cases h with | ite_valid hc ht he =>
      simp only [PredExpr.normalize, htc, htt]; exact .ite_valid (ihc hc) (iht ht) (iht ht)
  | case5 c cond t e tyc c₁ htc hff ihc ihe =>
    cases h with | ite_valid hc ht he =>
      simp only [PredExpr.normalize, htc, hff]; exact .ite_valid (ihc hc) (ihe he) (ihe he)
  | case6 c cond t e tyc c₁ htc hntt hnff ihc iht ihe =>
    cases h with | ite_valid hc ht he =>
      simp only [PredExpr.normalize, htc, hntt, hnff]; exact .ite_valid (ihc hc) (iht ht) (ihe he)
  | case7 c cond t e err htc ihc iht ihe =>
    cases h with | ite_valid hc ht he =>
      simp only [PredExpr.normalize, htc]; exact .ite_valid (ihc hc) (iht ht) (ihe he)
  | case8 c a b tyc c₁ hta hff iha =>
    cases h with | and_valid ha hb => simp only [PredExpr.normalize, hta, hff]; exact iha ha
  | case9 c a b tyc c₁ hta hnff iha ihb =>
    cases h with | and_valid ha hb =>
      simp only [PredExpr.normalize, hta, hnff]; exact .and_valid (iha ha) (ihb hb)
  | case10 c a b err hta iha ihb =>
    cases h with | and_valid ha hb => simp only [PredExpr.normalize, hta]; exact .and_valid (iha ha) (ihb hb)
  | case11 c a b tyc c₁ hta htt iha =>
    cases h with | or_valid ha hb => simp only [PredExpr.normalize, hta, htt]; exact iha ha
  | case12 c a b tyc c₁ hta hntt iha ihb =>
    cases h with | or_valid ha hb =>
      simp only [PredExpr.normalize, hta, hntt]; exact .or_valid (iha ha) (ihb hb)
  | case13 c a b err hta iha ihb =>
    cases h with | or_valid ha hb => simp only [PredExpr.normalize, hta]; exact .or_valid (iha ha) (ihb hb)
  | case14 c op x ih =>
    cases h with | unaryApp_valid hx => simp only [PredExpr.normalize]; exact .unaryApp_valid (ih hx)
  | case15 c op a b iha ihb =>
    cases h with | binaryApp_valid ha hb => simp only [PredExpr.normalize]; exact .binaryApp_valid (iha ha) (ihb hb)
  | case16 c x a ih =>
    cases h with | getAttr_valid hx => simp only [PredExpr.normalize]; exact .getAttr_valid (ih hx)
  | case17 c x a ih =>
    cases h with | hasAttr_valid hx => simp only [PredExpr.normalize]; exact .hasAttr_valid (ih hx)
  | case18 c x a attrs ih =>
    cases h with | extHasAttr_valid hx => simp only [PredExpr.normalize]; exact .extHasAttr_valid (ih hx)
  | case19 c axs ih =>
    cases h with
    | record_valid hall =>
      simp only [PredExpr.normalize]
      apply PredExpr.ValidRefs.record_valid
      intro ax hax
      simp only [List.map₂_eq_map (fun x : Attr × PredExpr => (x.fst, PredExpr.normalize x.snd itTy c env)),
        List.mem_map] at hax
      obtain ⟨⟨a', e'⟩, hmem, heq⟩ := hax
      subst heq
      exact ih a' e' (List.sizeOf_snd_lt_sizeOf_list hmem) (hall (a', e') hmem)
  | case20 c f xs ih =>
    cases h with
    | call_valid hall =>
      simp only [PredExpr.normalize]
      apply PredExpr.ValidRefs.call_valid
      intro x hx
      simp only [List.map₁_eq_map (fun e : PredExpr => PredExpr.normalize e itTy c env),
        List.mem_map] at hx
      obtain ⟨e', hmem, heq⟩ := hx
      subst heq
      exact ih e' hmem (hall e' hmem)

theorem typeOf_preserves_valid_refs
  {Γ : TypeEnv} (entities : Entities)
  {expr : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf expr c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor expr) :
  entities.ValidRefsFor tx.toExpr
:= by
  cases expr with
  | lit p => exact typeOf_preserves_valid_refs_lit entities hty hrefs
  | var v => exact typeOf_preserves_valid_refs_var entities hty hrefs
  | and e₁ e₂ =>
    apply typeOf_preserves_valid_refs_and entities hty hrefs
    · intros tx c c'; apply typeOf_preserves_valid_refs
    · intros tx c c'; apply typeOf_preserves_valid_refs
  | or e₁ e₂ =>
    apply typeOf_preserves_valid_refs_or entities hty hrefs
    · intros tx c c'; apply typeOf_preserves_valid_refs
    · intros tx c c'; apply typeOf_preserves_valid_refs
  | ite e₁ e₂ e₃ =>
    apply typeOf_preserves_valid_refs_ite entities hty hrefs
    · intros tx c c'; apply typeOf_preserves_valid_refs
    · intros tx c c'; apply typeOf_preserves_valid_refs
    · intros tx c c'; apply typeOf_preserves_valid_refs
  | unaryApp _ e =>
    apply typeOf_preserves_valid_refs_unaryApp entities hty hrefs
    intros tx c c'; apply typeOf_preserves_valid_refs
  | binaryApp _ e₁ e₂ =>
    apply typeOf_preserves_valid_refs_binaryApp entities hty hrefs
    · intros tx c c'; apply typeOf_preserves_valid_refs
    · intros tx c c'; apply typeOf_preserves_valid_refs
  | getAttr e _ =>
    apply typeOf_preserves_valid_refs_getAttr entities hty hrefs
    intros tx c c'; apply typeOf_preserves_valid_refs
  | hasAttr e _ =>
    apply typeOf_preserves_valid_refs_hasAttr entities hty hrefs
    intros tx c c'; apply typeOf_preserves_valid_refs
  | extHasAttr e _ _ =>
    simp only [typeOf] at hty
    cases hrefs with | extHasAttr_valid hrefs =>
    cases hty₁ : typeOf e c₁ Γ with
    | error => simp [hty₁] at hty
    | ok r₁ =>
      have ⟨tx₁, c₃⟩ := r₁
      simp only [hty₁, bind, Except.bind] at hty
      split at hty
      · simp at hty
      · simp [ok] at hty
        obtain ⟨hty_eq, _⟩ := hty
        simp only [←hty_eq, TypedExpr.toExpr]
        exact .extHasAttr_valid (typeOf_preserves_valid_refs entities hty₁ hrefs)
  | set s =>
    apply typeOf_preserves_valid_refs_set entities hty hrefs
    intros x hmem_x tx c c'
    apply typeOf_preserves_valid_refs
  | all x₁ p =>
    have ⟨_, _, tyr, cr, τ, htr, _, htyeq⟩ := type_of_all_inversion hty
    subst htyeq
    cases hrefs with
    | all_valid hrecv hpred =>
      simp only [TypedExpr.toExpr]
      exact Expr.ValidRefs.all_valid (typeOf_preserves_valid_refs entities htr hrecv) (normalize_validRefs hpred)
  | call _ args =>
    apply typeOf_preserves_valid_refs_call entities hty hrefs
    intros arg hmem_arg tx c c'
    apply typeOf_preserves_valid_refs
  | record rec =>
    apply typeOf_preserves_valid_refs_record entities hty hrefs
    intros attr hmem_attr tx c c'
    apply typeOf_preserves_valid_refs
termination_by sizeOf expr
decreasing_by
  any_goals simp [*]; omega
  · simp [*]
    have := List.sizeOf_lt_of_mem hmem_x
    omega
  · simp [*]
    have := List.sizeOf_lt_of_mem hmem_attr
    cases attr
    simp at this ⊢
    omega
  · simp [*]
    have := List.sizeOf_lt_of_mem hmem_arg
    omega

end Cedar.Thm
