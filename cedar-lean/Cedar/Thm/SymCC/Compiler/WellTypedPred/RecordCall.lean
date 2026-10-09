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

import Cedar.Thm.Data.Map
import Cedar.Thm.Data.List
import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.Tactics
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.ofType

/-!
D-72 step (3), recursive list arms of `compilePred_well_typed`: the `.record` and
`.call` arms. These mirror the scalar `compile_well_typed_record` /
`compile_well_typed_call` (Thm/SymCC/Compiler/WellTyped.lean), but drive the
sub-predicate typing from a per-element list hypothesis (the induction hypotheses
the dispatcher supplies) rather than a `cases hwt` on `TypedExpr.WellTyped`
evidence, which the predicate well-typedness relation does not carry.

This file is standalone (it does NOT import the still-red `compilePred_well_typed`
dispatcher in WellTyped.lean); the integrator imports it.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

/--
D-72 step (3), `.record` arm (mirror of `compile_well_typed_record`). The per-field
induction hypothesis is supplied as a `Forall₂` between the predicate fields `axs`
and the typed-field list `atys` that `typeOfPred (.record axs)` produced: each pair
`⟨(a, x), (a', ty)⟩` has `a = a'` and `x` compiles to a `.option (ofType ty.typeOf)`
term. From `typeOfPred (.record axs) = .ok (typ, c')`, `typ.typeOf` is already
`.record (Map.make (atys.map (λ (a, ty) => (a, .required ty.typeOf))))` by
construction, so the type reconciliation mirrors the scalar record arm with that
map playing the role of the scalar's `hrty`.
-/
theorem compilePred_well_typed_record
    {axs : List (Attr × Cedar.Spec.PredExpr)} {atys : List (Attr × TypedExpr)}
    {typ : TypedExpr} {Γ : TypeEnv} {it : Term}
    (ih : List.Forall₂ (λ ax aty => ax.fst = aty.fst ∧
      ∃ t, compilePred ax.snd it (SymEnv.ofEnv Γ) = .ok t ∧
        t.typeOf = .option (TermType.ofType aty.snd.typeOf) ∧
        t.WellFormed (SymEnv.ofEnv Γ).entities) axs atys)
    (htyp : typ = .record atys
      (.record (Map.make (atys.map (λ (a, ty) => (a, Qualified.required ty.typeOf)))))) :
    ∃ t, compilePred (.record axs) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType typ.typeOf) := by
  subst htyp
  simp only [TypedExpr.typeOf, TermType.ofType]
  -- All fields compile successfully.
  have ⟨tcomp_xs, hcomp_xs⟩ :
    ∃ ats : List (Attr × Term),
      List.mapM (fun (p : Attr × Cedar.Spec.PredExpr) =>
        (do Except.ok (p.fst, ← compilePred p.snd it (SymEnv.ofEnv Γ)) : SymCC.Result (Attr × Term))) axs
        = Except.ok ats := by
    apply List.all_ok_implies_mapM_ok
    intro p hx
    have ⟨aty, _, _, t, hcomp, _⟩ := List.forall₂_implies_all_left ih p hx
    exact ⟨(p.fst, t), by simp only [hcomp, Except.bind_ok]⟩
  -- Reduce the compile side to the `mapM`.
  simp only [compilePred, compileRecord]
  simp only [do_eq_ok, Except.ok.injEq]
  rw [List.mapM₂_eq_mapM λ (p : Attr × Cedar.Spec.PredExpr) =>
    (do Except.ok (p.fst, ← compilePred p.snd it (SymEnv.ofEnv Γ)) : SymCC.Result (Attr × Term))]
  -- Association between the typed fields `atys` and the compiled terms `tcomp_xs`.
  have hassoc_comp_xs_simp :
    List.Forallᵥ
      (λ (ty : TypedExpr) (t : Term) =>
        TermType.ofQualifiedType (Qualified.required ty.typeOf) =
        (Factory.option.get t).typeOf)
      atys tcomp_xs := by
    simp only [List.Forallᵥ]
    -- axs ↔ atys (ih) composed with axs ↔ tcomp_xs (hcomp_xs)
    have hat : List.Forall₂
        (λ (ax : Attr × Cedar.Spec.PredExpr) (t : Attr × Term) =>
          (do Except.ok (ax.fst, ← compilePred ax.snd it (SymEnv.ofEnv Γ)) : SymCC.Result (Attr × Term)) = .ok t)
        axs tcomp_xs := by
      apply List.mapM_implies_forall₂ _ hcomp_xs
      intro x y _ h; exact h
    apply List.forall₂_trans_ish ih hat
    intro ax aty t hih hcomp
    obtain ⟨hfst, tc, hcompx, htyx, hwfx⟩ := hih
    simp only [hcompx, Except.bind_ok, Except.ok.injEq] at hcomp
    have htfst : t.fst = ax.fst := by simp [← hcomp]
    have htsnd : t.snd = tc := by simp [← hcomp]
    refine ⟨by rw [htfst]; exact hfst.symm, ?_⟩
    simp only [TermType.ofQualifiedType, htsnd]
    exact Eq.symm (wf_option_get hwfx htyx).right
  -- Swap the association to the `recordOf`-friendly form.
  have hassoc_comp_xs :
    List.Forallᵥ
      (λ (t : Term) (ty : QualifiedType) => t.typeOf = TermType.ofQualifiedType ty)
      (List.map (fun x => (x.fst, Factory.option.get x.snd)) tcomp_xs)
      (List.map (fun x => (x.fst, Qualified.required x.snd.typeOf)) atys) := by
    apply List.forall₂_swap
    apply List.map_preserves_forall₂
    rotate_left
    · simp only [List.Forallᵥ] at hassoc_comp_xs_simp
      apply hassoc_comp_xs_simp
    · simp only [and_imp, Prod.forall]
      intros k1 x k2 y hkeq h
      simp [hkeq, h]
  -- Each compiled term and its `option.get` is well-formed.
  have hwf_comp_xs :
    ∀ (y : Term), y ∈ List.map Prod.snd tcomp_xs →
    Term.WellFormed (SymEnv.ofEnv Γ).entities y ∧
    Term.WellFormed (SymEnv.ofEnv Γ).entities (Factory.option.get y) := by
    simp only [List.mem_map, Prod.exists, exists_eq_right, forall_exists_index]
    intros y k hy
    have ⟨p, hx, hy⟩ := List.mapM_ok_implies_all_from_ok hcomp_xs (k, y) hy
    have ⟨aty, _, _, tc, hcompx, htyx, hwfx⟩ := List.forall₂_implies_all_left ih p hx
    simp only [hcompx, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hy
    simp only [hy.2] at hwfx htyx
    simp only [hwfx, true_and]
    exact (wf_option_get hwfx htyx).left
  -- Discharge the existential (compile succeeds) and the record type.
  simp only [hcomp_xs, Factory.someOf, Except.ok.injEq, exists_eq_left']
  apply (wf_ifAllSome (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_ ?_).right
  · intros g hg
    exact (hwf_comp_xs g hg).left
  · constructor
    apply wf_recordOf
    simp only [
      List.mem_map, Prod.exists, Prod.map_apply,
      id_eq, Prod.mk.injEq, forall_exists_index,
      and_imp,
    ]
    intros k y k2 y2 hy hk_to_k2 hopt_y
    simp only [← hopt_y]
    simp only [List.mem_map, Prod.exists, exists_eq_right, forall_exists_index] at hwf_comp_xs
    exact (hwf_comp_xs y2 k2 hy).right
  · simp only [
      Factory.recordOf, Data.Map.make, Term.typeOf,
      TypedExpr.typeOf, TermType.ofType,
      TermType.option.injEq, TermType.record.injEq,
    ]
    rw [Map.mapOnValues₂_eq_mapOnValues _ Term.typeOf]
    simp only [Map.mapOnValues, Map.toList_mk_id, Map.mk.injEq]
    rw [ofRecordType_as_map]
    simp only [Data.Map.make]
    apply List.forall₂_iff_map_eq.mp
    apply List.Forall₂.imp
    rotate_left
    · apply List.canonicalize_preserves_forallᵥ
      apply hassoc_comp_xs
    · simp

/-- From `tys.map typeOf = [T]` and the per-arg relation, recover `ts = [t]`. -/
private theorem call_ts_one {Γ : TypeEnv}
    {tys : List TypedExpr} {ts : List Term} {T : CedarType}
    (hmap : tys.map TypedExpr.typeOf = [T])
    (hrel : List.Forall₂ (λ (ty : TypedExpr) (t : Term) =>
      t.typeOf = .option (TermType.ofType ty.typeOf) ∧
      t.WellFormed (SymEnv.ofEnv Γ).entities) tys ts) :
    ∃ t, ts = [t] ∧ t.typeOf = .option (TermType.ofType T) ∧
      t.WellFormed (SymEnv.ofEnv Γ).entities := by
  match tys, ts, hrel with
  | [ty], [t], .cons h .nil =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
    subst hmap
    exact ⟨t, rfl, h.left, h.right⟩

/-- From `tys.map typeOf = [T₁, T₂]` and the per-arg relation, recover `ts = [t₁, t₂]`. -/
private theorem call_ts_two {Γ : TypeEnv}
    {tys : List TypedExpr} {ts : List Term} {T₁ T₂ : CedarType}
    (hmap : tys.map TypedExpr.typeOf = [T₁, T₂])
    (hrel : List.Forall₂ (λ (ty : TypedExpr) (t : Term) =>
      t.typeOf = .option (TermType.ofType ty.typeOf) ∧
      t.WellFormed (SymEnv.ofEnv Γ).entities) tys ts) :
    ∃ t₁ t₂, ts = [t₁, t₂] ∧
      t₁.typeOf = .option (TermType.ofType T₁) ∧ t₁.WellFormed (SymEnv.ofEnv Γ).entities ∧
      t₂.typeOf = .option (TermType.ofType T₂) ∧ t₂.WellFormed (SymEnv.ofEnv Γ).entities := by
  match tys, ts, hrel with
  | [ty₁, ty₂], [t₁, t₂], .cons h₁ (.cons h₂ .nil) =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
    obtain ⟨he₁, he₂⟩ := hmap
    subst he₁; subst he₂
    exact ⟨t₁, t₂, rfl, h₁.left, h₁.right, h₂.left, h₂.right⟩

/--
`typeOfCall` success depends on the argument-expr list only through the
`[.lit (.string s)]` test in its `.decimal/.ip/.datetime/.duration` constructor arms;
every other arm matches on `tys.map typeOf` alone (its `_ => err` branch reads the args
only in the error payload, which the `.ok` hypothesis never reaches). So two argument
lists that agree on that test give the same `typeOfCall` result on the `.ok` side. Here
the two lists are `L` (source) and `L'` (per-argument normalized), related elementwise by
`.lit` agreement (`normalize` is the identity on `.lit`).
-/
theorem typeOfCall_arg_lit_agree_ok
    {xfn : ExtFun} {tys : List TypedExpr} {L L' : List Cedar.Spec.Expr}
    {typ : TypedExpr} {c' : Capabilities}
    (hagree : List.Forall₂ (λ e e' => ∀ p, e = .lit p ↔ e' = .lit p) L L')
    (htp : typeOfCall xfn tys L = .ok (typ, c')) :
    typeOfCall xfn tys L' = .ok (typ, c') := by
  -- On the `.ok` side, `typeOfConstructor` reads the args only via `[.lit (.string s)]`,
  -- on which the two lists agree, so a success carries from `L` to `L'`.
  have hconstr : ∀ {α : Type} (mk : String → Option α) (ty : CedarType) (r : CedarType × Capabilities),
      typeOfConstructor mk L ty = .ok r → typeOfConstructor mk L' ty = .ok r := by
    intro α mk ty r hok
    -- `typeOfConstructor` succeeds only on `[.lit (.string s)]`.
    have hLshape : ∃ s, L = [.lit (.string s)] := by
      unfold typeOfConstructor at hok
      split at hok <;>
        first
          | (rename_i s _; exact ⟨s, rfl⟩)
          | (rename_i s; exact ⟨s, rfl⟩)
          | simp only [Validation.err, Validation.ok, reduceCtorEq] at hok
    obtain ⟨s, hLeq⟩ := hLshape
    -- Agreement then forces `L' = [.lit (.string s)]`.
    subst hLeq
    cases hagree with
    | cons h0 htl =>
      rename_i e' Ltl'
      cases htl with
      | nil =>
        have he' : e' = .lit (.string s) := (h0 (.string s)).mp rfl
        subst he'
        exact hok
  unfold typeOfCall at htp ⊢
  -- The `L`/`L'` dependence sits inside `typeOfConstructor` (the four constructor arms)
  -- or the dead `_ => err` payload (every other arm). Reverting the hypothesis places both
  -- `typeOfCall` occurrences under one goal; `split` on the shared `(xfn, tys.map typeOf)`
  -- discriminant reduces them together into aligned arms. Constructor arms are bridged by
  -- `hconstr`; type-only arms become `… = ok → … = ok` (identical); `err` arms are
  -- impossible against the `.ok` hypothesis.
  revert htp
  split <;> intro htp <;>
    first
      | exact htp
      | (simp only [bind, Except.bind] at htp ⊢
         split at htp <;> rename_i heqc <;>
           first
             | (rw [hconstr _ _ _ heqc]; exact htp)
             | (simp only [reduceCtorEq] at htp))
      | nomatch htp

/--
induction hypothesis is a `Forall₂` between the argument predicates `xs` and the
typed arguments `tys` that `typeOfPred (.call xfn xs)` produced. `typeOfCall`'s
success pins the operand types (via the matched `tys.map TypedExpr.typeOf` pattern)
and the result type `typ` (via its `let ok ty := ok (.call xfn tys ty)`), from which
`compileCall` succeeds with the matching `.option` type.
-/
theorem compilePred_well_typed_call
    {xfn : ExtFun} {xs : List Cedar.Spec.PredExpr} {tys : List TypedExpr}
    {typ : TypedExpr} {c' : Capabilities} {Γ : TypeEnv} {it : Term}
    (ih : List.Forall₂ (λ x ty =>
      ∃ t, compilePred x it (SymEnv.ofEnv Γ) = .ok t ∧
        t.typeOf = .option (TermType.ofType ty.typeOf) ∧
        t.WellFormed (SymEnv.ofEnv Γ).entities) xs tys)
    (htp : typeOfCall xfn tys (xs.map₁ (λ ⟨x₁, _⟩ => x₁.toExpr)) = .ok (typ, c')) :
    ∃ t, compilePred (.call xfn xs) it (SymEnv.ofEnv Γ) = .ok t ∧
      t.typeOf = .option (TermType.ofType typ.typeOf) := by
  -- All arguments compile successfully.
  have ⟨ts, hcomp_ts⟩ :
    ∃ ts : List Term,
      List.mapM (fun (x : Cedar.Spec.PredExpr) => compilePred x it (SymEnv.ofEnv Γ)) xs
        = Except.ok ts := by
    apply List.all_ok_implies_mapM_ok
    intro x hx
    have ⟨ty, _, t, hcomp, _⟩ := List.forall₂_implies_all_left ih x hx
    exact ⟨t, hcomp⟩
  -- Forall₂ relating xs to the compiled argument terms ts.
  have hxts : List.Forall₂ (λ x t => compilePred x it (SymEnv.ofEnv Γ) = .ok t) xs ts :=
    List.mapM_implies_forall₂ (fun _ _ _ h => h) hcomp_ts
  -- Compose with ih to get: Forall₂ relating tys to ts (compiled term types).
  have htys_ts : List.Forall₂
      (λ (ty : TypedExpr) (t : Term) =>
        t.typeOf = .option (TermType.ofType ty.typeOf) ∧ t.WellFormed (SymEnv.ofEnv Γ).entities)
      tys ts := by
    apply List.forall₂_trans_ish ih hxts
    intro x ty t hih hcomp
    obtain ⟨tc, hcompx, htyx, hwfx⟩ := hih
    rw [hcompx] at hcomp
    simp only [Except.ok.injEq] at hcomp
    subst hcomp
    exact ⟨htyx, hwfx⟩
  -- Reduce the compile side.
  simp only [compilePred]
  rw [List.mapM₁_eq_mapM (fun x => compilePred x it (SymEnv.ofEnv Γ))]
  simp only [hcomp_ts, Except.bind_ok]
  -- Extract operand types and result type from `typeOfCall` success.
  unfold typeOfCall at htp
  simp only at htp
  -- Helpers to pin `ts` from `tys.map typeOf = <concrete list>` plus `htys_ts`.
  split at htp
  case h_5 | h_6 | h_7 | h_8 | h_13 | h_14 | h_15 =>
    rename_i xfn' xtys heq
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨htyp, -⟩ := htp
    subst htyp
    obtain ⟨t₁, t₂, hts, hty₁, hwf₁, hty₂, hwf₂⟩ := call_ts_two heq htys_ts
    subst hts
    simp only [TypedExpr.typeOf, TermType.ofType] at hty₁ hty₂ ⊢
    simp only [compileCall, compileCall₂, compileCallWithError₂, hty₁, hty₂,
      decide_true, Bool.and_self, ↓reduceIte, Factory.someOf,
      Except.ok.injEq, exists_eq_left']
    apply typeOf_ifSome_option
    apply typeOf_ifSome_option
    try simp only [Term.typeOf, TermType.option.injEq]
    first
      | apply (wf_decimal_lessThan (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_).right
      | apply (wf_decimal_lessThanOrEqual (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_).right
      | apply (wf_decimal_greaterThan (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_).right
      | apply (wf_decimal_greaterThanOrEqual (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_).right
      | apply (wf_ipaddr_isInRange (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_).right
      | apply (wf_datetime_offset (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_).right
      | apply (wf_datetime_durationSince (εs := (SymEnv.ofEnv Γ).entities) ?_ ?_).right
    all_goals
      apply wf_option_get
      · assumption
      · simp only [hty₁, hty₂, TermType.ofType]
  case h_9 | h_10 | h_11 | h_12 | h_16 | h_17 | h_18 | h_19 | h_20 | h_21 | h_22 =>
    rename_i xfn' xtys heq
    simp only [Validation.ok, Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨htyp, -⟩ := htp
    subst htyp
    obtain ⟨t₁, hts, hty₁, hwf₁⟩ := call_ts_one heq htys_ts
    subst hts
    simp only [TypedExpr.typeOf, TermType.ofType] at hty₁ ⊢
    simp only [compileCall, compileCall₁, compileCallWithError₁, hty₁,
      TermType.ofType, ↓reduceIte, Factory.someOf,
      Except.ok.injEq, exists_eq_left']
    apply typeOf_ifSome_option
    try simp only [Term.typeOf, TermType.option.injEq]
    first
      | apply (wf_ipaddr_isIpv4 (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_ipaddr_isIpv6 (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_ipaddr_isLoopback (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_ipaddr_isMulticast (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_datetime_toDate (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_datetime_toTime (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_duration_toMilliseconds (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_duration_toSeconds (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_duration_toMinutes (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_duration_toHours (εs := (SymEnv.ofEnv Γ).entities) ?_).right
      | apply (wf_duration_toDays (εs := (SymEnv.ofEnv Γ).entities) ?_).right
    apply wf_option_get
    · assumption
    · simp only [hty₁, TermType.ofType]
  case h_23 =>
    simp only [Validation.err, reduceCtorEq] at htp
  case h_1 | h_2 | h_3 | h_4 =>
    simp only [typeOfConstructor, Validation.ok, Validation.err, bind, Except.bind] at htp
    split at htp <;> rename_i heq <;> try (simp only [reduceCtorEq] at htp)
    -- ok leaf: `heq : (match xs.map₁ toExpr with …) = .ok v`, `htp : .ok (.call … v.fst, v.snd) = .ok (typ,c')`.
    simp only [Except.ok.injEq, Prod.mk.injEq] at htp
    obtain ⟨htyp, -⟩ := htp
    -- Peel `heq`'s nested matches to pin `v.fst` and the argument shape.
    split at heq <;> try (simp only [reduceCtorEq] at heq)
    rename_i hmk
    split at heq <;> try (simp only [reduceCtorEq] at heq)
    rename_i s v hmkv
    simp only [Except.ok.injEq] at heq
    subst heq
    simp only at htyp
    subst htyp
    -- `hmk : xs.map₁ (·.toExpr) = [.lit (.string s)]`, so `xs = [.lit (.string s)]`.
    rw [List.map₁_eq_map] at hmk
    rcases xs with _ | ⟨x₀, rest⟩
    · simp only [List.map_nil, reduceCtorEq] at hmk
    simp only [List.map_cons, List.cons.injEq] at hmk
    obtain ⟨hx₀, hrest⟩ := hmk
    simp only [List.map_eq_nil_iff] at hrest
    subst hrest
    -- Compiled list is a singleton too.
    obtain ⟨t₁, tail, ht₁, htail, hts⟩ := List.forall₂_cons_left_iff.mp hxts
    rw [List.forall₂_nil_left_iff] at htail
    subst htail
    subst hts
    -- `x₀.toExpr = .lit (.string s)` ⇒ `x₀ = .lit (.string s)`.
    cases x₀ <;>
      simp only [PredExpr.toExpr, itExpr, reduceCtorEq, Expr.lit.injEq, Prim.string.injEq] at hx₀
    subst hx₀
    simp only [compilePred, compilePrim, Factory.someOf, Except.ok.injEq] at ht₁
    subst ht₁
    simp only [compileCall, compileCall₀, hmkv, Factory.someOf, Except.ok.injEq, exists_eq_left']
    simp only [TypedExpr.typeOf, TermType.ofType]
    rw [typeOf_term_some]
    simp only [TermType.option.injEq]
    first
      | exact typeOf_term_prim_ext_decimal
      | exact typeOf_term_prim_ext_ipaddr
      | exact typeOf_term_prim_ext_datetime
      | exact typeOf_term_prim_ext_duration

end Cedar.Thm
