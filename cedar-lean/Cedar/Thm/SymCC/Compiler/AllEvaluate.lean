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
import Cedar.Thm.SymCC.Compiler.CompilePredEvaluate
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Term.Same
import Cedar.Thm.Data.Set

/-!
Step D: `compile_evaluate_all`, the `.all` arm of `compile_evaluate`.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC Cedar.SymCC.Factory

/-- A term whose `value?` succeeds is a literal. -/
theorem value?_some_implies_isLiteral {t : Term} {v : Value} :
    t.value? = some v → t.isLiteral = true := by
  intro hv
  induction t using Term.value?.induct generalizing v
  case motive1 _ tᵢ =>
    exact (∀ vᵢ, tᵢ.value? = .some vᵢ → tᵢ.isLiteral = true)
  case case1 | case2 =>
    simp only [Term.value?, false_implies, implies_true, reduceCtorEq]
  case case3 ih =>
    intro v hv
    exact ih hv
  case case4 =>
    simp only [Term.isLiteral]
  case case5 ih =>
    simp only [Term.isLiteral, Cedar.Data.Set.all₁_eq_all, Cedar.Data.Set.all_eq_true]
    intro ti hti
    rename_i s _
    rw [Term.value?] at hv
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    replace ⟨vs', hv, _⟩ := hv
    simp only [List.mapM₁_eq_mapM Term.value?, ← List.mapM'_eq_mapM] at hv
    rw [← Cedar.Data.Set.mem_elts_iff_mem_set] at hti
    replace ⟨vi, hvi⟩ := List.mapM'_some_implies_all_some hv ti hti
    exact ih ti hti hvi.2
  case case6 ih =>
    rename_i ats
    rw [Term.isLiteral, List.all_attach₂_snd, List.all_eq_true]
    intro x hx
    obtain ⟨xa, xt⟩ := x
    simp only at *
    have hsz : sizeOf xt < 1 + sizeOf ats.toList := by
      have := List.sizeOf_snd_lt_sizeOf_list hx
      simp only at this; omega
    -- extract attrValue? xa xt = some _ for this attr from hv
    rw [Term.value?] at hv
    simp only [List.mapM₂_eq_mapM λ x : Attr × Term => Term.value?.attrValue? x.fst x.snd,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    replace ⟨avs, hm, _⟩ := hv
    replace ⟨pv, _, hav⟩ := List.mapM_some_implies_all_some hm (xa, xt) hx
    -- hav : attrValue? xa xt = some pv
    cases hxs : xt with
    | «some» t' =>
      rw [hxs] at hav
      simp only [Term.value?.attrValue?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hav
      obtain ⟨vv, hvv, _⟩ := hav
      rw [Term.isLiteral]
      exact ih xa t' (by rw [hxs] at hsz; simp only [Term.some.sizeOf_spec] at hsz; omega) vv hvv
    | «none» tty =>
      exact isLiteral_none
    | _ =>
      rw [hxs] at hav
      simp only [Term.value?.attrValue?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hav
      obtain ⟨vv, hvv, _⟩ := hav
      exact ih xa _ (by rw [hxs] at hsz; exact hsz) vv hvv
  case case7 =>
    simp only [Term.value?, reduceCtorEq] at hv

/-- The compiler's `anyErr` fold over a list of WF `.option .bool` literal predicate terms
is itself a `.bool` literal. -/
theorem foldr_anyErr_lit {εs : SymEntities} {pairs : List (Term × Spec.Result Bool)}
    (hwf : ∀ pr ∈ pairs, (pr.1).WellFormedLiteral εs ∧ (pr.1).typeOf = .option .bool) :
    ∃ ge, pairs.foldr (fun pr acc => Factory.or (Factory.not (Factory.isSome pr.1)) acc) (false : Term)
        = Term.prim (.bool ge) := by
  induction pairs with
  | nil => exact ⟨false, rfl⟩
  | cons pr rest ih =>
    have hwfhd := hwf pr (by simp only [List.mem_cons, true_or])
    obtain ⟨ge, hge⟩ := ih (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
    simp only [List.foldr_cons, hge]
    rcases wfl_of_type_option_is_option ⟨hwfhd.1.1, hwfhd.1.2⟩ hwfhd.2 with hnone | ⟨t', hsome, _⟩
    · exact ⟨true, by simp only [hnone, pe_isSome_none, pe_not_false, pe_or_true_left]⟩
    · exact ⟨ge, by simp only [hsome, pe_isSome_some, pe_not_true, pe_or_false_left]⟩

/-- Fold reconciliation: the compiler's per-element `conj`/`anyErr` fold reconciles
with `evalAll`'s `mapM (·.as Bool)` collapse, element-wise. -/
theorem all_fold_reconcile {εs : SymEntities} {pairs : List (Term × Spec.Result Bool)}
    (hwf : ∀ pr ∈ pairs, (pr.1).WellFormedLiteral εs ∧ (pr.1).typeOf = .option .bool)
    (hsame : ∀ pr ∈ pairs, SameResults (pr.2.map (Value.prim ∘ Prim.bool)) pr.1) :
    SameResults
      (match pairs.mapM Prod.snd with
        | .error _ => .error .quantifierError
        | .ok bs => .ok (Value.prim (.bool (bs.all id))))
      (Factory.ite
        (pairs.foldr (fun pr acc => Factory.or (Factory.not (Factory.isSome pr.1)) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (pairs.foldr (fun pr acc => Factory.and (Factory.option.get pr.1) acc) (true : Term)))) := by
  induction pairs with
  | nil =>
    simp only [List.mapM_nil, List.foldr_nil, pe_ite_false, Factory.someOf]
    exact same_ok_bool
  | cons pr rest ih =>
    have hwfhd := hwf pr (by simp only [List.mem_cons, true_or])
    have hshd := hsame pr (by simp only [List.mem_cons, true_or])
    have ihrest := ih (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
                      (fun p hp => hsame p (List.mem_cons_of_mem _ hp))
    obtain ⟨ger, hger⟩ := foldr_anyErr_lit (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
    simp only [List.foldr_cons]
    cases hrb : pr.2 with
    | error e =>
      rw [hrb] at hshd
      simp only [Except.map, SameResults] at hshd
      obtain ⟨ty, hnoneq⟩ : ∃ ty, pr.1 = Term.none ty := by
        cases hpt : pr.1 <;> simp only [hpt, SameResults] at hshd
        exact ⟨_, rfl⟩
      rw [List.mapM_cons, hrb]
      simp only [Except.bind_err, hnoneq, pe_isSome_none, pe_not_false,
        pe_or_true_left, pe_ite_true, Factory.noneOf]
      exact same_error_implied_by (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    | ok b =>
      rw [hrb] at hshd
      have hbt : (Except.ok (Value.prim (.bool b)) : Spec.Result Value) ∼ pr.1 := by
        simp only [Except.map, Function.comp] at hshd; exact hshd
      have ht : pr.1 = Term.some (.prim (.bool b)) := same_ok_bool_implies hbt
      rw [List.mapM_cons, hrb]
      simp only [Except.bind_ok, ht, pe_isSome_some, pe_not_true, pe_or_false_left,
        pe_option_get_some, hger]
      -- guard is literal `ger`; case on it
      cases ger with
      | «true» =>
        -- anyErr_rest = true ⇒ ihrest's ite = noneOf ⇒ its LHS is an error ⇒ mapM rest errors
        simp only [hger, pe_ite_true] at ihrest
        rw [pe_ite_true]
        cases hmr : List.mapM Prod.snd rest with
        | error e =>
          simp only [hmr, Except.bind_err, Factory.noneOf]
          exact same_error_implied_by (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
        | ok bs =>
          rw [hmr] at ihrest
          simp only [hmr, Factory.noneOf, SameResults, reduceCtorEq] at ihrest
      | «false» =>
        simp only [hger, pe_ite_false] at ihrest ⊢
        -- anyErr_rest = false ⇒ ihrest : (mapM rest result) ∼ someOf conj_rest
        cases hmr : List.mapM Prod.snd rest with
        | error e =>
          rw [hmr] at ihrest
          simp only [hmr, Factory.someOf, SameResults] at ihrest
        | ok bs =>
          rw [hmr] at ihrest
          simp only [hmr, Factory.someOf, List.all_cons] at ihrest ⊢
          replace ihrest := same_ok_some_implies ihrest
          cases b with
          | «true» =>
            simp only [pe_and_true_left, Bool.true_and]
            exact same_ok_some_iff.mpr ihrest
          | «false» =>
            simp only [pe_and_false_left, Bool.false_and]
            exact same_ok_bool



/-- Membership characterization of the compiler's `.all` fold over `pairs` (first projection = the
compiled per-element predicate terms; second = the concrete `.as Bool` results). It is `noneOf .bool`
exactly when some pair's result errors, else `someOf (.bool (decide (∀ pairs ok-true)))`. -/
theorem all_fold_mem_char {εs : SymEntities} {pairs : List (Term × Spec.Result Bool)}
    (hwf : ∀ pr ∈ pairs, (pr.1).WellFormedLiteral εs ∧ (pr.1).typeOf = .option .bool)
    (hsame : ∀ pr ∈ pairs, SameResults (pr.2.map (Value.prim ∘ Prim.bool)) pr.1) :
    (∃ pr ∈ pairs, ∀ b, pr.2 ≠ .ok b) ∧
      Factory.ite
        (pairs.foldr (fun pr acc => Factory.or (Factory.not (Factory.isSome pr.1)) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (pairs.foldr (fun pr acc => Factory.and (Factory.option.get pr.1) acc) (true : Term)))
        = Factory.noneOf .bool
    ∨ (∀ pr ∈ pairs, ∃ b, pr.2 = .ok b) ∧
      Factory.ite
        (pairs.foldr (fun pr acc => Factory.or (Factory.not (Factory.isSome pr.1)) acc) (false : Term))
        (Factory.noneOf .bool)
        (Factory.someOf (pairs.foldr (fun pr acc => Factory.and (Factory.option.get pr.1) acc) (true : Term)))
        = Factory.someOf (.prim (.bool (decide (∀ pr ∈ pairs, pr.2 = .ok true)))) := by
  induction pairs with
  | nil =>
    right
    refine ⟨by simp, ?_⟩
    simp only [List.foldr_nil, pe_ite_false, Factory.someOf, List.not_mem_nil, false_implies,
      implies_true, decide_true]
  | cons pr rest ih =>
    have hwfhd := hwf pr (by simp only [List.mem_cons, true_or])
    have hshd := hsame pr (by simp only [List.mem_cons, true_or])
    obtain ⟨ger, hger⟩ := foldr_anyErr_lit (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
    simp only [List.foldr_cons]
    cases hrb : pr.2 with
    | error e =>
      -- head errors ⇒ pr.1 = .none ⇒ anyErr head true ⇒ ite = noneOf
      rw [hrb] at hshd
      simp only [Except.map, SameResults] at hshd
      obtain ⟨ty, hnoneq⟩ : ∃ ty, pr.1 = Term.none ty := by
        cases hpt : pr.1 <;> simp only [hpt, SameResults] at hshd
        exact ⟨_, rfl⟩
      left
      refine ⟨⟨pr, by simp only [List.mem_cons, true_or], ?_⟩, ?_⟩
      · intro b hb; rw [hrb] at hb; simp only [reduceCtorEq] at hb
      · simp only [hnoneq, pe_isSome_none, pe_not_false, pe_or_true_left, pe_ite_true, Factory.noneOf]
    | ok b =>
      rw [hrb] at hshd
      have hbt : (Except.ok (Value.prim (.bool b)) : Spec.Result Value) ∼ pr.1 := by
        simp only [Except.map, Function.comp] at hshd; exact hshd
      have ht : pr.1 = Term.some (.prim (.bool b)) := same_ok_bool_implies hbt
      have ihr := ih (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
                     (fun p hp => hsame p (List.mem_cons_of_mem _ hp))
      simp only [ht, pe_isSome_some, pe_not_true, pe_or_false_left, pe_option_get_some]
      rcases ihr with ⟨⟨pr', hpr'mem, hpr'err⟩, hite⟩ | ⟨hallok, hite⟩
      · -- some tail pair errors ⇒ anyErr tail true (foldr_anyErr_lit says it is a bool literal; and the
        -- ite collapses to noneOf regardless of the head's conj contribution)
        left
        refine ⟨⟨pr', by simp only [List.mem_cons, hpr'mem, or_true], hpr'err⟩, ?_⟩
        -- the tail ite is noneOf; same guard here ⇒ noneOf
        obtain ⟨ge, hge⟩ := foldr_anyErr_lit (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
        rw [hge] at hite ⊢
        cases ge with
        | «true» => simp only [pe_ite_true, Factory.noneOf]
        | «false» => simp only [pe_ite_false, Factory.someOf, Factory.noneOf, reduceCtorEq] at hite
      · -- all tail ok
        obtain ⟨ge, hge⟩ := foldr_anyErr_lit (fun p hp => hwf p (List.mem_cons_of_mem _ hp))
        rw [hge] at hite ⊢
        cases ge with
        | «true» => simp only [pe_ite_true, Factory.someOf, Factory.noneOf, reduceCtorEq] at hite
        | «false» =>
          right
          refine ⟨?_, ?_⟩
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hqt
            · exact ⟨b, hrb⟩
            · exact hallok q hqt
          · simp only [pe_ite_false, Factory.someOf] at hite ⊢
            simp only [Term.some.injEq] at hite ⊢
            -- conj = and (bool b) tailConj ; tailConj = someOf-inner from hite = bool (decide ∀ tail ok-true)
            rw [hite]
            cases b with
            | «true» =>
              simp only [pe_and_true_left]
              congr 1; congr 1
              simp only [eq_iff_iff, decide_eq_decide, Bool.true_eq, List.mem_cons]
              constructor
              · intro h q hq; rcases hq with rfl | hqt
                · exact hrb
                · exact h q hqt
              · intro h; exact fun q hqt => h q (Or.inr hqt)
            | «false» =>
              simp only [pe_and_false_left]
              have hnot : ¬ (∀ q ∈ (pr :: rest), q.2 = Except.ok true) := by
                intro hall
                have h := hall pr (List.mem_cons_self ..)
                rw [hrb] at h
                simp only [Except.ok.injEq, Bool.false_eq_true] at h
              rw [decide_eq_false hnot]

/-- Membership characterization of `evalAll`: it errors (to `quantifierError`) exactly when some
element's `.as Bool` errors; otherwise it is `.ok (.bool b)` where `b` is true iff every element's
`.as Bool` is `.ok true`. -/
theorem evalAll_mem_char {s : Cedar.Data.Set Value} {f : Value → Spec.Result Value} :
    (∃ v ∈ s, ∀ b, (f v).as Bool ≠ .ok b) ∧ evalAll s f = .error .quantifierError
    ∨ (∀ v ∈ s, ∃ b, (f v).as Bool = .ok b) ∧
        evalAll s f = .ok (.prim (.bool (decide (∀ v ∈ s, (f v).as Bool = .ok true)))) := by
  simp only [evalAll, Cedar.Data.Set.toList]
  cases hm : s.elts.mapM (fun v => (f v).as Bool) with
  | error e =>
    left
    have ⟨v, hv, hve⟩ := List.mapM_error_implies_exists_error hm
    refine ⟨⟨v, (Cedar.Data.Set.mem_elts_iff_mem_set v s).mp hv, ?_⟩, ?_⟩
    · intro b hb; rw [hb] at hve; simp only [reduceCtorEq] at hve
    · simp only [Cedar.Data.Set.toList, hm]
  | ok bs =>
    right
    refine ⟨?_, ?_⟩
    · intro v hv
      have ⟨b, _, hb⟩ := List.mapM_ok_implies_all_ok hm v ((Cedar.Data.Set.mem_elts_iff_mem_set v s).mpr hv)
      exact ⟨b, hb⟩
    · simp only [Cedar.Data.Set.toList, hm, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq]
      have hiff : (bs.all id = true) ↔ (∀ v ∈ s, (f v).as Bool = Except.ok true) := by
        simp only [List.all_eq_true, id]
        constructor
        · intro hall v hv
          have ⟨b, hbmem, hb⟩ := List.mapM_ok_implies_all_ok hm v ((Cedar.Data.Set.mem_elts_iff_mem_set v s).mpr hv)
          have := hall b hbmem
          subst this; exact hb
        · intro hall b hbmem
          have ⟨v, hv, hvb⟩ := List.mapM_ok_implies_all_from_ok hm b hbmem
          have := hall v ((Cedar.Data.Set.mem_elts_iff_mem_set v s).mp hv)
          rw [hvb] at this; simp only [Except.ok.injEq] at this; subst this; rfl
      by_cases hd : (∀ v ∈ s, (f v).as Bool = Except.ok true)
      · rw [decide_eq_true hd]; exact hiff.mpr hd
      · rw [decide_eq_false hd]
        cases hb : bs.all id with
        | «true» => exact absurd (hiff.mp hb) hd
        | «false» => rfl

/-- Extraction for a `do`-let followed by a Bool-type guard, as the compiler's per-element
`.all` body produces. -/
theorem guard_ok_implies {r : SymCC.Result Term} {pti' : Term} {P : Term → Prop} [DecidablePred P] {e : SymCC.Error}
    (h : (do let pti ← r; if P pti then Except.ok pti else Except.error e) = Except.ok pti') :
    r = Except.ok pti' ∧ P pti' := by
  cases r with
  | error e' => simp only [Except.bind_err, reduceCtorEq] at h
  | ok pti =>
    simp only [Except.bind_ok] at h
    split at h
    · rename_i hP; simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, hP⟩
    · simp only [reduceCtorEq] at h

/-- The `.all` arm of `compile_evaluate`. -/
theorem compile_evaluate_all {x₁ : Expr} {p : PredExpr} {env : Env} {εnv : SymEnv} {t : Term}
    (heq : env ∼ εnv)
    (hwe : env.WellFormedFor (.all x₁ p))
    (hwε : εnv.WellFormedFor (.all x₁ p))
    (hok : compile (.all x₁ p) εnv = .ok t)
    (ih₁ : CompileEvaluate x₁) :
    evaluate (.all x₁ p) env.request env.entities ∼ t := by
  have hwφ₁ : εnv.WellFormedFor x₁ := by
    refine ⟨hwε.left, ?_⟩
    have hv := hwε.right; cases hv with | all_valid hvx _ => exact hvx
  have hwe₁ : env.WellFormedFor x₁ := by
    refine ⟨hwe.left, ?_⟩
    have hv := hwe.right; cases hv with | all_valid hvx _ => exact hvx
  have hprefs : p.ValidRefs (fun uid => env.entities.contains uid) := by
    have hv := hwe.right; cases hv with | all_valid _ hp => exact hp
  rw [compile.eq_def] at hok
  simp only [] at hok
  split at hok
  · simp only [reduceCtorEq] at hok
  simp_do_let (compile x₁ εnv) at hok
  rename_i t₁ hr₁
  have ihr := ih₁ heq hwe₁ hwφ₁ hr₁
  unfold evaluate
  simp only [Result.as, Coe.coe]
  split at hok
  · rename_i ty
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    rename_i sty
    cases hx : evaluate x₁ env.request env.entities with
    | error e =>
      rw [hx] at ihr
      have ⟨hne, _⟩ := same_error_implies ihr
      simp only [Except.bind_err, Factory.noneOf]
      exact same_error_implied_by hne
    | ok v => rw [hx] at ihr; simp only [Same.same, SameResults] at ihr
  · rename_i _ hnotnone
    cases hx : evaluate x₁ env.request env.entities with
    | error e =>
      rw [hx] at ihr
      have ⟨_, ty', hnoneq⟩ := same_error_implies ihr
      exact absurd hnoneq (hnotnone ty')
    | ok v =>
      rw [hx] at ihr
      obtain ⟨t', hteq, hv'⟩ := same_ok_implies ihr
      subst hteq
      simp only [Factory.option.get, pe_option_get_some] at hok ⊢
      have htlit : t'.isLiteral = true := value?_some_implies_isLiteral (same_values_def.mp hv')
      have ht1wf := (compile_wf hwφ₁ hr₁).left
      have htwf : t'.WellFormed εnv.entities := wf_term_some_implies ht1wf
      split at hok
      case h_2 => simp only [reduceCtorEq] at hok
      case h_1 elemTy helem =>
        obtain ⟨s, hts⟩ := wfl_of_type_set_is_set ⟨htwf, htlit⟩ helem
        subst hts
        obtain ⟨vs⟩ := s
        obtain ⟨valueSet, hveq, hvalue?eq⟩ := same_set_term_implies hv'
        subst hveq
        have hvalue? : (Term.set (Cedar.Data.Set.mk vs) elemTy).value? = some (Value.set valueSet) :=
          same_values_def.mp hv'
        have hvslit : (vs.all (·.isLiteral)) = true := by
          have := htlit
          simp only [Term.isLiteral, Cedar.Data.Set.all₁_eq_all, Cedar.Data.Set.all_eq_true] at this
          simp only [List.all_eq_true]
          intro ti hti
          exact this ti ((Cedar.Data.Set.mem_elts_iff_mem_set ti (Cedar.Data.Set.mk vs)).mpr hti)
        simp only [hvslit, reduceIte] at hok
        generalize hpts : (vs.mapM _ : SymCC.Result (List Term)) = r at hok
        cases r with
        | error e => simp only [Except.bind_err, reduceCtorEq] at hok
        | ok pts =>
          simp only [Except.bind_ok, Except.ok.injEq] at hok
          subst hok
          rw [List.mapM_ok_iff_forall₂] at hpts
          simp only [Value.asSet, Except.bind_ok]
          -- per-element compilePred eqn + Bool-typed guard
          have helt : List.Forall₂ (fun ti pti =>
              compilePred p (Factory.someOf ti) εnv = .ok pti ∧ (Factory.option.get pti).typeOf = .bool) vs pts := by
            apply List.Forall₂.imp _ hpts
            intro ti pti hti
            exact guard_ok_implies hti
          have hvwf : (Value.set valueSet).WellFormed env.entities := evaluate_wf hwe₁ (by rw [hx])
          have heltvalwf : ∀ vi ∈ valueSet, vi.WellFormed env.entities := by
            cases hvwf with | set_wf h _ => exact h
          have helttermty : ∀ ti ∈ vs, ti.typeOf = elemTy := by
            cases htwf with | set_wf _ hty _ _ =>
            intro ti hti; exact hty ti ((Cedar.Data.Set.mem_elts_iff_mem_set ti (Cedar.Data.Set.mk vs)).mpr hti)
          have helttermwf : ∀ ti ∈ vs, ti.WellFormed εnv.entities := by
            cases htwf with | set_wf h _ _ _ =>
            intro ti hti; exact h ti ((Cedar.Data.Set.mem_elts_iff_mem_set ti (Cedar.Data.Set.mk vs)).mpr hti)
          let g : Term → Spec.Result Bool := fun pti =>
            match pti with | .some (.prim (.bool b)) => .ok b | _ => .error .quantifierError
          -- (ti,vi)-threaded per-element fact
          have hkeyf : ∀ ti pti, ti ∈ vs → compilePred p (Factory.someOf ti) εnv = .ok pti →
              (Factory.option.get pti).typeOf = .bool → ∀ vi, ti.value? = some vi → vi ∈ valueSet →
              (pti.WellFormedLiteral εnv.entities ∧ pti.typeOf = .option .bool) ∧
              SameResults ((g pti).map (Value.prim ∘ Prim.bool)) pti ∧
              (∀ b, (evaluatePred p vi env.request env.entities).as Bool = .ok b ↔ g pti = .ok b) := by
            intro ti pti htimem hcp hbty vi hval hvimem
            have htisw : (Factory.someOf ti).WellFormed εnv.entities :=
              Term.WellFormed.some_wf (helttermwf ti htimem)
            have htisty : (Factory.someOf ti).typeOf = .option elemTy := by
              simp only [Factory.someOf, typeOf_term_some, helttermty ti htimem]
            obtain ⟨hptw, pty, hptty⟩ := compilePred_wf hwε.left htisw htisty hcp
            have hptybool : pty = .bool := by
              have h := hbty; simp only [(wf_option_get hptw hptty).right] at h; exact h
            subst hptybool
            have hvisim : (Except.ok vi : Spec.Result Value) ∼ Factory.someOf ti :=
              same_ok_some_iff.mpr (same_values_def.mpr hval)
            have hsim := compilePred_evaluate heq hwe₁.left hwε.left (heltvalwf vi hvimem) hvisim htisw htisty hprefs hcp
            cases hev : evaluatePred p vi env.request env.entities with
            | error e =>
              rw [hev] at hsim
              obtain ⟨hne, ty', hnoneq⟩ := same_error_implies hsim
              subst hnoneq
              refine ⟨⟨⟨hptw, isLiteral_none⟩, hptty⟩, ?_, ?_⟩
              · simp only [g, Except.map]
                exact same_error_implied_by (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
              · intro b; simp only [g, hev, Result.as, reduceCtorEq]
            | ok v' =>
              rw [hev] at hsim
              obtain ⟨pt', hpt', hsv⟩ := same_ok_implies hsim
              subst hpt'
              have hpt'wfl : pt'.WellFormedLiteral εnv.entities :=
                ⟨wf_term_some_implies hptw, value?_some_implies_isLiteral (same_values_def.mp hsv)⟩
              have hpt'ty : pt'.typeOf = .bool := by
                have h := hptty; simp only [typeOf_term_some, TermType.option.injEq] at h; exact h
              obtain ⟨b, hb⟩ := wfl_of_type_bool_is_bool hpt'wfl hpt'ty
              subst hb
              have hv'b : v' = .prim (.bool b) := same_bool_term_implies hsv
              subst hv'b
              refine ⟨⟨⟨hptw, isLiteral_some.mpr hpt'wfl.right⟩, hptty⟩, ?_, ?_⟩
              · simp only [g]; exact same_ok_bool
              · intro b'; simp only [g, hev, Result.as, Coe.coe, Value.asBool, Except.ok.injEq]
          let pairs : List (Term × Spec.Result Bool) := pts.map (fun pti => (pti, g pti))
          -- hwf / hsame for pairs via helt + hkeyf (each pti ∈ pts has ti ∈ vs with value vi ∈ valueSet)
          have hptifact : ∀ pti ∈ pts, ∃ ti ∈ vs, ∃ vi ∈ valueSet,
              compilePred p (Factory.someOf ti) εnv = .ok pti ∧ (Factory.option.get pti).typeOf = .bool ∧
              ti.value? = some vi := by
            intro pti hptimem
            obtain ⟨ti, htimem, hcp, hbty⟩ := List.forall₂_implies_all_right helt pti hptimem
            obtain ⟨vi, hvimem, hval⟩ := set_value?_implies_in_value hvalue? ti
              ((Cedar.Data.Set.mem_elts_iff_mem_set ti (Cedar.Data.Set.mk vs)).mpr htimem)
            exact ⟨ti, htimem, vi, hvimem, hcp, hbty, hval⟩
          have hwfp : ∀ pr ∈ pairs, (pr.1).WellFormedLiteral εnv.entities ∧ (pr.1).typeOf = .option .bool := by
            intro pr hpr; simp only [pairs, List.mem_map] at hpr
            obtain ⟨pti, hptimem, hpreq⟩ := hpr; subst hpreq
            obtain ⟨ti, htimem, vi, hvimem, hcp, hbty, hval⟩ := hptifact pti hptimem
            exact (hkeyf ti pti htimem hcp hbty vi hval hvimem).1
          have hsamep : ∀ pr ∈ pairs, SameResults (pr.2.map (Value.prim ∘ Prim.bool)) pr.1 := by
            intro pr hpr; simp only [pairs, List.mem_map] at hpr
            obtain ⟨pti, hptimem, hpreq⟩ := hpr; subst hpreq
            obtain ⟨ti, htimem, vi, hvimem, hcp, hbty, hval⟩ := hptifact pti hptimem
            exact (hkeyf ti pti htimem hcp hbty vi hval hvimem).2.1
          have hfold1 : pairs.foldr (fun pr acc => Factory.or (Factory.not (Factory.isSome pr.1)) acc) (false : Term)
              = pts.foldr (fun pti acc => Factory.or (Factory.not (Factory.isSome pti)) acc) (false : Term) := by
            simp only [pairs, List.foldr_map]
          have hfold2 : pairs.foldr (fun pr acc => Factory.and (Factory.option.get pr.1) acc) (true : Term)
              = pts.foldr (fun pti acc => Factory.and (Factory.option.get pti) acc) (true : Term) := by
            simp only [pairs, List.foldr_map]
          have hfm := all_fold_mem_char hwfp hsamep
          rw [hfold1, hfold2] at hfm
          simp only [Factory.option.get] at hfm ⊢
          have hem := @evalAll_mem_char valueSet (fun v => evaluatePred p v env.request env.entities)
          -- bridge: error-existence predicates coincide
          have hErrIff : (∃ pr ∈ pairs, ∀ b, pr.2 ≠ .ok b) ↔
              (∃ vi ∈ valueSet, ∀ b, (evaluatePred p vi env.request env.entities).as Bool ≠ .ok b) := by
            constructor
            · rintro ⟨pr, hpr, hprerr⟩
              simp only [pairs, List.mem_map] at hpr
              obtain ⟨pti, hptimem, hpreq⟩ := hpr; subst hpreq
              obtain ⟨ti, htimem, vi, hvimem, hcp, hbty, hval⟩ := hptifact pti hptimem
              have hiff := (hkeyf ti pti htimem hcp hbty vi hval hvimem).2.2
              exact ⟨vi, hvimem, fun b hb => hprerr b ((hiff b).mp hb)⟩
            · rintro ⟨vi, hvimem, hvierr⟩
              obtain ⟨ti, htimem, hval⟩ := set_value?_implies_in_term hvalue? vi hvimem
              obtain ⟨pti, hptimem, hcp, hbty⟩ := List.forall₂_implies_all_left helt ti htimem
              have hiff := (hkeyf ti pti htimem hcp hbty vi hval hvimem).2.2
              refine ⟨(pti, g pti), ?_, fun b hb => hvierr b ((hiff b).mpr hb)⟩
              simp only [pairs, List.mem_map]; exact ⟨pti, hptimem, rfl⟩
          -- decides coincide
          have hDecIff : (∀ pr ∈ pairs, pr.2 = .ok true) ↔
              (∀ vi ∈ valueSet, (evaluatePred p vi env.request env.entities).as Bool = .ok true) := by
            constructor
            · intro hall vi hvimem
              obtain ⟨ti, htimem, hval⟩ := set_value?_implies_in_term hvalue? vi hvimem
              obtain ⟨pti, hptimem, hcp, hbty⟩ := List.forall₂_implies_all_left helt ti htimem
              have hiff := (hkeyf ti pti htimem hcp hbty vi hval hvimem).2.2
              exact (hiff true).mpr (hall (pti, g pti) (by simp only [pairs, List.mem_map]; exact ⟨pti, hptimem, rfl⟩))
            · intro hall pr hpr
              simp only [pairs, List.mem_map] at hpr
              obtain ⟨pti, hptimem, hpreq⟩ := hpr; subst hpreq
              obtain ⟨ti, htimem, vi, hvimem, hcp, hbty, hval⟩ := hptifact pti hptimem
              have hiff := (hkeyf ti pti htimem hcp hbty vi hval hvimem).2.2
              exact (hiff true).mp (hall vi hvimem)
          -- combine
          rcases hfm with ⟨hferr, hfite⟩ | ⟨hfall, hfite⟩
          · -- compiler fold = noneOf ; so some element errors ⇒ evalAll = quantifierError
            rw [hfite]
            rw [pe_ifSome_some (tty := .bool) (by simp only [Factory.noneOf, typeOf_term_none])]
            obtain ⟨vi, hvimem, hvierr⟩ := hErrIff.mp hferr
            rcases hem with ⟨_, hev⟩ | ⟨hallok, _⟩
            · rw [hev]; exact same_error_implied_by (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
            · exact absurd (hallok vi hvimem) (fun ⟨b, hb⟩ => hvierr b hb)
          · -- compiler fold = someOf (bool decide pairs) ; all elements ok ⇒ evalAll ok
            rw [hfite]
            rw [pe_ifSome_some (tty := .bool) (by simp only [Factory.someOf, typeOf_term_some, typeOf_bool])]
            rcases hem with ⟨⟨vi, hvimem, hvierr⟩, _⟩ | ⟨_, hev⟩
            · obtain ⟨pr, hpr, hprerr⟩ := hErrIff.mpr ⟨vi, hvimem, hvierr⟩
              rcases hfall pr hpr with ⟨b, hb⟩; exact absurd hb (hprerr b)
            · rw [hev, Factory.someOf]
              have : decide (∀ pr ∈ pairs, pr.2 = Except.ok true)
                   = decide (∀ vi ∈ valueSet, (evaluatePred p vi env.request env.entities).as Bool = Except.ok true) := by
                simp only [decide_eq_decide]; exact hDecIff
              rw [this]; exact same_ok_bool
