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
import Cedar.Thm.SymCC.WellTyped

/-! `verify*` functions always succeed on well-formed inputs. --/

namespace Cedar.Thm

open Spec SymCC Validation

/-- The well-typed form of a policy is quantifier-free (SymCC-supported fragment).
SymCC cannot compile/verify `.all` policies until Part B (D-33/D-34), so the
verifier completeness lemmas are stated over this fragment. -/
def PolicyNoQ (p' : Policy) (Γ : TypeEnv) : Prop :=
  ∀ tx : TypedExpr, TypedExpr.WellTyped Γ tx → tx.toExpr = p'.toExpr → tx.NoQuantifier

/-- Every policy in a list has a quantifier-free well-typed form. -/
def PoliciesNoQ (ps' : Policies) (Γ : TypeEnv) : Prop :=
  ∀ p' ∈ ps', PolicyNoQ p' Γ

/-- `verifyEvaluate` succeeds on sufficiently well-formed inputs. -/
theorem verifyEvaluate_is_ok {φ : Term → Term} {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .ok p')
  (hnq : PolicyNoQ p' Γ) :
  ∃ asserts, verifyEvaluate φ p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨tx, hwt_tx, heq_tx⟩ := wellTypedPolicy_ok_implies_well_typed_expr hwt
  simp only [verifyEvaluate]
  have ⟨_, hok, _⟩ := compile_well_typed hwf hwt_tx (hnq tx hwt_tx heq_tx)
  simp only [heq_tx] at hok
  simp [hok]

/-- `verifyEvaluatePair` succeeds on sufficiently well-formed inputs. -/
theorem verifyEvaluatePair_is_ok {φ : Term → Term → Term} {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicy p₁ Γ = .ok p₁')
  (hwt₂ : wellTypedPolicy p₂ Γ = .ok p₂')
  (hnq₁ : PolicyNoQ p₁' Γ)
  (hnq₂ : PolicyNoQ p₂' Γ) :
  ∃ asserts, verifyEvaluatePair φ p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨tx₁, hwt_tx₁, heq_tx₁⟩ := wellTypedPolicy_ok_implies_well_typed_expr hwt₁
  have ⟨tx₂, hwt_tx₂, heq_tx₂⟩ := wellTypedPolicy_ok_implies_well_typed_expr hwt₂
  simp only [verifyEvaluatePair]
  have ⟨_, hok₁, _⟩ := compile_well_typed hwf hwt_tx₁ (hnq₁ tx₁ hwt_tx₁ heq_tx₁)
  have ⟨_, hok₂, _⟩ := compile_well_typed hwf hwt_tx₂ (hnq₂ tx₂ hwt_tx₂ heq_tx₂)
  simp only [heq_tx₁, heq_tx₂] at hok₁ hok₂
  simp [hok₁, hok₂]

/-- `compileWithEffect` succeeds on sufficiently well-formed inputs. -/
theorem compileWithEffect_is_ok (effect : Effect) {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .ok p')
  (hnq : PolicyNoQ p' Γ) :
  ∃ asserts, compileWithEffect effect p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨tx, hwt_tx, heq_tx⟩ := wellTypedPolicy_ok_implies_well_typed_expr hwt
  simp only [compileWithEffect]
  have ⟨_, hok, _⟩ := compile_well_typed hwf hwt_tx (hnq tx hwt_tx heq_tx)
  simp only [heq_tx] at hok
  simp only [hok]
  split <;> simp

/-- `satisfiedPolicies` succeeds on sufficiently well-formed inputs. -/
theorem satisfiedPolicies_is_ok (effect : Effect) {ps ps' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicies ps Γ = .ok ps')
  (hnq : PoliciesNoQ ps' Γ) :
  ∃ asserts, satisfiedPolicies effect ps' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [SymCC.satisfiedPolicies]
  have ⟨ts, hts⟩ :
    ∃ ts,
      List.filterMapM (fun x => compileWithEffect effect x (SymEnv.ofEnv Γ)) ps' = .ok ts
  := by
    induction ps' generalizing ps with
    | nil => exists []
    | cons hd tl ih =>
      simp only [List.filterMapM_cons]
      have hwt_policies := List.mapM_ok_implies_all_from_ok hwt
      have ⟨p, hmem_p, hwt_p⟩ := hwt_policies hd List.mem_cons_self
      have ⟨asserts, hasserts⟩ := compileWithEffect_is_ok effect hwf hwt_p
        (hnq hd List.mem_cons_self)
      simp only [hasserts, bind_pure_comp, Except.bind_ok]
      cases ps with
      | nil => contradiction
      | cons ps_hd ps_tl =>
        simp only [wellTypedPolicies, List.mapM_cons, bind, Except.bind, pure, Except.pure] at hwt
        split at hwt
        contradiction
        split at hwt
        contradiction
        rename_i heq
        simp only [Except.ok.injEq, List.cons.injEq] at hwt
        simp only [hwt.2] at heq
        have ⟨ts_tl, hts_tl⟩ := ih heq (fun p' hp' => hnq p' (List.mem_cons_of_mem _ hp'))
        split
        · exists ts_tl
        · simp [hts_tl]
  simp [hts]

/-- `isAuthorized` succeeds on sufficiently well-formed inputs. -/
theorem isAuthorized_is_ok {ps ps' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicies ps Γ = .ok ps')
  (hnq : PoliciesNoQ ps' Γ) :
  ∃ asserts, isAuthorized ps' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [SymCC.isAuthorized]
  have ⟨_, h₁⟩ := satisfiedPolicies_is_ok .forbid hwf hwt hnq
  have ⟨_, h₂⟩ := satisfiedPolicies_is_ok .permit hwf hwt hnq
  simp [h₁, h₂]

/-- `verifyIsAuthorized` succeeds on sufficiently well-formed inputs. -/
theorem verifyIsAuthorized_is_ok (φ : Term → Term → Term) {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicies ps₁ Γ = .ok ps₁')
  (hwt₂ : wellTypedPolicies ps₂ Γ = .ok ps₂')
  (hnq₁ : PoliciesNoQ ps₁' Γ)
  (hnq₂ : PoliciesNoQ ps₂' Γ) :
  ∃ asserts, verifyIsAuthorized φ ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [verifyIsAuthorized]
  have ⟨_, h₁⟩ := isAuthorized_is_ok hwf hwt₁ hnq₁
  have ⟨_, h₂⟩ := isAuthorized_is_ok hwf hwt₂ hnq₂
  simp [h₁, h₂]

/-- `verifyNeverErrors` succeeds on sufficiently well-formed inputs. -/
theorem verifyNeverErrors_is_ok {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .ok p')
  (hnq : PolicyNoQ p' Γ) :
  ∃ asserts, verifyNeverErrors p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyEvaluate_is_ok hwf hwt hnq

/-- `verifyAlwaysMatches` succeeds on sufficiently well-formed inputs. -/
theorem verifyAlwaysMatches_is_ok {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .ok p')
  (hnq : PolicyNoQ p' Γ) :
  ∃ asserts, verifyAlwaysMatches p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyEvaluate_is_ok hwf hwt hnq

/-- `verifyNeverMatches` succeeds on sufficiently well-formed inputs. -/
theorem verifyNeverMatches_is_ok {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .ok p')
  (hnq : PolicyNoQ p' Γ) :
  ∃ asserts, verifyNeverMatches p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyEvaluate_is_ok hwf hwt hnq

/-- `verifyMatchesEquivalent` succeeds on sufficiently well-formed inputs. -/
theorem verifyMatchesEquivalent_is_ok {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicy p₁ Γ = .ok p₁')
  (hwt₂ : wellTypedPolicy p₂ Γ = .ok p₂')
  (hnq₁ : PolicyNoQ p₁' Γ)
  (hnq₂ : PolicyNoQ p₂' Γ) :
  ∃ asserts, verifyMatchesEquivalent p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyEvaluatePair_is_ok hwf hwt₁ hwt₂ hnq₁ hnq₂

/-- `verifyMatchesImplies` succeeds on sufficiently well-formed inputs. -/
theorem verifyMatchesImplies_is_ok {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicy p₁ Γ = .ok p₁')
  (hwt₂ : wellTypedPolicy p₂ Γ = .ok p₂')
  (hnq₁ : PolicyNoQ p₁' Γ)
  (hnq₂ : PolicyNoQ p₂' Γ) :
  ∃ asserts, verifyMatchesImplies p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyEvaluatePair_is_ok hwf hwt₁ hwt₂ hnq₁ hnq₂

/-- `verifyMatchesDisjoint` succeeds on sufficiently well-formed inputs. -/
theorem verifyMatchesDisjoint_is_ok {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicy p₁ Γ = .ok p₁')
  (hwt₂ : wellTypedPolicy p₂ Γ = .ok p₂')
  (hnq₁ : PolicyNoQ p₁' Γ)
  (hnq₂ : PolicyNoQ p₂' Γ) :
  ∃ asserts, verifyMatchesDisjoint p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyEvaluatePair_is_ok hwf hwt₁ hwt₂ hnq₁ hnq₂

/-- `verifyImplies` succeeds on sufficiently well-formed inputs. -/
theorem verifyImplies_is_ok {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicies ps₁ Γ = .ok ps₁')
  (hwt₂ : wellTypedPolicies ps₂ Γ = .ok ps₂')
  (hnq₁ : PoliciesNoQ ps₁' Γ)
  (hnq₂ : PoliciesNoQ ps₂' Γ) :
  ∃ asserts, verifyImplies ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyIsAuthorized_is_ok _ hwf hwt₁ hwt₂ hnq₁ hnq₂

theorem isAuthorized_allowAll_is_ok (Γ : TypeEnv) :
  isAuthorized [verifyAlwaysAllows.allowAll] (SymEnv.ofEnv Γ) = .ok (.prim (.bool .true))
:= by
  simp [SymCC.isAuthorized, SymCC.satisfiedPolicies, SymCC.compileWithEffect, verifyAlwaysAllows.allowAll]
  simp [Policy.toExpr, PrincipalScope.toExpr, ActionScope.toExpr, ResourceScope.toExpr, Scope.toExpr, Conditions.toExpr, Condition.toExpr]
  simp [Factory.and, Factory.anyTrue, Factory.not, Factory.or]
  simp [do_eq_ok, Factory.someOf]
  exists (Term.prim (.bool true)).some
  simp only [pe_eq_same, and_true]
  simp [SymCC.compile, compilePrim, Factory.someOf, compileAnd, pe_ifSome_some]

/-- `verifyAlwaysAllows` succeeds on sufficiently well-formed inputs. -/
theorem verifyAlwaysAllows_is_ok {ps ps' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicies ps Γ = .ok ps')
  (hnq : PoliciesNoQ ps' Γ) :
  ∃ asserts, verifyAlwaysAllows ps' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨_, h₁⟩ := isAuthorized_is_ok hwf hwt hnq
  have h₂ := isAuthorized_allowAll_is_ok Γ
  simp [
    verifyAlwaysAllows,
    verifyImplies,
    verifyIsAuthorized,
    h₁, h₂,
  ]

/-- `verifyAlwaysDenies` succeeds on sufficiently well-formed inputs. -/
theorem verifyAlwaysDenies_is_ok {ps ps' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicies ps Γ = .ok ps')
  (hnq : PoliciesNoQ ps' Γ) :
  ∃ asserts, verifyAlwaysDenies ps' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨_, h⟩ := isAuthorized_is_ok hwf hwt hnq
  simp only [
    h, verifyAlwaysDenies,
    verifyImplies,
    verifyIsAuthorized,
  ]
  simp [SymCC.isAuthorized, SymCC.satisfiedPolicies]

/-- `verifyEquivalent` succeeds on sufficiently well-formed inputs. -/
theorem verifyEquivalent_is_ok {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicies ps₁ Γ = .ok ps₁')
  (hwt₂ : wellTypedPolicies ps₂ Γ = .ok ps₂')
  (hnq₁ : PoliciesNoQ ps₁' Γ)
  (hnq₂ : PoliciesNoQ ps₂' Γ) :
  ∃ asserts, verifyEquivalent ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyIsAuthorized_is_ok _ hwf hwt₁ hwt₂ hnq₁ hnq₂

/-- `verifyDisjoint` succeeds on sufficiently well-formed inputs. -/
theorem verifyDisjoint_is_ok {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicies ps₁ Γ = .ok ps₁')
  (hwt₂ : wellTypedPolicies ps₂ Γ = .ok ps₂')
  (hnq₁ : PoliciesNoQ ps₁' Γ)
  (hnq₂ : PoliciesNoQ ps₂' Γ) :
  ∃ asserts, verifyDisjoint ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyIsAuthorized_is_ok _ hwf hwt₁ hwt₂ hnq₁ hnq₂

end Cedar.Thm
