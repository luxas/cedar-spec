/-
 Copyright Cedar Contributors
 SPDX-License-Identifier: Apache-2.0
-/

-- NOTE (D-68, crux): this file is deliberately NOT a `module`. It must import the
-- non-module `CompilePredInterpret`; a `module` file may not import a non-module
-- one. A non-module file CAN import the module files below and see their `public`
-- lemmas (`interpret_set_all_lit`, `interpret_extInterp_eq_of_noAnyAllItVar`,
-- `interpretWith_some_eq_interpret_ext`, …).

import Cedar.SymCC
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Compiler.CompilePredInterpret
import Cedar.Thm.SymCC.Compiler.SetAllInterpret
import Cedar.Thm.SymCC.Term.Interpret.WF
import Cedar.Thm.SymCC.Term.Interpret.SubstAnyAllIt
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Env.Interpret
import Cedar.Thm.Tactics

namespace Cedar.Thm

open Spec SymCC Factory Cedar.Data

/-- D-68 step 4: interpreting a symbolic environment under `extInterp I v ety`
gives the same environment as interpreting under `I`. The entities read only
`I.funs`/`I.partials` (which `extInterp` leaves untouched), and a well-formed
request's four terms are `NoAnyAllItVar`/`NoSetAll` (D-62), so they never read the
reserved `I.vars` entry that `extInterp` redefines. -/
theorem symEnv_interpret_extInterp {εnv : SymEnv} {I : Interpretation} {v : Term} {ety : TermType}
    (hwε : εnv.WellFormed) :
    εnv.interpret (extInterp I v ety) = εnv.interpret I := by
  have hreq := hwε.left
  simp only [SymRequest.WellFormed] at hreq
  obtain ⟨_, _, hpn, hps, _, _, han, has, _, _, hrn, hrs, _, _, hcn, hcs⟩ := hreq
  simp only [SymEnv.interpret, SymRequest.interpret, SymEntities.interpret]
  refine SymEnv.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · -- request: each term interprets identically
    refine SymRequest.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact interpret_extInterp_eq_of_noAnyAllItVar _ hpn hps
    · exact interpret_extInterp_eq_of_noAnyAllItVar _ han has
    · exact interpret_extInterp_eq_of_noAnyAllItVar _ hrn hrs
    · exact interpret_extInterp_eq_of_noAnyAllItVar _ hcn hcs
  · -- entities: `extInterp` only redefines `I.vars`, which entity interpretation never reads
    rfl

-- NEXT: `compile_interpret_all` (closes Compiler.lean:168) is to be added here and
-- wired into Compiler.lean's `.all` arm. The receiver interprets to a WF *literal*
-- set, so the interpreted-side compile always takes the per-element literal-fold
-- path; its reconciliation with the three εnv-side cases consumes, per element:
--   `interpret_ifSome` + `interpret_option_get_aux` (ifSome/option.get commute),
--   `interpret_set_all_lit` (interpret of the symbolic set.all node, D-67),
--   `interpretWith_some_eq_interpret_ext` (D-67) + `compilePred_interpret` at
--   I' := extInterp I vi elemTy + `symEnv_interpret_extInterp` (above) +
--   `extInterp_wf`. See .kiro/.../phase5b/D-68-compiler-fold.md.

end Cedar.Thm
