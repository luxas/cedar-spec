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
import Cedar.Spec
public import Cedar.SymCC.Env
import Cedar.SymCC.Factory
public import Cedar.SymCC.Function
public import Cedar.SymCC.Term

/-!

# Interpretations

An `Interpretation` is a structure that binds term variables to literal terms
and uninterpreted functions (`UUF`) to interpreted ones (`UDF`). In practice,
Interpretations are obtained from low-level models returned by SMT solvers.

When a symbolic structure (such as a term, request, function, or entities) is
interpreted with respect to an Interpretation, the result is a literal symbolic
structure.
-/

namespace Cedar.SymCC

open Data Factory Spec

/--
An Interpretation consists of three maps:
- `vars` maps variables to literal terms of the same type;
- `funs` maps uninterpreted functions to intepreted functions; and
- `partials` maps partial application terms to literals of the right type.

A partial application term represents the application of an operator to a
correctly typed literal outside of the operator's domain---for example, the
application of `option.get` to a `.none` term. The SMTLib language treats all
such operators as total, and it picks an arbitrary value of the right type as
the result of the application.
-/
public structure Interpretation where
  vars : TermVar → Term
  funs : UUF → UDF
  partials : Term → Term

-- TODO: make private once files like `Thm/.../Interpret/Factory.lean become `module`s and able to `import all` this file in order to prove things about internals like this helper function
public def UnaryFunction.interpret (I : Interpretation) : UnaryFunction → UnaryFunction
  | .uuf f => .udf (I.funs f)
  | .udf f => .udf f

public def Factory.option.get' (I : Interpretation) (t : Term) : Term :=
  if let .none ty := t
  then I.partials (.app Op.option.get [.none ty] ty)
  else (Factory.option.get t)

-- TODO: make `private` once files like `Thm/.../Interpret/Lit.lean` become `module`s and able to (perhaps transitively) `import all` this file in order to prove things about internals like this helper function
public def Factory.ext.ipaddr.addrV4' (I : Interpretation) (t : Term) : Term :=
  if let .prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩))) := t
  then I.partials (.app (.ext ExtOp.ipaddr.addrV4) [.prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩)))] (.bitvec 32))
  else (Factory.ext.ipaddr.addrV4 t)

-- TODO: make `private` once files like `Thm/.../Interpret/Lit.lean` become `module`s and able to (perhaps transitively) `import all` this file in order to prove things about internals like this helper function
public def Factory.ext.ipaddr.prefixV4' (I : Interpretation) (t : Term) : Term :=
  if let .prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩))) := t
  then I.partials (.app (.ext ExtOp.ipaddr.prefixV4) [.prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩)))] (.option (.bitvec 5)))
  else (Factory.ext.ipaddr.prefixV4 t)

-- TODO: make `private` once files like `Thm/.../Interpret/Lit.lean` become `module`s and able to (perhaps transitively) `import all` this file in order to prove things about internals like this helper function
public def Factory.ext.ipaddr.addrV6' (I : Interpretation) (t : Term) : Term :=
  if let .prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩))) := t
  then I.partials (.app (.ext ExtOp.ipaddr.addrV6) [.prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩)))] (.bitvec 128))
  else (Factory.ext.ipaddr.addrV6 t)

-- TODO: make `private` once files like `Thm/.../Interpret/Lit.lean` become `module`s and able to (perhaps transitively) `import all` this file in order to prove things about internals like this helper function
public def Factory.ext.ipaddr.prefixV6' (I : Interpretation) (t : Term) : Term :=
  if let .prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩))) := t
  then I.partials (.app (.ext ExtOp.ipaddr.prefixV6) [.prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩)))] (.option (.bitvec 7)))
  else (Factory.ext.ipaddr.prefixV6 t)

def ExtOp.interpret (I : Interpretation) (op : ExtOp) (t₁ : Term) : Term :=
  match op with
  | ExtOp.decimal.val       => Factory.ext.decimal.val t₁
  | ExtOp.ipaddr.isV4       => Factory.ext.ipaddr.isV4 t₁
  | ExtOp.ipaddr.addrV4     => Factory.ext.ipaddr.addrV4' I t₁
  | ExtOp.ipaddr.prefixV4   => Factory.ext.ipaddr.prefixV4' I t₁
  | ExtOp.ipaddr.addrV6     => Factory.ext.ipaddr.addrV6' I t₁
  | ExtOp.ipaddr.prefixV6   => Factory.ext.ipaddr.prefixV6' I t₁
  | ExtOp.datetime.val      => Factory.ext.datetime.val t₁
  | ExtOp.datetime.ofBitVec => Factory.ext.datetime.ofBitVec t₁
  | ExtOp.duration.val      => Factory.ext.duration.val t₁
  | ExtOp.duration.ofBitVec => Factory.ext.duration.ofBitVec t₁

def Op.interpret (I : Interpretation) (op : Op) (ts : List Term) (ty : TermType) : Term :=
  match op, ts with
  | .not, [t₁]            => Factory.not t₁
  | .and, [t₁, t₂]        => Factory.and t₁ t₂
  | .or,  [t₁, t₂]        => Factory.or t₁ t₂
  | .eq,  [t₁, t₂]        => Factory.eq t₁ t₂
  | .ite, [t₁, t₂, t₃]    => Factory.ite t₁ t₂ t₃
  | .uuf f, [t₁]          => Factory.app (.udf (I.funs f)) t₁
  | .bvneg, [t₁]          => Factory.bvneg t₁
  | .bvadd, [t₁, t₂]      => Factory.bvadd t₁ t₂
  | .bvsub, [t₁, t₂]      => Factory.bvsub t₁ t₂
  | .bvmul, [t₁, t₂]      => Factory.bvmul t₁ t₂
  | .bvsdiv, [t₁, t₂]     => Factory.bvsdiv t₁ t₂
  | .bvsrem, [t₁, t₂]     => Factory.bvsrem t₁ t₂
  | .bvsmod, [t₁, t₂]     => Factory.bvsmod t₁ t₂
  | .bvurem, [t₁, t₂]     => Factory.bvurem t₁ t₂
  | .bvudiv, [t₁, t₂]     => Factory.bvudiv t₁ t₂
  | .bvshl, [t₁, t₂]      => Factory.bvshl t₁ t₂
  | .bvlshr, [t₁, t₂]     => Factory.bvlshr t₁ t₂
  | .bvnego, [t₁]         => Factory.bvnego t₁
  | .bvsaddo, [t₁, t₂]    => Factory.bvsaddo t₁ t₂
  | .bvssubo, [t₁, t₂]    => Factory.bvssubo t₁ t₂
  | .bvsmulo, [t₁, t₂]    => Factory.bvsmulo t₁ t₂
  | .bvslt, [t₁, t₂]      => Factory.bvslt t₁ t₂
  | .bvsle, [t₁, t₂]      => Factory.bvsle t₁ t₂
  | .bvult, [t₁, t₂]      => Factory.bvult t₁ t₂
  | .bvule, [t₁, t₂]      => Factory.bvule t₁ t₂
  | .zero_extend n, [t₁]  => Factory.zero_extend n t₁
  | Op.set.member, [t₁, t₂] => Factory.set.member t₁ t₂
  | Op.set.subset, [t₁, t₂] => Factory.set.subset t₁ t₂
  | Op.set.inter, [t₁, t₂]  => Factory.set.inter t₁ t₂
  | Op.option.get, [t₁]     => Factory.option.get' I t₁
  | Op.record.get a, [t₁]   => Factory.record.get t₁ a
  | Op.string.like p, [t₁]  => Factory.string.like t₁ p
  | .ext xop, [t₁]        => xop.interpret I t₁
  | _, _                  => .app op ts ty

/--
`Term.interpretWith σ I` interprets a term under model `I`, additionally
substituting the reserved bound element variable `anyAllItVar` by `σ` when `σ`
is `some v` (used inside the `set.all` concrete fold, D-55). It is structural on
the term and otherwise identical to `interpret` — every arm calls the same
Factory / `op.interpret` constructors, so it re-normalises (e.g. `bvslt 0 1`
folds to `true`). `Term.interpret I := interpretWith none I`. -/
public def Term.interpretWith (σ : Option Term) (I : Interpretation) : Term → Term
  | .prim p       => .prim p
  | .var v        => match σ with
                     | Option.some v' => if v.id = "!anyall!it" then v' else I.vars v
                     | Option.none    => I.vars v
  | .none ty      => noneOf ty
  | .some t       => someOf (Term.interpretWith σ I t)
  | .set ts ty    =>
    let ts' := ts.map₁ (λ ⟨t, _⟩ => Term.interpretWith σ I t)
    .set ts' ty
  | .app Op.set.all [setT, predT, errT] ty =>
    -- D-55 final semantics: interpret the receiver; if it is a literal set, fold
    -- element-by-element (bound var substituted by each element, free vars
    -- interpreted) to a literal, matching `evalAll`. Otherwise keep the symbolic
    -- node, interpreting free vars in the bodies but leaving the bound var.
    match Term.interpretWith σ I setT with
    | .set (Set.mk vs) _ =>
      let conj   := vs.foldr (fun vi acc => Factory.and (Term.interpretWith (some vi) I predT) acc) (true : Term)
      let anyErr := vs.foldr (fun vi acc => Factory.or  (Term.interpretWith (some vi) I errT)  acc) (false : Term)
      Factory.ite anyErr (Factory.noneOf .bool) (Factory.someOf conj)
    | setT' =>
      -- D-59: the receiver did not interpret to a literal set. This branch is
      -- unreachable under a well-formed interpretation (an interpretation makes
      -- every term of set type a literal set), so it exists only to keep
      -- `interpretWith` total. We still interpret the bodies' free variables, but
      -- only adopt the interpreted bodies when they carry the `set.all` typing
      -- evidence (`NoSetAll` + `anyAllItTyped`) that a well-formed `set.all` node
      -- requires; otherwise we fall back to the original bodies, which carry that
      -- evidence by the node's own well-formedness. Both shapes are well-formed.
      let p' := Term.interpretWith Option.none I predT
      let e' := Term.interpretWith Option.none I errT
      match setT'.typeOf with
      | .set elemTy =>
        if p'.NoSetAll && e'.NoSetAll && p'.anyAllItTyped elemTy && e'.anyAllItTyped elemTy
        then .app Op.set.all [setT', p', e'] ty
        else .app Op.set.all [setT', predT, errT] ty
      | _ => .app Op.set.all [setT', predT, errT] ty
  | .app op ts ty =>
    let ts' := ts.map₁ (λ ⟨t, _⟩ => Term.interpretWith σ I t)
    op.interpret I ts' ty
  | .record ats   =>
    .record $ ats.mapOnValues₂ (λ ⟨t, _⟩ => Term.interpretWith σ I t)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (rename_i h; have := Set.sizeOf_lt_of_mem h; omega)
      | (rename_i h; have := List.sizeOf_lt_of_mem h; omega)

@[expose]
public def Term.interpret (I : Interpretation) (t : Term) : Term := Term.interpretWith Option.none I t

@[expose]
public def SymRequest.interpret (I : Interpretation) (req : SymRequest)  : SymRequest :=
  {
    principal := req.principal.interpret I,
    action    := req.action.interpret I,
    resource  := req.resource.interpret I,
    context   := req.context.interpret I
  }

public def SymTags.interpret (I : Interpretation) (τags : SymTags) : SymTags :=
  {
    keys := τags.keys.interpret I,
    vals := τags.vals.interpret I
  }

public def SymEntityData.interpret (I : Interpretation) (d : SymEntityData) : SymEntityData :=
  {
    attrs     := d.attrs.interpret I,
    ancestors := d.ancestors.mapOnValues (UnaryFunction.interpret I)
    members   := d.members,
    tags      := d.tags.map (SymTags.interpret I)
  }

public def SymEntities.interpret (I : Interpretation) (es : SymEntities)  : SymEntities :=
  es.mapOnValues (SymEntityData.interpret I)

@[expose]
public def SymEnv.interpret (I : Interpretation) (env : SymEnv) : SymEnv :=
  ⟨env.request.interpret I, env.entities.interpret I⟩


end Cedar.SymCC
