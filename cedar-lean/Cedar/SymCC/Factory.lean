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

import Cedar.Spec
public import Cedar.SymCC.Function
import Cedar.Data.SizeOf

/-!
This file defines an API for construcing well-formed Terms. In this basic
implementation, the factory functions perform only basic partial
evaluation---constant folding along with a few other rewrites.  In an optimized
implementation, the factory functions would include more rewrite rules, and
share a cache of partially cannonicalized terms that have been constructed so
far.

The factory functions are total. If given well-formed and type-correct
arguments, a factory function will return a well-formed and type-correct output.
Otherwise, the output is an arbitrary term.

This design lets us minimize the number of error paths in the overall
specification of symbolic compilation, which makes for nicer code and proofs, and
it more closely tracks the specification of the concrete evaluator.

See `Compiler.lean` to see how the symbolic compiler uses this API.
-/

namespace Cedar.SymCC

open Cedar.Data
open Cedar.Spec

/--
Capture-free substitution of the reserved bound element variable `anyAllItVar`
(by its `id` `!anyall!it`) with a term `v` throughout `t` (D-55). Used by the
concrete fold of `set.all` over a literal receiver: predicate bodies are
non-nested (they contain no further `set.all` binder), so this is a plain
structural replacement with no capture concern. -/
public def Term.substAnyAllIt (v : Term) : Term → Term
  | .var w        => if w.id = "!anyall!it" then v else .var w
  | .prim p       => .prim p
  | .none ty      => .none ty
  | .some t       => .some (Term.substAnyAllIt v t)
  | .set ts ty    => .set (ts.map₁ (fun ⟨t, _⟩ => Term.substAnyAllIt v t)) ty
  | .record ats   => .record (ats.mapOnValues₂ (fun ⟨t, _⟩ => Term.substAnyAllIt v t))
  | .app op ts ty => .app op (ts.map₁ (fun ⟨t, _⟩ => Term.substAnyAllIt v t)) ty
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | omega
      | (rename_i h; have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem h; omega)
      | (rename_i h; have := List.sizeOf_lt_of_mem h; omega)
      | (rename_i h; have := Map.sizeOf_lt_of_toList ats; have := List.sizeOf_lt_of_mem h; omega)

/--
`Term.NoSetAll t` holds iff `t` contains no `Op.set.all` application node
anywhere. Predicate/error bodies produced by `compilePred` satisfy this
(predicates are non-nested, D-55), which is exactly the side condition under
which `interpretWith (some v)` agrees with `substAnyAllIt v` followed by
`interpret` (the latter has no `set.all` arm, the former folds it). -/
public def Term.NoSetAll : Term → Bool
  | .prim _      => true
  | .var _       => true
  | .none _      => true
  | .some t      => Term.NoSetAll t
  | .set ts _    => ts.all₁ λ ⟨t, _⟩ => Term.NoSetAll t
  | .record ats  => ats.toList.attach₂.all λ ⟨(_, t), _⟩ => Term.NoSetAll t
  | .app Op.set.all _ _ => false
  | .app _ ts _  => ts.attach.all λ ⟨t, _⟩ => Term.NoSetAll t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (have h := Set.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := Map.sizeOf_lt_of_toList ats; simp only at *; omega)
      | omega

/--
`Term.anyAllItTyped ety t` holds iff every occurrence of the reserved bound
variable `!anyall!it` in `t` carries type `ety`. Compiler-produced predicate
bodies satisfy this with `ety = elemTy` (they bind `anyAllItVar elemTy`), which
is what lets the concrete fold substitute a literal element (of type `elemTy`)
for the bound variable while preserving well-typedness (D-57). -/
public def Term.anyAllItTyped (ety : TermType) : Term → Bool
  | .prim _      => true
  | .var w       => if w.id = "!anyall!it" then w.ty = ety else true
  | .none _      => true
  | .some t      => Term.anyAllItTyped ety t
  | .set ts _    => ts.all₁ λ ⟨t, _⟩ => Term.anyAllItTyped ety t
  | .record ats  => ats.toList.attach₂.all λ ⟨(_, t), _⟩ => Term.anyAllItTyped ety t
  | .app _ ts _  => ts.attach.all λ ⟨t, _⟩ => Term.anyAllItTyped ety t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := Map.sizeOf_lt_of_toList ats; simp only at *; omega)
      | omega

/--
`Term.NoAnyAllItVar t` holds iff `t` contains no occurrence of the reserved
bound element variable `!anyall!it` (D-62). A well-formed `SymRequest`'s
principal/action/resource/context must satisfy this: otherwise a receiver term
mentioning `!anyall!it` would let `s.all(...)` capture the request variable when
the `set.all` encoding binds it, which is unsound. It implies
`Term.anyAllItTyped ety` for every `ety` (there is no reserved var to type). -/
public def Term.NoAnyAllItVar : Term → Bool
  | .prim _      => true
  | .var w       => w.id ≠ "!anyall!it"
  | .none _      => true
  | .some t      => Term.NoAnyAllItVar t
  | .set ts _    => ts.all₁ λ ⟨t, _⟩ => Term.NoAnyAllItVar t
  | .record ats  => ats.toList.attach₂.all λ ⟨(_, t), _⟩ => Term.NoAnyAllItVar t
  | .app _ ts _  => ts.attach.all λ ⟨t, _⟩ => Term.NoAnyAllItVar t
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (have := Set.sizeOf_lt_of_elts ts; have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)
      | (have := Map.sizeOf_lt_of_toList ats; simp only at *; omega)
      | omega


namespace Factory

---------- Term constructors ----------

@[inline, expose]
public def noneOf (ty : TermType) : Term := .none ty

@[inline, expose]
public def someOf (t : Term) : Term := .some t
prefix:0 "⊙" => someOf

public def setOf (ts : List Term) (ty : TermType) : Term := .set (Set.make ts) ty

public def recordOf (ats : List (Attr × Term)) : Term := .record (Map.make ats)

public def tagOf (entity tag : Term) : Term := .record (EntityTag.mk entity tag)

---------- SMTLib core theory of equality with uninterpreted functions (`UF`) ----------

public def not : Term → Term
  | .prim (.bool b)  => ! b
  | .app .not [t'] _ => t'
  | t                => .app .not [t] .bool

-- TODO: make private once Term/WF.lean and Thm/.../Factory.lean become `module`s able to `import all` this file (they need access to internals here)
public def opposites : Term → Term → Bool
  | t₁, .app .not [t₂] _
  | .app .not [t₁] _, t₂ => t₁ = t₂
  | _, _                 => false

public def and (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ || t₂ = true
  then t₁
  else if t₁ = true
  then t₂
  else if t₁ = false || t₂ = false || opposites t₁ t₂
  then false
  else .app .and [t₁, t₂] .bool

public def or (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ || t₂ = false
  then t₁
  else if t₁ = false
  then t₂
  else if t₁ = true || t₂ = true || opposites t₁ t₂
  then true
  else .app .or [t₁, t₂] .bool

public def implies (t₁ t₂ : Term) : Term :=
  or (not t₁) t₂

@[expose] -- TODO: remove `@[expose]` once Term/WF.lean and Thm/.../Factory.lean become `module`s able to `import all` this file (they need access to internals here)
public def eq (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .some t₁', .some t₂' => simplify t₁' t₂'
  | .some _, .none _     => false
  | .none _, .some _     => false
  | _, _                 => simplify t₁ t₂
where
  simplify (t₁ t₂ : Term) : Term :=
    if t₁ = t₂
    then true
    else if t₁.isLiteral && t₂.isLiteral
    then false
    else if t₁ = true && t₂.typeOf = .bool
    then t₂
    else if t₂ = true && t₁.typeOf = .bool
    then t₁
    else if t₁ = false && t₂.typeOf = .bool
    then not t₂
    else if t₂ = false && t₁.typeOf = .bool
    then not t₁
    else .app .eq [t₁, t₂] .bool

@[expose] -- TODO: remove `@[expose]` once Term/WF.lean and Thm/.../Factory.lean become `module`s able to `import all` this file (they need access to internals here)
public def ite (t₁ t₂ t₃ : Term) : Term :=
  match t₂, t₃ with
  | .some t₂', .some t₃' => .some (simplify t₂' t₃')
  | _, _                 => simplify t₂ t₃
where
  simplify (t₂ t₃ : Term) : Term :=
    if t₁ = true || t₂ = t₃
    then t₂
    else if t₁ = false
    then t₃
    else match t₂, t₃ with
    | .bool true,  .bool false => t₁
    | .bool false, .bool true  => not t₁
    | t₂,          .bool false => and t₁ t₂
    | .bool true,  t₃          => or t₁ t₃
    | t₂, t₃                   => .app .ite [t₁, t₂, t₃] t₂.typeOf

/-
Returns the result of applying a UUF or a UDF to a term. UDFs can be applied to
both literals and non-literal terms. The latter will result in the creation of a
chained `ite` expression that encodes the semantics of table lookup on an
unknown value.
-/
public def app : UnaryFunction → Term → Term
  | .uuf f, t => .app (.uuf f) [t] f.out
  | .udf f, t =>
  if t.isLiteral
  then match f.table.find? t with
    | .some t' => t'
    | .none    => f.default
  else f.table.toList.foldr (λ ⟨t₁, t₂⟩ t₃ => ite (eq t t₁) t₂ t₃) f.default

---------- SMTLib theory of finite bitvectors (`BV`) ----------

-- We are doing very weak partial evaluation for bitvectors: just constant
-- propagation. If more rewrites are needed, we can add them later.  This simple
-- approach is sufficient for the strong PE property we care about:  if given a
-- fully concrete input, the symbolic compiler returns a fully concrete output.

public def bvneg : Term → Term
  | .prim (.bitvec b)  => b.neg
  | .app .bvneg [t] _  => t
  | t                  => .app .bvneg [t] t.typeOf

-- TODO: make private once Term/WF.lean and Thm/.../Factory.lean become `module`s able to `import all` this file (they need access to internals here)
public def bvapp (op : Op) (fn : ∀ {n}, BitVec n → BitVec n → BitVec n) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    fn b₁ (BitVec.ofNat n b₂.toNat)
  | _, _ =>
    .app op [t₁, t₂] t₁.typeOf

public def bvadd := bvapp .bvadd BitVec.add
public def bvsub := bvapp .bvsub BitVec.sub
public def bvmul := bvapp .bvmul BitVec.mul
public def bvsdiv := bvapp .bvsdiv BitVec.smtSDiv
public def bvudiv := bvapp .bvudiv BitVec.smtUDiv
public def bvsrem := bvapp .bvsrem BitVec.srem
public def bvsmod := bvapp .bvsmod BitVec.smod
public def bvurem := bvapp .bvurem BitVec.umod

public def bvshl  := bvapp .bvshl (λ b₁ b₂ => b₁ <<< b₂)
public def bvlshr := bvapp .bvlshr (λ b₁ b₂ => b₁ >>> b₂)

-- TODO: make private once Term/WF.lean and Thm/.../Factory.lean become `module`s able to `import all` this file (they need access to internals here)
public def bvcmp (op : Op) (fn : ∀ {n}, BitVec n → BitVec n → Bool) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    fn b₁ (BitVec.ofNat n b₂.toNat)
  | _, _ =>
    .app op [t₁, t₂] .bool

public def bvslt := bvcmp .bvslt BitVec.slt
public def bvsle := bvcmp .bvsle BitVec.sle
public def bvult := bvcmp .bvult BitVec.ult
public def bvule := bvcmp .bvule BitVec.ule

public def bvnego : Term → Term
  | .prim (@TermPrim.bitvec n b₁) => BitVec.overflows n (-b₁.toInt)
  | t                             => .app .bvnego [t] .bool

-- TODO: make private once Term/WF.lean and Thm/.../Factory.lean become `module`s able to `import all` this file (they need access to internals here)
public def bvso (op : Op) (fn : Int → Int → Int) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    BitVec.overflows n (fn b₁.toInt b₂.toInt)
  | _, _ => .app op [t₁, t₂] .bool

public def bvsaddo := bvso .bvsaddo (· + ·)
public def bvssubo := bvso .bvssubo (· - ·)
public def bvsmulo := bvso .bvsmulo (· * ·)

/-
Note that BitVec defines zero_extend differently from SMTLib,
so we compensate for the difference in partial evaluation.
-/
public def zero_extend (n : Nat) : Term → Term
  | .prim (@TermPrim.bitvec m b) =>
    BitVec.zeroExtend (n + m) b
  | t =>
    match t.typeOf with
    | .bitvec m => .app (.zero_extend n) [t] (.bitvec (n + m))
    | _         => t -- should be ruled out by callers


---------- CVC theory of finite sets (`FS`) ----------

public def set.member (t ts : Term) : Term :=
  match ts with
  | .set (Set.mk []) _ => false
  | .set s _ =>
    if t.isLiteral && ts.isLiteral
    then s.contains t
    else .app Op.set.member [t, ts] .bool
  | _ => .app Op.set.member [t, ts] .bool

public def set.subset (sub sup : Term) : Term :=
  if sub = sup
  then true
  else match sub, sup with
    | .set (Set.mk []) _, _ => true
    | .set s₁ _, .set s₂ _  =>
      if sub.isLiteral && sup.isLiteral
      then s₁.subset s₂
      else .app Op.set.subset [sub, sup] .bool
    | _, _ => .app Op.set.subset [sub, sup] .bool

public def set.inter (ts₁ ts₂ : Term) : Term :=
  if ts₁ = ts₂
  then ts₁
  else match ts₁, ts₂ with
    | .set (Set.mk []) _, _ => ts₁
    | _, .set (Set.mk []) _ => ts₂
    | .set s₁ ty, .set s₂ _  =>
      if ts₁.isLiteral && ts₂.isLiteral
      then .set (s₁.intersect s₂) ty
      else .app Op.set.inter [ts₁, ts₂] (.set ty)
    | _, _ => .app Op.set.inter [ts₁, ts₂] ts₁.typeOf

public def set.isEmpty : Term → Term
  | .set s _ => s.isEmpty
  | ts =>
    match ts.typeOf with
    | .set ty => eq ts (.set Set.empty ty)
    | _       => false

public def set.intersects (ts₁ ts₂ : Term) : Term :=
  not (set.isEmpty (set.inter ts₁ ts₂))

/--
The reserved bound-element variable for the `.all` set-quantifier encoding
(D-51). Its `id` cannot be produced by the compiler for any Cedar variable, so
it never clashes with a free symbolic variable; `set.all` binds it. `elemTy` is
the set's element type.
-/
public def anyAllItVar (elemTy : TermType) : TermVar :=
  { id := "!anyall!it", ty := elemTy }

/--
Smart constructor for the `.all` set-quantifier term (D-34/D-51). `set` is the
compiled receiver (type `.set elemTy`), `pred`/`err` are boolean Terms over
`anyAllItVar elemTy` (the per-element predicate value and error). The result is `.option .bool` (tri-valued, D-35); it encodes via two
`set.filter` comprehensions under `HO_ALL` (D-52).

D-68: ALWAYS build the symbolic `.app Op.set.all` node. The literal-receiver
constant fold used to live here (D-55/D-64), but `Term.substAnyAllIt` is
*syntactic* and never re-reduces, which makes `compile_interpret .all` FALSE:
recompiling under a literal interpretation would fold with the unreduced
substitution (`app bvslt [bv 0, bv 5]`) while interpreting the node reduces to
`some true`. The fold therefore moves into the compiler's `.all` arm (which can
compile the predicate per element and so produce *reduced* bodies), and the only
reducing fold that remains is the one in `Term.interpret`/`interpretWith`
(`Interpretation.lean`), which IS semantics-preserving. -/
public def set.all (set pred err : Term) : Term :=
  .app Op.set.all [set, pred, err] (.option .bool)

---------- Core ADT operators with a trusted mapping to SMT ----------

public def option.get : Term → Term
  | .some t  => t
  | t        =>
    match t.typeOf with
    | .option ty => .app Op.option.get [t] ty
    | _          => t

public def record.get (t : Term) (a : Attr) : Term :=
  match t with
  | .record r => if let some tₐ := r.find? a then tₐ else t
  | _         =>
    match t.typeOf with
    | .record rty => if let some ty := rty.find? a then .app (Op.record.get a) [t] ty else t
    | _           => t

public def string.like (t : Term) (p : Pattern) : Term :=
  match t with
  | .prim (.string s) => wildcardMatch s p
  | _                 => .app (Op.string.like p) [t] .bool

---------- Extension ADT operators with a trusted mapping to SMT ----------

public def ext.decimal.val : Term → Term
  | .prim (.ext (.decimal d)) => d
  | t                         => .app (.ext ExtOp.decimal.val) [t] (.bitvec 64)

public def ext.ipaddr.isV4 : Term → Term
  | .prim (.ext (.ipaddr ip)) => ip.isV4
  | t                         => .app (.ext ExtOp.ipaddr.isV4) [t] .bool

public def ext.ipaddr.addrV4 : Term → Term
  | .prim (.ext (.ipaddr (.V4 ⟨v4, _⟩))) => v4
  | t                                    => .app (.ext ExtOp.ipaddr.addrV4) [t] (.bitvec 32)

public def ext.ipaddr.prefixV4 : Term → Term
  | .prim (.ext (.ipaddr (.V4 ⟨_, p4⟩))) =>
    match p4 with
    | .none     => noneOf (.bitvec 5)
    | .some pre => someOf pre
  | t => .app (.ext ExtOp.ipaddr.prefixV4) [t] (.option (.bitvec 5))

public def ext.ipaddr.addrV6 : Term → Term
  | .prim (.ext (.ipaddr (.V6 ⟨v6, _⟩))) => v6
  | t                                    => .app (.ext ExtOp.ipaddr.addrV6) [t] (.bitvec 128)

public def ext.ipaddr.prefixV6 : Term → Term
  | .prim (.ext (.ipaddr (.V6 ⟨_, p6⟩))) =>
    match p6 with
    | .none     => noneOf (.bitvec 7)
    | .some pre => someOf pre
  | t => .app (.ext ExtOp.ipaddr.prefixV6) [t] (.option (.bitvec 7))

public def ext.datetime.val : Term → Term
  | .prim (.ext (.datetime d)) => d.val
  | t                          => .app (.ext ExtOp.datetime.val) [t] (.bitvec 64)

public def ext.datetime.ofBitVec : Term -> Term
  | .prim (@TermPrim.bitvec 64 bv) => .prim (.ext (.datetime (Int64.ofInt bv.toInt)))
  | t                              => .app (.ext ExtOp.datetime.ofBitVec) [t] (.ext .datetime)

public def ext.duration.val : Term → Term
  | .prim (.ext (.duration d)) => d.val
  | t                          => .app (.ext ExtOp.duration.val) [t] (.bitvec 64)

public def ext.duration.ofBitVec : Term -> Term
  | .prim (@TermPrim.bitvec 64 bv) => .prim (.ext (.duration (Int64.ofInt bv.toInt)))
  | t                              => .app (.ext ExtOp.duration.ofBitVec) [t] (.ext .duration)

---------- Helper functions for constructing compound terms ----------

public def isNone : Term → Term
  | .none _  => true
  | .some _  => false
  | .app .ite [_, .some _, .some _] _ => false
  | .app .ite [g, .some _, .none _] _ => not g
  | .app .ite [g, .none _, .some _] _ => g
  | t =>
    match t.typeOf with
    | .option ty => eq t (.none ty)
    | _          => false

public def isSome (t : Term) : Term :=
  not (isNone t)

public def ifFalse (g t : Term) : Term :=
  ite g (noneOf t.typeOf) (someOf t)

public def ifTrue (g t : Term) : Term :=
  ite g (someOf t) (noneOf t.typeOf)

public def ifSome (g t : Term) : Term :=
  if let .option ty := t.typeOf
  then ite (isNone g) (noneOf ty) t
  else ifFalse (isNone g) t

public def anyTrue (f : Term → Term) (ts : List Term) : Term :=
  ts.foldl (λ acc t => or (f t) acc) false

public def anyNone (gs : List Term) : Term := anyTrue isNone gs

public def ifAllSome (gs : List Term) (t : Term) : Term :=
  let g := anyNone gs
  if let .option ty := t.typeOf
  then ite g (noneOf ty) t
  else ifFalse g t

public def bvaddChecked t₁ t₂ := ifFalse (bvsaddo t₁ t₂) (bvadd t₁ t₂)
public def bvsubChecked t₁ t₂ := ifFalse (bvssubo t₁ t₂) (bvsub t₁ t₂)
public def bvmulChecked t₁ t₂ := ifFalse (bvsmulo t₁ t₂) (bvmul t₁ t₂)

end Factory
end Cedar.SymCC
