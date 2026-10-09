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

public import Cedar.Data
import Cedar.Data.SizeOf
public import Cedar.Spec.ExtFun
public import Cedar.Spec.Wildcard

/-! This file defines abstract syntax for Cedar expressions. -/

namespace Cedar.Spec

open Cedar.Data

----- Definitions -----

public inductive Var where
  | principal
  | action
  | resource
  | context

public inductive UnaryOp where
  | not
  | neg
  | isEmpty
  | like (p : Pattern)
  | is (ety : EntityType)

public inductive BinaryOp where
  | eq
  | mem -- represents Cedar's in operator
  | hasTag
  | getTag
  | less
  | lessEq
  | add
  | sub
  | mul
  | contains
  | containsAll
  | containsAny

/--
A restricted predicate over the current set element, used as the body of
`Expr.all` (the `.all`/`.any` set quantifier). `item` is the element (surface
keyword `it`). There is deliberately no `set` and no `all` constructor, so
predicates are set-free and non-nested by construction (the decidable fragment
of Mohamed et al., FMCAD 2025, Condition 1). The remaining set-valued operators
(`isEmpty`, `contains`, `containsAll`, `containsAny`) are rejected by the Rust
smart constructors before an AST reaches the Lean spec.
-/
public inductive PredExpr where
  | item
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond : PredExpr) (thenExpr : PredExpr) (elseExpr : PredExpr)
  | and (a : PredExpr) (b : PredExpr)
  | or (a : PredExpr) (b : PredExpr)
  | unaryApp (op : UnaryOp) (expr : PredExpr)
  | binaryApp (op : BinaryOp) (a : PredExpr) (b : PredExpr)
  | getAttr (expr : PredExpr) (attr : Attr)
  | hasAttr (expr : PredExpr) (attr : Attr)
  | extHasAttr (expr : PredExpr) (attr : Attr) (attrs : List Attr)
  | record (map : List (Attr × PredExpr))
  | call (xfn : ExtFun) (args : List PredExpr)

public inductive Expr where
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond : Expr) (thenExpr : Expr) (elseExpr : Expr)
  | and (a : Expr) (b : Expr)
  | or (a : Expr) (b : Expr)
  | unaryApp (op : UnaryOp) (expr : Expr)
  | binaryApp (op : BinaryOp) (a : Expr) (b : Expr)
  | getAttr (expr : Expr) (attr : Attr)
  | hasAttr (expr : Expr) (attr : Attr)
  | extHasAttr (expr : Expr) (attr : Attr) (attrs : List Attr)
  | set (ls : List Expr)
  | record (map : List (Attr × Expr))
  | call (xfn : ExtFun) (args : List Expr)
  /-- `expr.all(pred)`: `pred` holds for every element of the set `expr`.
  `expr.any(pred)` is lowered to `!expr.all(!pred)` before reaching Lean. -/
  | all (expr : Expr) (pred : PredExpr)

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for Var
deriving instance Repr, DecidableEq, Inhabited for UnaryOp
deriving instance Repr, DecidableEq, Inhabited for BinaryOp
deriving instance Repr, Inhabited for PredExpr
deriving instance Repr, Inhabited for Expr

mutual

public def decPredExpr (x y : PredExpr) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case item.item => exact isTrue rfl
  case lit.lit x₁ y₁ | var.var x₁ y₁ =>
    exact match decEq x₁ y₁ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite x₁ x₂ x₃ y₁ y₂ y₃ =>
    exact match decPredExpr x₁ y₁, decPredExpr x₂ y₂, decPredExpr x₃ y₃ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ y₁ y₂ | or.or x₁ x₂ y₁ y₂ =>
    exact match decPredExpr x₁ y₁, decPredExpr x₂ y₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ o' y₁ =>
    exact match decEq o o', decPredExpr x₁ y₁ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ o' y₁ y₂ =>
    exact match decEq o o', decPredExpr x₁ y₁, decPredExpr x₂ y₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a y₁ a' | hasAttr.hasAttr x₁ a y₁ a' =>
    exact match decPredExpr x₁ y₁, decEq a a' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case extHasAttr.extHasAttr x₁ a b y₁ a' b' =>
    exact match decPredExpr x₁ y₁, decEq a a', decEq b b' with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs ays =>
    exact match decProdAttrPredExprList axs ays with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs f' ys =>
    exact match decEq f f', decPredExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrPredExprList (axs ays : List (Prod Attr PredExpr)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decPredExpr x y, decProdAttrPredExprList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decPredExprList (xs ys : List PredExpr) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decPredExpr x y, decPredExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

public instance : DecidableEq PredExpr := decPredExpr

mutual

-- We should be able to get rid of this manual derivation eventually.
-- There is work in progress on making these mutual derivations automatic.

public def decExpr (x y : Expr) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case lit.lit x₁ y₁ | var.var x₁ y₁ =>
    exact match decEq x₁ y₁ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite x₁ x₂ x₃ y₁ y₂ y₃ =>
    exact match decExpr x₁ y₁, decExpr x₂ y₂, decExpr x₃ y₃ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ y₁ y₂ | or.or x₁ x₂ y₁ y₂ =>
    exact match decExpr x₁ y₁, decExpr x₂ y₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ o' y₁ =>
    exact match decEq o o', decExpr x₁ y₁ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ o' y₁ y₂ =>
    exact match decEq o o', decExpr x₁ y₁, decExpr x₂ y₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a y₁ a' | hasAttr.hasAttr x₁ a y₁ a' =>
    exact match decExpr x₁ y₁, decEq a a' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case extHasAttr.extHasAttr x₁ a b y₁ a' b' =>
    exact match decExpr x₁ y₁, decEq a a', decEq b b' with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set xs ys =>
    exact match decExprList xs ys with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs ays =>
    exact match decProdAttrExprList axs ays with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs f' ys =>
    exact match decEq f f', decExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case all.all x₁ p y₁ q =>
    exact match decExpr x₁ y₁, decPredExpr p q with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrExprList (axs ays : List (Prod Attr Expr)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decExpr x y, decProdAttrExprList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decExprList (xs ys : List Expr) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decExpr x y, decExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

public instance : DecidableEq Expr := decExpr

/--
Internal placeholder expression standing for the quantifier element keyword `it`
(`PredExpr.item`) when a predicate is reconstructed as an `Expr` for typing. It is
never evaluated: the evaluator binds the real element value through
`evaluatePred`. Only its identity (as a capability key, and as a non-literal for
equality typing) matters, so any fixed closed expression serves; `principal` is
used because it is always well-typed in any request environment. This mirrors the
Rust validator's reserved unknown `__cedar::anyall::it` (D-21/D-44).
-/
public def itExpr : Expr := .var .principal

/--
Reconstruct the `Expr` denoted by a predicate, substituting the element keyword
`it` with `itExpr`. Used to type a predicate by reusing the ordinary expression
typing machinery (D-44). The set-free, non-nested shape of `PredExpr` (no `set`,
no `all`) is preserved — the result never contains `Expr.set` or `Expr.all`.
-/
public def PredExpr.toExpr : PredExpr → Expr
  | .item               => itExpr
  | .lit l              => .lit l
  | .var v              => .var v
  | .ite a b c          => .ite a.toExpr b.toExpr c.toExpr
  | .and a b            => .and a.toExpr b.toExpr
  | .or a b             => .or a.toExpr b.toExpr
  | .unaryApp op a      => .unaryApp op a.toExpr
  | .binaryApp op a b   => .binaryApp op a.toExpr b.toExpr
  | .getAttr a attr     => .getAttr a.toExpr attr
  | .hasAttr a attr     => .hasAttr a.toExpr attr
  | .extHasAttr a attr attrs => .extHasAttr a.toExpr attr attrs
  | .record axs         => .record $ axs.map₂ (λ ⟨(a, e), _⟩ => (a, e.toExpr))
  | .call f xs          => .call f $ xs.map₁ (λ ⟨e, _⟩ => e.toExpr)
decreasing_by
  all_goals (simp_wf ; try omega)
  all_goals
    rename_i h
    try simp at h
    try replace h := List.sizeOf_lt_of_mem h
    omega

/--
Does the predicate syntactically mention the current set element `it`
(`PredExpr.item`)?  SymCC uses this to keep the quantifier footprint `it`-free.
-/
public def PredExpr.mentionsIt : PredExpr → Bool
  | .item                    => true
  | .lit _                   => false
  | .var _                   => false
  | .ite c t e               => c.mentionsIt || t.mentionsIt || e.mentionsIt
  | .and a b                 => a.mentionsIt || b.mentionsIt
  | .or a b                  => a.mentionsIt || b.mentionsIt
  | .unaryApp _ e            => e.mentionsIt
  | .binaryApp _ a b         => a.mentionsIt || b.mentionsIt
  | .getAttr e _             => e.mentionsIt
  | .hasAttr e _             => e.mentionsIt
  | .extHasAttr e _ _        => e.mentionsIt
  | .record axs              => axs.attach₂.any (λ x => x.val.snd.mentionsIt)
  | .call _ xs               => xs.attach.any (λ x => have := List.sizeOf_lt_of_mem x.property; x.val.mentionsIt)
decreasing_by
  all_goals (simp_wf ; try omega)
  all_goals
    rename_i h
    try simp at h
    try replace h := List.sizeOf_lt_of_mem h
    omega

/--
`p` applies no `in` (ancestors) to an `it`-dependent left operand: every
`.binaryApp .mem l r` in `p` has `l.mentionsIt = false`.  This is the predicate
whose compiled footprint-sensitive `in` operands are all `it`-free, hence covered
by `footprintPred` (D-70, option A — `compile` guarantees it).
-/
public def PredExpr.NoItDependentIn : PredExpr → Bool
  | .item                    => true
  | .lit _                   => true
  | .var _                   => true
  | .ite c t e               => c.NoItDependentIn && t.NoItDependentIn && e.NoItDependentIn
  | .and a b                 => a.NoItDependentIn && b.NoItDependentIn
  | .or a b                  => a.NoItDependentIn && b.NoItDependentIn
  | .unaryApp _ e            => e.NoItDependentIn
  | .binaryApp .mem l r      => (!l.mentionsIt) && l.NoItDependentIn && r.NoItDependentIn
  | .binaryApp _ a b         => a.NoItDependentIn && b.NoItDependentIn
  | .getAttr e _             => e.NoItDependentIn
  | .hasAttr e _             => e.NoItDependentIn
  | .extHasAttr e _ _        => e.NoItDependentIn
  | .record axs              => axs.attach₂.all (λ x => x.val.snd.NoItDependentIn)
  | .call _ xs               => xs.attach.all (λ x => have := List.sizeOf_lt_of_mem x.property; x.val.NoItDependentIn)
decreasing_by
  all_goals (simp_wf ; try omega)
  all_goals
    rename_i h
    try simp at h
    try replace h := List.sizeOf_lt_of_mem h
    omega

end Cedar.Spec
