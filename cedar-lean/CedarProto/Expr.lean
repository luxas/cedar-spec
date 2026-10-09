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

import Cedar.Spec
import Cedar.Data.Int64
import Protobuf.Message
import Protobuf.Enum
import Protobuf.Map

-- Message Dependencies
import CedarProto.EntityUID

open Proto

namespace Cedar.Spec

namespace Prim

-- Note that Cedar.Spec.Prim is defined as
-- inductive Prim where
-- | bool (b : Bool)
-- | int (i : Int64)
-- | string (s : String)
-- | entityUID (uid : EntityUID)
-- Note: This corresponds to Literal in the protobuf definitions

@[inline]
def merge_bool (p : Prim) (b2 : Bool) : Prim :=
  match p with
  | .bool b1 => .bool (Field.merge b1 b2)
  | _        => .bool b2

@[inline]
def merge_int (_ : Prim) (pi : Proto.Int64) : Prim :=
  have i : Int := pi
  if h₁ : i < Int64.MIN then
    panic!("Integer less than INT64_MIN")
  else if h₂ : i > Int64.MAX then
    panic!("Integer greater than INT64_MAX")
  else
    have h : Int64.MIN ≤ i ∧ i ≤ Int64.MAX := by omega
    -- Override semantics
    .int (Int64.ofIntChecked i h)

@[inline]
def merge_string (p : Prim) (s2 : String) : Prim :=
  match p with
  | .string s1 => .string (Field.merge s1 s2)
  | _          => .string s2

@[inline]
def merge_euid (p : Prim) (euid2 : EntityUID) : Prim :=
  match p with
  | .entityUID euid1 => .entityUID (Field.merge euid1 euid2)
  | _                => .entityUID euid2

@[inline]
def merge (p1 : Prim) (p2 : Prim) : Prim :=
  match p2 with
  | .bool b2      => merge_bool p1 b2
  | .int i2       => merge_int p1 (i2 : Int)
  | .string s2    => merge_string p1 s2
  | .entityUID e2 => merge_euid p1 e2

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn Prim) := do
  match t.fieldNum with
  | 1 =>
    let x : Bool ← Field.guardedParse t
    pureMergeFn (merge_bool · x)
  | 2 =>
    let x : Proto.Int64 ← Field.guardedParse t
    pureMergeFn (merge_int · x)
  | 3 =>
    let x : String ← Field.guardedParse t
    pureMergeFn (merge_string · x)
  | 4 =>
    let x : EntityUID ← Field.guardedParse t
    pureMergeFn (merge_euid · x)
  | _ =>
    t.wireType.skip
    pure ignore

instance : Message Prim := {
  parseField := parseField,
  merge      := merge
}

end Prim

namespace Var

@[inline]
def fromInt (n : Int) : Except String Var :=
  match n with
  | 0 => .ok .principal
  | 1 => .ok .action
  | 2 => .ok .resource
  | 3 => .ok .context
  | n => .error s!"Field {n} does not exist in Var"

instance : Inhabited Var where
  default := .principal

instance : ProtoEnum Var := {
  fromInt := fromInt
}

end Var

namespace PatElem

inductive Wildcard where
  | star
deriving Inhabited

instance : ProtoEnum Wildcard where
  fromInt
  | 0 => .ok .star
  | n => .error s!"Field {n} does not exist in enum"

@[inline]
def mergeWildcard (_ : PatElem) (x : Wildcard) : PatElem :=
  -- With enums we perform replacement
  match x with
  | .star => .star

@[inline]
def mergeC (_ : PatElem) (x2 : String) : PatElem :=
  -- With a single character we'll perform replacement
  match x2.toList with
  | [c2] => .justChar c2
  | _    => panic!("Only expected a single character in PatElem")

@[inline]
def merge (_ : PatElem) (y : PatElem) : PatElem :=
  -- Each constructor of the sum type merges through
  -- replacement, so we'll do the same here
  y

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn PatElem) := do
  match t.fieldNum with
  | 1 =>
    let x : Wildcard ← Field.guardedParse t
    pureMergeFn (mergeWildcard · x)
  | 2 =>
    let x : String ← Field.guardedParse t
    pureMergeFn (mergeC · x)
  | _ =>
    t.wireType.skip
    pure ignore

instance : Message PatElem where
  parseField := parseField
  merge      := merge

instance : Field Pattern := Field.fromInterField (λ (elems : Repeated PatElem) => elems.toList) (· ++ ·)

end PatElem

instance : ProtoEnum UnaryOp where
  fromInt
  | 0 => .ok .not
  | 1 => .ok .neg
  | 2 => .ok .isEmpty
  | n => .error s!"Field {n} does not exist in UnaryOp"

def UnaryOp.merge : UnaryOp → UnaryOp → UnaryOp
| .like p1, .like p2 => .like (Field.merge p1 p2)
| .is et1, .is et2   => .is (Field.merge et1 et2)
| _, op2             => op2 -- in all other cases, override

instance : Field UnaryOp := Field.fromInterField id UnaryOp.merge

namespace Proto

-- Wrapper type
def ExprKind := Expr
  deriving Inhabited

-- Recursive constructors for Expr
def ExprKind.If := ExprKind
instance : Inhabited ExprKind.If where
  default := .ite default default default

def ExprKind.And := ExprKind
instance : Inhabited ExprKind.And where
  default := .and default default

def ExprKind.Or := ExprKind
instance : Inhabited ExprKind.Or where
  default := .or default default

def ExprKind.UnaryApp := ExprKind
instance : Inhabited ExprKind.UnaryApp where
  default := .unaryApp default default

def ExprKind.BinaryApp := ExprKind
instance : Inhabited ExprKind.BinaryApp where
  default := .binaryApp default default default

def ExprKind.ExtensionFunctionApp := ExprKind
instance : Inhabited ExprKind.ExtensionFunctionApp where
  default := .call default default

def ExprKind.GetAttr := ExprKind
instance : Inhabited ExprKind.GetAttr where
  default := .getAttr default default

def ExprKind.HasAttr := ExprKind
instance : Inhabited ExprKind.HasAttr where
  default := .hasAttr default default

def ExprKind.ExtHasAttr := ExprKind
instance : Inhabited ExprKind.ExtHasAttr where
  default := .extHasAttr default default default

def ExprKind.Like := ExprKind
instance : Inhabited ExprKind.Like where
  default := .unaryApp (.like default) default

def ExprKind.Is := ExprKind
instance : Inhabited ExprKind.Is where
  default := .unaryApp (.is default) default

def ExprKind.Set := ExprKind
instance : Inhabited ExprKind.Set where
  default := .set default

def ExprKind.Record := ExprKind
instance : Inhabited ExprKind.Record where
  default := .record default

/-- Proto `All { arg: Expr = 1, pred: Expr = 2 }` (ExprKind field 17, `anyall`
feature). Accumulated as a `Spec.Expr.all` node during parsing; `pred` decodes
to a `PredExpr` (D-29). -/
def ExprKind.All := ExprKind
instance : Inhabited ExprKind.All where
  default := .all (.lit (.bool true)) .item

end Proto

def Expr.merge (e1 : Expr) (e2 : Expr) : Expr :=
  match e1, e2 with
  | .lit p1, .lit p2 => .lit (Field.merge p1 p2)
  | .var v1, .var v2 => .var (Field.merge v1 v2)
  | .ite cond1 then1 else1, .ite cond2 then2 else2 =>
    .ite (merge cond1 cond2) (merge then1 then2) (merge else1 else2)
  | .and left1 right1, .and left2 right2 =>
    .and (merge left1 left2) (merge right1 right2)
  | .or left1 right1, .or left2 right2 =>
    .or (merge left1 left2) (merge right1 right2)
  | .unaryApp op1 e1, .unaryApp op2 e2 =>
    .unaryApp (UnaryOp.merge op1 op2) (merge e1 e2)
  | .binaryApp _ left1 right1, .binaryApp op2 left2 right2 =>
    .binaryApp op2 (merge left1 left2) (merge right1 right2)
  | .getAttr e1 a1, .getAttr e2 a2 =>
    .getAttr (merge e1 e2) (Field.merge a1 a2)
  | .hasAttr e1 a1, .hasAttr e2 a2 =>
    .hasAttr (merge e1 e2) (Field.merge a1 a2)
  | .extHasAttr e1 a1 as1, .extHasAttr e2 a2 as2 =>
    .extHasAttr (merge e1 e2) (Field.merge a1 a2) (as1 ++ as2)
  | .set es1, .set es2 => .set (es1 ++ es2)
  | .record m1, .record m2 => .record (m1 ++ m2)
  | .call _ args1, .call fn2 args2 => .call fn2 (args1 ++ args2)
  | _, _ => e2

namespace Proto.ExprKind.If

@[inline]
def mergeTestExpr (result : ExprKind.If) (x : Expr) : ExprKind.If :=
  match result with
  | .ite testExpr thenExpr elseExpr => .ite (Expr.merge testExpr x) thenExpr elseExpr
  | _                               => panic!("Expected ExprKind.If to have .ite constructor")

@[inline]
def mergeThenExpr (result : ExprKind.If) (x : Expr) : ExprKind.If :=
  match result with
  | .ite testExpr thenExpr elseExpr => .ite testExpr (Expr.merge thenExpr x) elseExpr
  | _                               => panic!("Expected ExprKind.If to have .ite constructor")

@[inline]
def mergeElseExpr (result : ExprKind.If) (x : Expr) : ExprKind.If :=
  match result with
  | .ite testExpr thenExpr elseExpr => .ite testExpr thenExpr (Expr.merge elseExpr x)
  | _                               => panic!("Expected ExprKind.If to have .ite constructor")

@[inline]
def merge (x1 x2 : ExprKind.If) : ExprKind.If :=
  match x1, x2 with
  | .ite c1 t1 e1, .ite c2 t2 e2 => .ite (Expr.merge c1 c2) (Expr.merge t1 t2) (Expr.merge e1 e2)
  | _, _                         => panic!("Expected ExprKind.If to have .ite constructor")

-- parseField requires mutual recursion and thus can be found at the end
-- of the file
end Proto.ExprKind.If

namespace Proto.ExprKind.And

@[inline]
def mergeLeft (result : ExprKind.And) (x : Expr) : ExprKind.And :=
  match result with
  | .and left right => .and (Expr.merge left x) right
  | _               => panic!("Expected ExprKind.And to have .and constructor")

@[inline]
def mergeRight (result : ExprKind.And) (x : Expr) : ExprKind.And :=
  match result with
  | .and left right => .and left (Expr.merge right x)
  | _               => panic!("Expected ExprKind.And to have .and constructor")

@[inline]
def merge (x1 x2 : ExprKind.And) : ExprKind.And :=
  match x1, x2 with
  | .and l1 r1, .and l2 r2 => .and (Expr.merge l1 l2) (Expr.merge r1 r2)
  | _, _                   => panic!("Expected Proto.Expr.And to have .and constructor")

-- parseField requires mutual recursion and thus can be found at the end
-- of the file
end Proto.ExprKind.And

namespace Proto.ExprKind.Or

@[inline]
def mergeLeft (result : ExprKind.Or) (x : Expr) : ExprKind.Or :=
  match result with
  | .or left right => .or (Expr.merge left x) right
  | _              => panic!("Expected ExprKind.Or to have .or constructor")

@[inline]
def mergeRight (result : ExprKind.Or) (x : Expr) : ExprKind.Or :=
  match result with
  | .or left right => .or left (Expr.merge right x)
  | _              => panic!("Expected ExprKind.Or to have .or constructor")

@[inline]
def merge (x1 x2 : ExprKind.Or) : ExprKind.Or :=
  match x1, x2 with
  | .or l1 r1, .or l2 r2 => .or (Expr.merge l1 l2) (Expr.merge r1 r2)
  | _, _                 => panic!("Expected ExprKind.Or to have .or constructor")

-- parseField requires mutual recursion and thus can be found at the end
-- of the file
end Proto.ExprKind.Or

namespace Proto.ExprKind.UnaryApp

inductive Op where
  | not
  | neg
  | isEmpty
deriving Inhabited

namespace Op

@[inline]
def fromInt (n : Int) : Except String Op :=
  match n with
  | 0 => .ok .not
  | 1 => .ok .neg
  | 2 => .ok .isEmpty
  | n => .error s!"Field {n} does not exist in enum"

instance : Inhabited Op where
  default := .not

instance : ProtoEnum Op := {
  fromInt := fromInt
}

end Op

@[inline]
def mergeOp (result : ExprKind.UnaryApp) (x : Op) : ExprKind.UnaryApp :=
  -- Since op is an enum, we perform a replacement
  match result with
  | .unaryApp _ expr =>
    match x with
    | .not     => .unaryApp .not expr
    | .neg     => .unaryApp .neg expr
    | .isEmpty => .unaryApp .isEmpty expr
  | _                => panic!("Expected ExprKind.UnaryApp to be of constructor .unaryApp")

@[inline]
def mergeArg (result : ExprKind.UnaryApp) (e2 : Expr) : ExprKind.UnaryApp :=
  match result with
  | .unaryApp op e1 => .unaryApp op (Expr.merge e1 e2)
  | _               => panic!("Expected ExprKind.UnaryApp to be of constructor .unaryApp")

@[inline]
def merge (x1 x2 : ExprKind.UnaryApp) : ExprKind.UnaryApp :=
  match x1, x2 with
  | .unaryApp _ e1, .unaryApp op2 e2 => .unaryApp op2 (Expr.merge e1 e2)
  | _, _                             => panic!("Expected ExprKind.UnaryApp to be of constructor .unaryApp")

-- parseField requires mutual recursion and can be found at the end of the file
end Proto.ExprKind.UnaryApp

namespace Proto.ExprKind.BinaryApp

inductive Op where
  | eq
  | less
  | lesseq
  | add
  | sub
  | mul
  | in
  | contains
  | containsAll
  | containsAny
  | getTag
  | hasTag
deriving Inhabited

namespace Op

@[inline]
def fromInt (n : Int) : Except String Op :=
  match n with
  | 0 => .ok .eq
  | 1 => .ok .less
  | 2 => .ok .lesseq
  | 3 => .ok .add
  | 4 => .ok .sub
  | 5 => .ok .mul
  | 6 => .ok .in
  | 7 => .ok .contains
  | 8 => .ok .containsAll
  | 9 => .ok .containsAny
  | 10 => .ok .getTag
  | 11 => .ok .hasTag
  | n  => .error s!"Field {n} does not exist in enum"

instance : Inhabited Op where
  default := .eq

instance : ProtoEnum Op := {
  fromInt := fromInt
}

end Op

@[inline]
def mergeOp (result : ExprKind.BinaryApp) (x : Op) : ExprKind.BinaryApp :=
  match result with
  | .binaryApp _ left right =>
    match x with
    | .eq          => .binaryApp .eq left right
    | .less        => .binaryApp .less left right
    | .lesseq      => .binaryApp .lessEq left right
    | .add         => .binaryApp .add left right
    | .sub         => .binaryApp .sub left right
    | .mul         => .binaryApp .mul left right
    | .in          => .binaryApp .mem left right
    | .contains    => .binaryApp .contains left right
    | .containsAll => .binaryApp .containsAll left right
    | .containsAny => .binaryApp .containsAny left right
    | .getTag      => .binaryApp .getTag left right
    | .hasTag      => .binaryApp .hasTag left right
  | _ => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")

@[inline]
def mergeLeft (result : ExprKind.BinaryApp) (e2 : Expr) : ExprKind.BinaryApp :=
  match result with
  | .binaryApp op e1 right => .binaryApp op (Expr.merge e1 e2) right
  | _                      => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")

@[inline]
def mergeRight (result : ExprKind.BinaryApp) (e2 : Expr) : ExprKind.BinaryApp :=
  match result with
  | .binaryApp op left e1 => .binaryApp op left (Expr.merge e1 e2)
  | _                     => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")

@[inline]
def merge (x1 x2 : ExprKind.BinaryApp) : ExprKind.BinaryApp :=
  match x1, x2 with
  | .binaryApp _ l1 r1, .binaryApp op2 l2 r2 => .binaryApp op2 (Expr.merge l1 l2) (Expr.merge r1 r2)
  | _, _                                     => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")

-- parseField requires mutual recursion and can be found at the end of the file
end Proto.ExprKind.BinaryApp

namespace Proto.ExprKind.ExtensionFunctionApp

@[inline]
def mergeName (result : ExprKind.ExtensionFunctionApp) (xfn : Spec.Name) : BParsec ExprKind.ExtensionFunctionApp :=
  match result with
  | .call _ es =>
    let ret f := pure (.call f es)
    match xfn.id with
    | "decimal" => ret .decimal
    | "lessThan" => ret .lessThan
    | "lessThanOrEqual" => ret .lessThanOrEqual
    | "greaterThan" => ret .greaterThan
    | "greaterThanOrEqual" => ret .greaterThanOrEqual
    | "ip" => ret .ip
    | "isIpv4" => ret .isIpv4
    | "isIpv6" => ret .isIpv6
    | "isLoopback" => ret .isLoopback
    | "isMulticast" => ret .isMulticast
    | "isInRange" => ret .isInRange
    | "datetime" => ret .datetime
    | "duration" => ret .duration
    | "offset" => ret .offset
    | "durationSince" => ret .durationSince
    | "toDate" => ret .toDate
    | "toTime" => ret .toTime
    | "toMilliseconds" => ret .toMilliseconds
    | "toSeconds" => ret .toSeconds
    | "toMinutes" => ret .toMinutes
    | "toHours" => ret .toHours
    | "toDays" => ret .toDays
    | xfn => throw s!"mergeName: unknown extension function {xfn}"
  | _ => throw "Expected ExprKind.ExtensionFunctionApp to have constructor .call"

@[inline]
def mergeArgs (result : ExprKind.ExtensionFunctionApp) (es2 : Array Expr) : ExprKind.ExtensionFunctionApp :=
  match result with
  | .call n1 es1 => .call n1 (es1 ++ es2.toList)
  | _            => panic!("Expected ExprKind.ExtensionFunctionApp to have constructor .call")

@[inline]
def merge (x1 x2 : ExprKind.ExtensionFunctionApp) : ExprKind.ExtensionFunctionApp :=
  match x1, x2 with
  | .call _ args1, .call fn2 args2 => .call fn2 (args1 ++ args2)
  | _, _                           => panic!("Expected ExprKind.ExtensionFunctionApp to have constructor .call")

-- parseField requires mutual recursion and can be found at the end of the file
end Proto.ExprKind.ExtensionFunctionApp

namespace Proto.ExprKind.GetAttr

@[inline]
def mergeAttr (result : ExprKind.GetAttr) (attr2 : String) : ExprKind.GetAttr :=
  match result with
  | .getAttr expr attr1 => .getAttr expr (Field.merge attr1 attr2)
  | _                   => panic!("Expected ExprKind.GetAttr to be constructor .getAttr")

@[inline]
def mergeExpr (result : ExprKind.GetAttr) (e2 : Expr) : ExprKind.GetAttr :=
  match result with
  | .getAttr e1 attr => .getAttr (Expr.merge e1 e2) attr
  | _                => panic!("Expected ExprKind.GetAttr to be constructor .getAttr")

@[inline]
def merge (x1 x2 : ExprKind.GetAttr) : ExprKind.GetAttr :=
  match x1, x2 with
  | .getAttr e1 a1, .getAttr e2 a2 => .getAttr (Expr.merge e1 e2) (Field.merge a1 a2)
  | _, _                           => panic!("Expected ExprKind.GetAttr to be constructor .getAttr")

-- parseField requires mutual recursion and can be found at the end of this file
end Proto.ExprKind.GetAttr

namespace Proto.ExprKind.HasAttr

@[inline]
def mergeAttr (result : ExprKind.HasAttr) (attr2 : String) : ExprKind.HasAttr :=
  match result with
  | .hasAttr expr attr1 => .hasAttr expr (Field.merge attr1 attr2)
  | _                   => panic!("Expected ExprKind.HasAttr to be constructor .hasAttr")

@[inline]
def mergeExpr (result : ExprKind.HasAttr) (e2 : Expr) : ExprKind.HasAttr :=
  match result with
  | .hasAttr e1 attr => .hasAttr (Expr.merge e1 e2) attr
  | _                => panic!("Expected ExprKind.HasAttr to be constructor .hasAttr")

@[inline]
def merge (x1 x2 : ExprKind.HasAttr) : ExprKind.HasAttr :=
  match x1, x2 with
  | .hasAttr e1 a1, .hasAttr e2 a2 => .hasAttr (Expr.merge e1 e2) (Field.merge a1 a2)
  | _, _                           => panic!("Expected ExprKind.HasAttr to be constructor .hasAttr")

-- parseField requires mutual recursion and can be found at the end of this file
end Proto.ExprKind.HasAttr

namespace Proto.ExprKind.ExtHasAttr

@[inline]
def mergeExpr (result : ExprKind.ExtHasAttr) (e2 : Expr) : ExprKind.ExtHasAttr :=
  match result with
  | .extHasAttr e1 attr attrs => .extHasAttr (Expr.merge e1 e2) attr attrs
  | _                         => panic!("Expected ExprKind.ExtHasAttr to be constructor .extHasAttr")

@[inline]
def mergeAttrs (result : ExprKind.ExtHasAttr) (as2 : Array String) : ExprKind.ExtHasAttr :=
  -- note this assumes protobuf of syntactically correct extended has: the attr are non-empty
  -- ids
  match result with
  | .extHasAttr expr attr attrs =>
    if attr == "" && attrs == [] then
      match as2.toList with
      | []      => .extHasAttr expr attr attrs
      | a :: as => .extHasAttr expr a as
    else
      .extHasAttr expr attr (attrs ++ as2.toList)
  | _ => panic!("Expected ExprKind.ExtHasAttr to be constructor .extHasAttr")

@[inline]
def merge (x1 x2 : ExprKind.ExtHasAttr) : ExprKind.ExtHasAttr :=
  match x1, x2 with
  | .extHasAttr e1 a1 as1, .extHasAttr e2 a2 as2 => .extHasAttr (Expr.merge e1 e2) (Field.merge a1 a2) (as1 ++ as2)
  | _, _                                          => panic!("Expected ExprKind.ExtHasAttr to be constructor .extHasAttr")

-- parseField requires mutual recursion and can be found at the end of this file
end Proto.ExprKind.ExtHasAttr

namespace Proto.ExprKind.Like

@[inline]
def mergeExpr (result : ExprKind.Like) (e2 : Expr) : ExprKind.Like :=
  match result with
  | .unaryApp (.like pat) e1 => .unaryApp (.like pat) (Expr.merge e1 e2)
  | _                        => panic!("Expected ExprKind.Like to have constructor .unaryApp .like")

@[inline]
def mergePattern (result : ExprKind.Like) (pat2 : Repeated PatElem) : ExprKind.Like :=
  match result with
  | .unaryApp (.like pat1) e => .unaryApp (.like (Field.merge pat1 pat2.toList)) e
  | _                        => panic!("Expected ExprKind.Like to have constructor .unaryApp .like")

@[inline]
def merge (x1 x2 : ExprKind.Like) : ExprKind.Like :=
  match x1, x2 with
  | .unaryApp (.like p1) e1, .unaryApp (.like p2) e2 => .unaryApp (.like (Field.merge p1 p2)) (Expr.merge e1 e2)
  | _, _                                             => panic!("Expected ExprKind.Like to have constructor .unaryApp .like")

-- parseField relies on mutual recursion and can be found at the end of the file
end Proto.ExprKind.Like

namespace Proto.ExprKind.Is

@[inline]
def mergeExpr (result : ExprKind.Is) (e2 : Expr) : ExprKind.Is :=
  match result with
  | .unaryApp (.is et) e1 => .unaryApp (.is et) (Expr.merge e1 e2)
  | _                     => panic!("Expected ExprKind.Is to have constructor .unaryApp .is")

@[inline]
def mergeEt (result : ExprKind.Is) (et2 : Spec.Name) : ExprKind.Is :=
  match result with
  | .unaryApp (.is et1) e => .unaryApp (.is (Field.merge et1 et2)) e
  | _                     => panic!("Expected ExprKind.Is to have constructor .unaryApp .is")

@[inline]
def merge (x1 x2 : ExprKind.Is) : ExprKind.Is :=
  match x1, x2 with
  | .unaryApp (.is et1) e1, .unaryApp (.is et2) e2 => .unaryApp (.is (Field.merge et1 et2)) (Expr.merge e1 e2)
  | _, _                                           => panic!("Expected ExprKind.Is to have constructor .unaryApp .is")

-- parseField relies on mutual recursion and can be found at the end of the file
end Proto.ExprKind.Is

namespace Proto.ExprKind.Set

@[inline]
def mergeElems (result : ExprKind.Set) (es2 : Array Expr) : ExprKind.Set :=
  match result with
  | .set es1 => .set (es1 ++ es2.toList)
  | _        => panic!("Expected ExprKind.Set to have the .set constructor")

@[inline]
def merge (x1 x2 : ExprKind.Set) : ExprKind.Set :=
  match x1, x2 with
  | .set es1, .set es2 => .set (es1 ++ es2)
  | _, _               => panic!("Expected ExprKind.Set to have the .set constructor")

-- parseField relies on mutual recursion and can be found at the end of the file
end Proto.ExprKind.Set

namespace Proto.ExprKind.Record

@[inline]
def mergeItems (result : ExprKind.Record) (its2 : Array (String × Expr)) : ExprKind.Record :=
  match result with
  | .record its1 => .record (its1 ++ its2.toList)
  | _            => panic!("Expected ExprKind.Record to have constructor .record")

@[inline]
def merge (x1 x2 : ExprKind.Record) : ExprKind.Record :=
  match x1, x2 with
  | .record items1, .record items2 => .record (items1 ++ items2)
  | _, _                           => panic!("Expected ExprKind.Record to have constructor .record")

-- parseField relies on mutual recursion and can be found at the end of the file
end Proto.ExprKind.Record

namespace Proto.ExprKind

@[inline]
def mergePrim (result : ExprKind) (p2 : Prim) : ExprKind :=
  match result with
  | .lit p1 => .lit (Field.merge p1 p2)
  | _       => .lit p2

@[inline]
def mergeVar (result : ExprKind) (v2 : Var) : ExprKind :=
  match result with
  | .var v1 => .var (Field.merge v1 v2)
  | _       => .var v2

@[inline]
def mergeIf (result : ExprKind) (x : ExprKind.If) : ExprKind :=
  match result with
  | .ite _ _ _ => ExprKind.If.merge result x
  | _          => x

@[inline]
def mergeAnd (result : ExprKind) (x : ExprKind.And) : ExprKind :=
  match result with
  | .and _ _ => ExprKind.And.merge result x
  | _        => x

@[inline]
def mergeOr (result : ExprKind) (x : ExprKind.Or) : ExprKind :=
  match result with
  | .or _ _ => ExprKind.Or.merge result x
  | _       => x

@[inline]
def mergeUApp (result : ExprKind) (x : ExprKind.UnaryApp) : ExprKind :=
  match result with
  | .unaryApp _ _ => ExprKind.UnaryApp.merge result x
  | _             => x

@[inline]
def mergeBApp (result : ExprKind) (x : ExprKind.BinaryApp) : ExprKind :=
  match result with
  | .binaryApp _ _ _ => ExprKind.BinaryApp.merge result x
  | _                => x

@[inline]
def mergeExtApp (result : ExprKind) (x : ExprKind.ExtensionFunctionApp) : ExprKind :=
  match result with
  | .call _ _ => ExprKind.ExtensionFunctionApp.merge result x
  | _         => x

@[inline]
def mergeGetAttr (result : ExprKind) (x : ExprKind.GetAttr) : ExprKind :=
  match result with
  | .getAttr _ _ => ExprKind.GetAttr.merge result x
  | _            => x

@[inline]
def mergeHasAttr (result : ExprKind) (x : ExprKind.HasAttr) : ExprKind :=
  match result with
  | .hasAttr _ _ => ExprKind.HasAttr.merge result x
  | _            => x

@[inline]
def mergeExtHasAttr (result : ExprKind) (x : ExprKind.ExtHasAttr) : ExprKind :=
  match result with
  | .extHasAttr _ _ _ => ExprKind.ExtHasAttr.merge result x
  | _                 => x

@[inline]
def mergeLike (result : ExprKind) (x : ExprKind.Like) : ExprKind :=
  match result with
  | .unaryApp (.like _) _ => ExprKind.Like.merge result x
  | _                     => x

@[inline]
def mergeIs (result : ExprKind) (x : ExprKind.Is) : ExprKind :=
  match result with
  | .unaryApp (.is _) _ => ExprKind.Is.merge result x
  | _                   => x

@[inline]
def mergeSet (result : ExprKind) (x : ExprKind.Set) : ExprKind :=
  match result with
  | .set _ => ExprKind.Set.merge result x
  | _      => x

@[inline]
def mergeRecord (result : ExprKind) (x : ExprKind.Record) : ExprKind :=
  match result with
  | .record _ => ExprKind.Record.merge result x
  | _         => x

@[inline]
def merge (x1 x2 : ExprKind) : ExprKind :=
  Expr.merge x1 x2

-- parseField relies on mutual recursion which can be found at the
-- end of this file
end Proto.ExprKind

/-!
Proto decoder for the `.all` quantifier predicate (`anyall` feature, D-29).
The protobuf `All.pred` field is a full `Expr` message in which the element
keyword `it` is the `Item` message (field 18). Lean's `Spec.Expr` has no `Item`
leaf, so the predicate is decoded DIRECTLY into a `PredExpr` by a parser that
mirrors the `Expr` wire format but recurses into `PredExpr` for every child
(so a nested `Item` becomes `PredExpr.item`, not a dropped field). It REJECTS
field 14 (`Set` — a set term) and field 17 (`All` — a nested quantifier),
exactly as Rust's `PredExpr::try_from_expr` re-check does on untrusted bytes.
`Like`(12)/`Is`(13) map to `unaryApp .like`/`.is` as the `Expr` decoder does.

Each proto sub-message (If/And/.../Record) is given a `PredExpr` accumulator and
a pred-targeting field parser; the parsers are mutually recursive and live at the
end of the file alongside `PredExprMsg.parseField`.
-/
namespace Proto.PredExprKind
def If : Type := Spec.PredExpr
def And : Type := Spec.PredExpr
def Or : Type := Spec.PredExpr
def UApp : Type := Spec.PredExpr
def BApp : Type := Spec.PredExpr
def ExtApp : Type := Spec.PredExpr
def GetAttr : Type := Spec.PredExpr
def HasAttr : Type := Spec.PredExpr
def ExtHasAttr : Type := Spec.PredExpr
def Like : Type := Spec.PredExpr
def Is : Type := Spec.PredExpr
def Record : Type := Spec.PredExpr

instance : Inhabited If := ⟨(.ite .item .item .item : Spec.PredExpr)⟩
instance : Inhabited And := ⟨(.and .item .item : Spec.PredExpr)⟩
instance : Inhabited Or := ⟨(.or .item .item : Spec.PredExpr)⟩
instance : Inhabited UApp := ⟨(.unaryApp .not .item : Spec.PredExpr)⟩
instance : Inhabited BApp := ⟨(.binaryApp .eq .item .item : Spec.PredExpr)⟩
instance : Inhabited ExtApp := ⟨(.call .decimal [] : Spec.PredExpr)⟩
instance : Inhabited GetAttr := ⟨(.getAttr .item "" : Spec.PredExpr)⟩
instance : Inhabited HasAttr := ⟨(.hasAttr .item "" : Spec.PredExpr)⟩
instance : Inhabited ExtHasAttr := ⟨(.extHasAttr .item "" [] : Spec.PredExpr)⟩
instance : Inhabited Like := ⟨(.unaryApp (.like []) .item : Spec.PredExpr)⟩
instance : Inhabited Is := ⟨(.unaryApp (.is default) .item : Spec.PredExpr)⟩
instance : Inhabited Record := ⟨(.record [] : Spec.PredExpr)⟩
end Proto.PredExprKind

namespace Proto.ExprKind.All

/-- Merge the decoded `arg` (field 1) into the `.all` accumulator. -/
@[inline]
def mergeArg (result : ExprKind.All) (x : Spec.Expr) : ExprKind.All :=
  match result with
  | .all a p => .all (Expr.merge a x) p
  | _        => .all x .item

/-- Merge the decoded `pred` (field 2, already a `PredExpr`) in. -/
@[inline]
def mergePred (result : ExprKind.All) (p : Spec.PredExpr) : ExprKind.All :=
  match result with
  | .all a _ => .all a p
  | _        => .all (.lit (.bool true)) p

@[inline]
def merge (x1 x2 : ExprKind.All) : ExprKind.All :=
  match x1, x2 with
  | .all a1 _, .all a2 p2 => .all (Expr.merge a1 a2) p2
  | _, x2                 => x2

/-- Fold a fully-parsed `All` sub-message into the enclosing `ExprKind`. -/
@[inline]
def mergeInto (_result : ExprKind) (x : ExprKind.All) : ExprKind := x

-- parseField requires mutual recursion and is defined at the end of the file
end Proto.ExprKind.All

-- Expr depends on ExprKind and ExprKind is a sum type
-- where many of the constructors depend on Expr
mutual

partial def Proto.ExprKind.If.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.If) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.If.mergeTestExpr · x)
  | 2 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.If.mergeThenExpr · x)
  | 3 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.If.mergeElseExpr · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.And.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.And) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.And.mergeLeft · x)
  | 2 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.And.mergeRight · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.Or.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.Or) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.Or.mergeLeft · x)
  | 2 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.Or.mergeRight · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.UnaryApp.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.UnaryApp) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Proto.ExprKind.UnaryApp.Op ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.UnaryApp.mergeOp · x)
  | 2 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.UnaryApp.mergeArg · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.BinaryApp.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.BinaryApp) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Proto.ExprKind.BinaryApp.Op ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.BinaryApp.mergeOp · x)
  | 2 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.BinaryApp.mergeLeft · x)
  | 3 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.BinaryApp.mergeRight · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.ExtensionFunctionApp.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.ExtensionFunctionApp) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Spec.Name ← Field.guardedParse t
    pure (Proto.ExprKind.ExtensionFunctionApp.mergeName · x)
  | 2 =>
    let x : Repeated Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.ExtensionFunctionApp.mergeArgs · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.GetAttr.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.GetAttr) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.GetAttr.mergeExpr · x)
  | 2 =>
    let x : String ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.GetAttr.mergeAttr · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.HasAttr.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.HasAttr) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.HasAttr.mergeExpr · x)
  | 2 =>
    let x : String ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.HasAttr.mergeAttr · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.ExtHasAttr.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.ExtHasAttr) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.ExtHasAttr.mergeExpr · x)
  | 2 =>
    let x : Repeated String ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.ExtHasAttr.mergeAttrs · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.Like.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.Like) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.Like.mergeExpr · x)
  | 2 =>
    let x : Repeated PatElem ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.Like.mergePattern · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.Is.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.Is) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.Is.mergeExpr · x)
  | 2 =>
    let x : Name ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.Is.mergeEt · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.Set.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.Set) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Repeated Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.Set.mergeElems · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.Record.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.Record) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
  | 1 =>
    let x : Proto.Map String Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.Record.mergeItems · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Expr.parseField (t : Proto.Tag) : BParsec (MergeFn Expr) := do
  have : Message Proto.ExprKind.If := { parseField := Proto.ExprKind.If.parseField, merge := Proto.ExprKind.If.merge }
  have : Message Proto.ExprKind.And := { parseField := Proto.ExprKind.And.parseField, merge := Proto.ExprKind.And.merge }
  have : Message Proto.ExprKind.Or := { parseField := Proto.ExprKind.Or.parseField, merge := Proto.ExprKind.Or.merge }
  have : Message Proto.ExprKind.UnaryApp := { parseField := Proto.ExprKind.UnaryApp.parseField, merge := Proto.ExprKind.UnaryApp.merge }
  have : Message Proto.ExprKind.BinaryApp := { parseField := Proto.ExprKind.BinaryApp.parseField, merge := Proto.ExprKind.BinaryApp.merge }
  have : Message Proto.ExprKind.ExtensionFunctionApp := { parseField := Proto.ExprKind.ExtensionFunctionApp.parseField, merge := Proto.ExprKind.ExtensionFunctionApp.merge }
  have : Message Proto.ExprKind.GetAttr := { parseField := Proto.ExprKind.GetAttr.parseField, merge := Proto.ExprKind.GetAttr.merge }
  have : Message Proto.ExprKind.HasAttr := { parseField := Proto.ExprKind.HasAttr.parseField, merge := Proto.ExprKind.HasAttr.merge }
  have : Message Proto.ExprKind.ExtHasAttr := { parseField := Proto.ExprKind.ExtHasAttr.parseField, merge := Proto.ExprKind.ExtHasAttr.merge }
  have : Message Proto.ExprKind.Like := { parseField := Proto.ExprKind.Like.parseField, merge := Proto.ExprKind.Like.merge }
  have : Message Proto.ExprKind.Is := { parseField := Proto.ExprKind.Is.parseField, merge := Proto.ExprKind.Is.merge }
  have : Message Proto.ExprKind.Set := { parseField := Proto.ExprKind.Set.parseField, merge := Proto.ExprKind.Set.merge }
  have : Message Proto.ExprKind.Record := { parseField := Proto.ExprKind.Record.parseField, merge := Proto.ExprKind.Record.merge }
  have : Message Proto.ExprKind.All := { parseField := Proto.ExprKind.All.parseField, merge := Proto.ExprKind.All.merge }
  match t.fieldNum with
  | 1 =>
    let x : Prim ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergePrim · x)
  | 2 =>
    let x : Var ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeVar · x)
  | 4 =>
    let x : Proto.ExprKind.If ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeIf · x)
  | 5 =>
    let x : Proto.ExprKind.And ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeAnd · x)
  | 6 =>
    let x : Proto.ExprKind.Or ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeOr · x)
  | 7 =>
    let x : Proto.ExprKind.UnaryApp ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeUApp · x)
  | 8 =>
    let x : Proto.ExprKind.BinaryApp ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeBApp · x)
  | 9 =>
    let x : Proto.ExprKind.ExtensionFunctionApp ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeExtApp · x)
  | 10 =>
    let x : Proto.ExprKind.GetAttr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeGetAttr · x)
  | 11 =>
    let x : Proto.ExprKind.HasAttr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeHasAttr · x)
  | 12 =>
    let x : Proto.ExprKind.Like ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeLike · x)
  | 13 =>
    let x : Proto.ExprKind.Is ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeIs · x)
  | 14 =>
    let x : Proto.ExprKind.Set ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeSet · x)
  | 15 =>
    let x : Proto.ExprKind.Record ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeRecord · x)
  | 16 =>
    let x : Proto.ExprKind.ExtHasAttr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.mergeExtHasAttr · x)
  | 17 =>
    -- `.all`/`.any` set quantifier (`anyall`); `pred` is decoded into a
    -- `PredExpr` by `PredExprMsg.parseField` (D-29). `any` is encoded by Rust
    -- as the lowered `!all(!p)`, so Lean only ever sees `all`.
    let x : Proto.ExprKind.All ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.All.mergeInto · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def Proto.ExprKind.All.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.ExprKind.All) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.All.mergeArg · x)
  | 2 =>
    let p : Spec.PredExpr ← Field.guardedParse t
    pureMergeFn (Proto.ExprKind.All.mergePred · p)
  | _ =>
    t.wireType.skip
    pure ignore

-- Pred sub-message parsers: identical wire format to the `Expr` sub-messages,
-- but every child is parsed as a `PredExpr` (via `PredExprMsg`) so a nested
-- `Item` becomes `PredExpr.item`. Op/pattern/name/entity-type leaves reuse the
-- Expr-side decoders.
partial def Proto.PredExprKind.If.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.If) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .ite _ b c => .ite x b c | _ => .ite x .item .item)
  | 2 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .ite a _ c => .ite a x c | _ => .ite .item x .item)
  | 3 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .ite a b _ => .ite a b x | _ => .ite .item .item x)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.And.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.And) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .and _ b => .and x b | _ => .and x .item)
  | 2 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .and a _ => .and a x | _ => .and .item x)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.Or.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.Or) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .or _ b => .or x b | _ => .or x .item)
  | 2 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .or a _ => .or a x | _ => .or .item x)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.UApp.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.UApp) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Proto.ExprKind.UnaryApp.Op ← Field.guardedParse t
         pureMergeFn (fun r => match r, x with
           | .unaryApp _ e, .not => .unaryApp .not e
           | .unaryApp _ e, .neg => .unaryApp .neg e
           | .unaryApp _ e, .isEmpty => .unaryApp .isEmpty e
           | _, .not => .unaryApp .not .item
           | _, .neg => .unaryApp .neg .item
           | _, .isEmpty => .unaryApp .isEmpty .item)
  | 2 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .unaryApp op _ => .unaryApp op x | _ => .unaryApp .not x)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.BApp.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.BApp) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Proto.ExprKind.BinaryApp.Op ← Field.guardedParse t
         let op : Spec.BinaryOp := match x with
           | .less => .less | .lesseq => .lessEq | .add => .add | .sub => .sub | .mul => .mul
           | .in => .mem | .contains => .contains | .containsAll => .containsAll
           | .containsAny => .containsAny | .getTag => .getTag | .hasTag => .hasTag | .eq => .eq
         pureMergeFn (fun r => match r with | .binaryApp _ a b => .binaryApp op a b | _ => .binaryApp op .item .item)
  | 2 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .binaryApp op _ b => .binaryApp op x b | _ => .binaryApp .eq x .item)
  | 3 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .binaryApp op a _ => .binaryApp op a x | _ => .binaryApp .eq .item x)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.ExtApp.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.ExtApp) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.Name ← Field.guardedParse t
         let f : Spec.ExtFun ← (match x.id with
           | "decimal" => pure .decimal | "lessThan" => pure .lessThan
           | "lessThanOrEqual" => pure .lessThanOrEqual | "greaterThan" => pure .greaterThan
           | "greaterThanOrEqual" => pure .greaterThanOrEqual | "ip" => pure .ip
           | "isIpv4" => pure .isIpv4 | "isIpv6" => pure .isIpv6 | "isLoopback" => pure .isLoopback
           | "isMulticast" => pure .isMulticast | "isInRange" => pure .isInRange
           | "datetime" => pure .datetime | "duration" => pure .duration | "offset" => pure .offset
           | "durationSince" => pure .durationSince | "toDate" => pure .toDate | "toTime" => pure .toTime
           | "toMilliseconds" => pure .toMilliseconds | "toSeconds" => pure .toSeconds
           | "toMinutes" => pure .toMinutes | "toHours" => pure .toHours | "toDays" => pure .toDays
           | other => throw s!"unknown extension function {other} in quantifier predicate")
         pureMergeFn (fun r => match r with | .call _ es => .call f es | _ => .call f [])
  | 2 => let x : Repeated Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .call f es => .call f (es ++ x.toList) | _ => .call .decimal x.toList)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.GetAttr.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.GetAttr) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .getAttr _ a => .getAttr x a | _ => .getAttr x "")
  | 2 => let x : String ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .getAttr e a => .getAttr e (Field.merge a x) | _ => .getAttr .item x)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.HasAttr.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.HasAttr) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .hasAttr _ a => .hasAttr x a | _ => .hasAttr x "")
  | 2 => let x : String ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .hasAttr e a => .hasAttr e (Field.merge a x) | _ => .hasAttr .item x)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.ExtHasAttr.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.ExtHasAttr) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .extHasAttr _ a as => .extHasAttr x a as | _ => .extHasAttr x "" [])
  | 2 => let x : Repeated String ← Field.guardedParse t
         pureMergeFn (fun r => match r with
           | .extHasAttr e a as =>
             match x.toList with
             | []       => .extHasAttr e a as
             | hd :: tl => .extHasAttr e (Field.merge a hd) (as ++ tl)
           | _ => .extHasAttr .item "" x.toList)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.Like.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.Like) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .unaryApp (.like p) _ => .unaryApp (.like p) x | _ => .unaryApp (.like []) x)
  | 2 => let x : Repeated PatElem ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .unaryApp (.like p) e => .unaryApp (.like (p ++ x.toList)) e | _ => .unaryApp (.like x.toList) .item)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.Is.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.Is) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .unaryApp (.is et) _ => .unaryApp (.is et) x | _ => .unaryApp (.is default) x)
  | 2 => let x : Spec.Name ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .unaryApp (.is _) e => .unaryApp (.is x) e | _ => .unaryApp (.is x) .item)
  | _ => t.wireType.skip; pure ignore

partial def Proto.PredExprKind.Record.parseField (t : Proto.Tag) : BParsec (MergeFn Proto.PredExprKind.Record) := do
  have : Message Spec.PredExpr := { parseField := PredExprMsg.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Proto.Map String Spec.PredExpr ← Field.guardedParse t
         pureMergeFn (fun r => match r with | .record m => .record (m ++ x.toList) | _ => .record x.toList)
  | _ => t.wireType.skip; pure ignore

/-- See the `Proto.PredExprKind` docstring. Decodes the `Expr` wire format into a
`PredExpr`, recursing into `PredExpr` for every child. -/
partial def PredExprMsg.parseField (t : Proto.Tag) : BParsec (MergeFn Spec.PredExpr) := do
  have : Message Prim := { parseField := Prim.parseField, merge := Prim.merge }
  have : Message Proto.PredExprKind.If := { parseField := Proto.PredExprKind.If.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.And := { parseField := Proto.PredExprKind.And.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.Or := { parseField := Proto.PredExprKind.Or.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.UApp := { parseField := Proto.PredExprKind.UApp.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.BApp := { parseField := Proto.PredExprKind.BApp.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.ExtApp := { parseField := Proto.PredExprKind.ExtApp.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.GetAttr := { parseField := Proto.PredExprKind.GetAttr.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.HasAttr := { parseField := Proto.PredExprKind.HasAttr.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.ExtHasAttr := { parseField := Proto.PredExprKind.ExtHasAttr.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.Like := { parseField := Proto.PredExprKind.Like.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.Is := { parseField := Proto.PredExprKind.Is.parseField, merge := fun _ p => p }
  have : Message Proto.PredExprKind.Record := { parseField := Proto.PredExprKind.Record.parseField, merge := fun _ p => p }
  match t.fieldNum with
  | 1 => let x : Prim ← Field.guardedParse t
         pureMergeFn (fun _ => .lit x)
  | 2 => let x : Var ← Field.guardedParse t
         pureMergeFn (fun _ => .var x)
  | 4 => let x : Proto.PredExprKind.If ← Field.guardedParse t
         pureMergeFn (fun _ => x)
  | 5 => let x : Proto.PredExprKind.And ← Field.guardedParse t
         pureMergeFn (fun _ => x)
  | 6 => let x : Proto.PredExprKind.Or ← Field.guardedParse t
         pureMergeFn (fun _ => x)
  | 7 => let x : Proto.PredExprKind.UApp ← Field.guardedParse t
         pureMergeFn (fun _ => x)
  | 8 => let x : Proto.PredExprKind.BApp ← Field.guardedParse t
         pureMergeFn (fun _ => x)
  | 9 => let x : Proto.PredExprKind.ExtApp ← Field.guardedParse t
         pureMergeFn (fun _ => x)
  | 10 => let x : Proto.PredExprKind.GetAttr ← Field.guardedParse t
          pureMergeFn (fun _ => x)
  | 11 => let x : Proto.PredExprKind.HasAttr ← Field.guardedParse t
          pureMergeFn (fun _ => x)
  | 12 => let x : Proto.PredExprKind.Like ← Field.guardedParse t
          pureMergeFn (fun _ => x)
  | 13 => let x : Proto.PredExprKind.Is ← Field.guardedParse t
          pureMergeFn (fun _ => x)
  | 15 => let x : Proto.PredExprKind.Record ← Field.guardedParse t
          pureMergeFn (fun _ => x)
  | 16 => let x : Proto.PredExprKind.ExtHasAttr ← Field.guardedParse t
          pureMergeFn (fun _ => x)
  | 18 => t.wireType.skip; pureMergeFn (fun _ => .item)
  | 14 => throw "`.all`/`.any` predicate may not contain a set literal (set-free fragment)"
  | 17 => throw "`.all`/`.any` predicate may not contain a nested quantifier"
  | _  => t.wireType.skip; pure ignore

end

instance : Message Expr := {
  parseField := Expr.parseField,
  merge      := Expr.merge
}

end Cedar.Spec
