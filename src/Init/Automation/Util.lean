/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
prelude

import Init.Data.List
import Init.Data.Array
import Init.Lean.Expr

namespace Automation
open Lean (Name Level Expr mkConst mkApp mkAppN)

universe u

-- Input:  (ts : Array Expr) where each `t` has type `α`.
-- Output: (t : Expr) that has type `List α`
private partial def pushArrayCore (α : Expr) (lvls : List Level) (ts : Array Expr) : Nat → Expr
| i =>
  if h : i < ts.size then
    mkAppN (mkConst `List.cons lvls) #[α, ts.get ⟨i, h⟩, pushArrayCore (i+1)]
  else
    mkApp (mkConst `List.nil lvls) α

-- Input:  (ts : Array Expr) where each `t` has type `α`.
-- Output: (t : Expr) that has type `Array α`
def pushArray (α : Expr) (lvls : List Level) (ts : Array Expr) : Expr :=
mkAppN (mkConst `List.toArray lvls) #[α, pushArrayCore α lvls ts 0]

instance {α : Type u} [HasOfNat α] : HasZero α := ⟨ofNat α 0⟩
instance {α : Type u} [HasOfNat α] : HasOne  α := ⟨ofNat α 1⟩

def mkAppC (n : Name) (e : Expr) : Expr := mkApp (mkConst n []) e
def mkAppCN (n : Name) (es : Array Expr) : Expr := mkAppN (mkConst n []) es

end Automation
