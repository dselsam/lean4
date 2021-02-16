/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean.Compiler.IR

namespace Lean.Inspect

inductive Object : Type
  | ctor        : Nat → Array Object → Object
  | closure     : (fileName symbolName : Option String) → Nat → Array Object → Object
  | scalar      : Nat → Object
  | unsupported : Object /- TODO(dselsam): other kinds -/
  deriving Repr, Inhabited, BEq

end Inspect

@[extern "lean_inspect"]
constant inspect (thing : PNonScalar) : IO Inspect.Object

end Lean
