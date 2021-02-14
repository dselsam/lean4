/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean

namespace Lean.Inspect

inductive Object : Type
  | unsupported : Object
  | ctor        : Nat → Array Object → Object
  | closure     : Option Name → Nat → Array Object → Object
  | scalar      : Nat → Object
  | error       : Nat → Object
  | default     : Nat → Object
  deriving Repr, Inhabited, BEq

structure Result : Type where
  obj : Object
  env : Environment

-- set_option trace.compiler.ir.result true in
@[noinline] def inspect (thing : NonScalar) : IO Result := do
  let env ← mkEmptyEnvironment 0
  match thing with
  | NonScalar.mk k => pure { obj := Object.default k, env := env }

-- set_option trace.compiler.ir.result true in
@[noinline] unsafe def renderUnsafe {α : Type} (thing : α) : IO Unit := do
  let result ← inspect (unsafeCast thing)
  println! "[render] {repr result.obj}"

@[implementedBy renderUnsafe]
constant render {α : Type} (thing : α) : IO Unit

end Lean.Inspect
