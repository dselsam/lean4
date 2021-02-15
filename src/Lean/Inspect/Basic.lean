/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean.Compiler.IR

namespace Lean.Inspect

inductive Object : Type
  | ctor        : Nat → Array Object → Object
  | closure     : Option Name → Nat → Array Object → Object
  | scalar      : Nat → Object
  | unsupported : Object
  | error       : Nat → Object
  deriving Repr, Inhabited, BEq

structure Result : Type where
  obj : Object
  env : Environment

@[noinline] def inspectCore (thing : NonScalar) : IO Result := do
  let env ← mkEmptyEnvironment 0
  match thing with
  | NonScalar.mk k => pure { obj := Object.error k, env := env }

@[noinline] unsafe def inspectUnsafe {α : Type} (thing : α) : IO Result :=
  inspectCore (unsafeCast thing)

@[implementedBy inspectUnsafe]
constant inspect {α : Type} (thing : α) : IO Result

end Lean.Inspect
