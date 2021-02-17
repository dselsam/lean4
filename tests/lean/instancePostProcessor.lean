import Lean.Meta

class Zero (α : Type u) := (zero : α)
class One  (α : Type u) := (one : α)

universes u
variable {α : Type u} [Zero α] [One α] [Add α]

def bit0 (x : α) : α := x + x
def bit1 (x : α) : α := bit0 x + One.one

instance instOne2Inhabited : Inhabited α := ⟨Zero.zero⟩

open Lean Lean.Meta

partial def nat2bits (n : Nat) : α :=
  if n == 0 then Zero.zero
  else if n == 1 then One.one
  else if n % 2 == 1 then bit1 (nat2bits (n / 2))
  else bit0 (nat2bits (n / 2))

instance instBits2Nat (n : Nat) : OfNat α n := ⟨nat2bits n⟩

open Lean.Meta (mkAppM instantiateMVars)

partial def nat2bitsExpr (lvl : Level) (type zero one add : Expr) (n : Nat) : MetaM Expr := do
  if      n == 0 then mkAppN (mkConst `Zero.zero [lvl]) #[type, zero]
  else if n == 1 then mkAppN (mkConst `One.one [lvl]) #[type, one]
  else
    let rec ← nat2bitsExpr lvl type zero one add (n/2)
    if n % 2 == 0 then mkAppN (mkConst `bit0 [lvl]) #[type, add, rec]
    else               mkAppN (mkConst `bit1 [lvl]) #[type, one, add, rec]

@[instancePostProcessor instBits2Nat]
def instBits2NatPostProcessor : Lean.Meta.InstancePostProcessor := {
  apply := λ e => do
    let lvl  := e.getAppFn.constLevels!.head!
    let #[type, zero, one, add, n] ← pure e.getAppArgs | throwError "foo"
    match (← instantiateMVars n).natLit? with
    | none   => pure none
    | some n =>
      let x ← nat2bitsExpr lvl type zero one add n
      pure $ some $ mkAppN (mkConst `OfNat.mk [lvl]) #[type, mkNatLit n, x]
}

set_option pp.all true
#check (0 : α)
#check (1 : α)
#check (2 : α)
#check (5 : α)
