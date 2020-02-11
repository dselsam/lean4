/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Mario Carneiro

Proving equalities in commutative rings, building on:

1. https://github.com/leanprover-community/mathlib/blob/master/src/tactic/ring2.lean
2. Grégoire, B. and Mahboubi, A., 2005, August. Proving equalities in a commutative ring done right in Coq.

-/
prelude
import Init.Data.Nat
import Init.Data.Int
import Init.Data.Array
import Init.Control.EState
import Init.Automation.Util
import Init.Lean.Expr
import Init.Lean.Meta
import Init.Lean.Elab.Tactic

namespace Automation
namespace Arithmetic

open Lean (Level Literal Expr mkApp mkAppN mkConst mkNatLit)

universe u

class Ring (α : Type u) [DecidableEq α]
extends HasOfNat α, HasAdd α, HasMul α, HasSub α, HasNeg α, HasPow α Nat :=
(add0        : ∀ (x : α), x + 0 = x)
(addC        : ∀ (x y : α), x + y = y + x)
(addA        : ∀ (x y z : α), (x + y) + z = x + (y + z))
(mul0        : ∀ (x : α), x * 0 = 0)
(mul1        : ∀ (x : α), x * 1 = x)
(mulC        : ∀ (x y : α), x * y = y * x)
(mulA        : ∀ (x y z : α), (x * y) * z = x * (y * z))
(distribL    : ∀ (x y z : α), x * (y + z) = x * y + x * z)
(negMul      : ∀ (x y : α), - (x * y) = (- x) * y)
(negAdd      : ∀ (x y : α), - (x + y) = (- x) + (- y))
(subDef      : ∀ (x y : α), x - y = x + (- y))
(pow0        : ∀ (x : α), x^0 = 1)
(powS        : ∀ (x : α) (n : Nat), x^(n + 1) = x * x^n)

inductive RExpr : Type
| atom : Nat → RExpr
| nat  : Nat → RExpr
| add  : RExpr → RExpr → RExpr
| mul  : RExpr → RExpr → RExpr
| sub  : RExpr → RExpr → RExpr
| neg  : RExpr → RExpr
| pow  : RExpr → Nat → RExpr

namespace RExpr

instance : HasOfNat RExpr   := ⟨nat⟩
instance : HasZero RExpr    := ⟨nat 0⟩ -- TODO: why are these necessary?
instance : HasOne RExpr     := ⟨nat 1⟩
instance : HasAdd RExpr     := ⟨add⟩
instance : HasMul RExpr     := ⟨mul⟩
instance : HasSub RExpr     := ⟨sub⟩
instance : HasPow RExpr Nat := ⟨pow⟩
instance : HasNeg RExpr     := ⟨neg⟩
instance : Inhabited RExpr  := ⟨0⟩

-- TODO: HasReflect typeclass, with deriving
def reflect : RExpr → Expr
| atom x    => mkAppC  `Automation.Arithmetic.RExpr.atom (mkNatLit x)
| nat  n    => mkAppC  `Automation.Arithmetic.RExpr.nat (mkNatLit n)
| add r₁ r₂ => mkAppCN `Automation.Arithmetic.RExpr.add #[reflect r₁, reflect r₂]
| mul r₁ r₂ => mkAppCN `Automation.Arithmetic.RExpr.mul #[reflect r₁, reflect r₂]
| sub r₁ r₂ => mkAppCN `Automation.Arithmetic.RExpr.sub #[reflect r₁, reflect r₂]
| neg r     => mkAppC  `Automation.Arithmetic.RExpr.neg (reflect r)
| pow r k   => mkAppCN `Automation.Arithmetic.RExpr.pow #[reflect r, mkNatLit k]

def denote {α : Type u} [DecidableEq α] [Ring α] (xs : Array α) : RExpr → α
| atom i  => xs.getD i 0
| nat n   => ofNat α n
| add x y => denote x + denote y
| mul x y => denote x * denote y
| sub x y => denote x - denote y
| pow x k => (denote x)^k
| neg x   => - (denote x)

end RExpr

abbrev Atom := Nat
abbrev Power := Nat

-- Horner expressions
-- Note: care must be taken to maintain "canonical forms"
inductive HExpr : Type
| int       : Int → HExpr
| hornerAux : ∀ (a : HExpr) (x : Atom) (k : Power) (b : HExpr), HExpr -- a[x]^k + b

namespace HExpr

instance : HasOfNat HExpr  := ⟨λ n => int n⟩
instance : HasZero HExpr   := ⟨int 0⟩
instance : HasOne HExpr    := ⟨int 0⟩
instance : Inhabited HExpr := ⟨0⟩

def hasBeq : HExpr → HExpr → Bool
| int n₁, int n₂ => n₁ == n₂
| hornerAux a₁ x₁ k₁ b₁, hornerAux a₂ x₂ k₂ b₂ => hasBeq a₁ a₂ && x₁ == x₂ && k₁ == k₂ && hasBeq b₁ b₂
| _, _ => false

instance : HasBeq HExpr := ⟨hasBeq⟩

def atom (n : Atom) : HExpr := hornerAux 1 n 1 0

-- Constructor that maintains canonical form.
def horner (a : HExpr) (x : Atom) (k : Power) (b : HExpr) : HExpr :=
match a with
| int c                 =>
  if c = 0 then b else hornerAux a x k b
| hornerAux a₁ x₁ k₁ b₁ =>
  if x₁ = x ∧ b₁ == 0 then hornerAux a₁ x (k₁ + k) b else hornerAux a x k b

partial def addConst (k₁ : Int) : HExpr → HExpr
| e₂ =>
  if k₁ == 0 then e₂ else
    match e₂ with
    | int k₂ => int (k₁ + k₂)
    | hornerAux a₂ x₂ k₂ b₂ => hornerAux a₂ x₂ k₂ (addConst b₂)

def addAux (a₁ : HExpr) (addA₁ : HExpr → HExpr) (x₁ : Atom) : HExpr → Power → HExpr → (HExpr → HExpr) → HExpr
| int c₂,                k₁, b₁, ϕ => addConst c₂ (horner a₁ x₁ k₁ b₁)
| hornerAux a₂ x₂ k₂ b₂, k₁, b₁, ϕ =>
  if x₁ < x₂ then hornerAux a₁ x₁ k₁ (ϕ $ hornerAux a₂ x₂ k₂ b₂)
  else if x₂ < x₁ then hornerAux a₂ x₂ k₂ (addAux b₂ k₁ b₁ ϕ)
  else if k₁ < k₂ then hornerAux (addAux a₂ (k₁ - k₂) 0 id) x₁ k₂ (ϕ b₂)
  else if k₂ < k₁ then hornerAux (addA₁ $ hornerAux a₂ x₁ (k₂ - k₁) 0) x₁ k₁ (ϕ b₂)
  else horner (addA₁ a₂) x₁ k₁ (ϕ b₂)

def add : HExpr → HExpr → HExpr
| int c₁,                e₂ => addConst c₁ e₂
| hornerAux a₁ x₁ k₁ b₁, e₂ => addAux a₁ (add a₁) x₁ e₂ k₁ b₁ (add b₁)

instance : HasAdd HExpr := ⟨add⟩

def neg : HExpr → HExpr
| int n => int (-n)
| hornerAux a x k b => hornerAux (neg a) x k (neg b)

instance : HasNeg HExpr := ⟨neg⟩

partial def mulConst (k₁ : Int) : HExpr → HExpr
| e₂ =>
  if k₁ = 0 then 0
  else if k₁ = 1 then e₂
  else match e₂ with
    | int k₂ => int (k₁ * k₂)
    | hornerAux a₂ x₂ n₂ b₂ => hornerAux (mulConst a₂) x₂ x₂ (mulConst b₂)

def mulAux (a₁ : HExpr) (x₁ : Atom) (k₁ : Power) (b₁ : HExpr) (mulA₁ mulB₁ : HExpr → HExpr) : HExpr → HExpr
| int k₂ => mulConst k₂ (horner a₁ x₁ k₁ b₁)
| e₂@(hornerAux a₂ x₂ k₂ b₂) =>
  if x₁ < x₂ then horner (mulA₁ e₂) x₁ k₁ (mulB₁ e₂)
  else if x₂ < x₁ then horner (mulAux a₂) x₂ k₂ (mulAux b₂)
  else
    let t : HExpr := horner (mulAux a₂) x₁ k₂ 0;
    if b₂ == 0 then t else t + horner (mulA₁ b₂) x₁ k₁ (mulB₁ b₂)

def mul : HExpr → HExpr → HExpr
| int k₁                => mulConst k₁
| hornerAux a₁ x₁ k₁ b₁ => mulAux a₁ x₁ k₁ b₁ (mul a₁) (mul b₁)

instance : HasMul HExpr := ⟨mul⟩

def pow (t : HExpr) : Nat → HExpr
| 0 => 1
| 1 => t
| k+1 => t * pow k

instance : HasPow HExpr Nat := ⟨pow⟩

end HExpr

def RExpr.toHExpr : RExpr → HExpr
| RExpr.atom x => HExpr.atom x
| RExpr.nat n  => HExpr.int n
| RExpr.add x y => x.toHExpr + y.toHExpr
| RExpr.sub x y => x.toHExpr + - y.toHExpr
| RExpr.mul x y => x.toHExpr * y.toHExpr
| RExpr.neg x   => - x.toHExpr
| RExpr.pow x k => x.toHExpr ^ k

namespace HExpr

def denote {α : Type u} [Inhabited α] [DecidableEq α] [Ring α] (xs : Array α) : HExpr → α
| (HExpr.int n)             => ofNat α n.natAbs
| (HExpr.hornerAux a x k b) => a.denote * (xs.get! x)^k + b.denote

axiom denoteCommutes {α : Type u} [Inhabited α] [DecidableEq α] [Ring α] (xs : Array α) :
  ∀ (r : RExpr), r.denote xs = r.toHExpr.denote xs

end HExpr

axiom HCorrect (α : Type u) [DecidableEq α] [Ring α] (xs : Array α) (r₁ r₂ : RExpr) :
  r₁.toHExpr = r₂.toHExpr → r₁.denote xs = r₂.denote xs

namespace Tactic

open Lean

namespace Reflect

protected structure State : Type :=
(e2idx : HashMap Lean.Expr Nat := HashMap.empty)
(atoms : Array Lean.Expr := #[])

abbrev ReflectM := StateM State

private def mkAtom (e : Lean.Expr) : ReflectM RExpr := do
lookup ← get >>= λ ϕ => pure $ ϕ.e2idx.find? e;
match lookup with
| some idx => get >>= λ ϕ => pure $ RExpr.atom idx
| none     => do
  idx ← get >>= λ ϕ => pure $ ϕ.atoms.size;
  modify $ λ ϕ => { e2idx := ϕ.e2idx.insert e idx, atoms := ϕ.atoms.push e, .. ϕ };
  pure $ RExpr.atom idx

-- TODO: numbers
partial def reflectCore : Lean.Expr → ReflectM RExpr
| e =>
  -- TODO: perf
  let f : Lean.Expr := e.getAppFn;
  let args : Array Lean.Expr := e.getAppArgs;
  match f with
  | Lean.Expr.const n _ _ =>
    if args.size == 4 && [`HasAdd.add, `HasMul.mul, `HasSub.sub].elem n then do
      t₁ ← reflectCore $ args.get! 2;
      t₂ ← reflectCore $ args.get! 3;
      let op := if n == `HasAdd.add then RExpr.add
                else if n == `HasMul.mul then RExpr.mul
                else RExpr.sub;
      pure $ op t₁ t₂
    else if args.size == 3 && n == `HasNeg.neg then do
      t ← reflectCore $ args.get! 2;
      pure $ RExpr.neg t
    else if args.size == 5 && n == `HasPow.pow then
      match args.get! 4 with
      | Lean.Expr.lit (Lean.Literal.natVal k) _ => do
        t ← reflectCore $ args.get! 3;
        pure $ RExpr.pow t k
      | _ => mkAtom e
    else
      mkAtom e
  | _ => mkAtom e

def reflectCore₂ (e₁ e₂ : Expr) : ReflectM (RExpr × RExpr) := do
r₁ ← Reflect.reflectCore e₁;
r₂ ← Reflect.reflectCore e₂;
pure $ (r₁, r₂)

end Reflect

def reflect₂ (α : Expr) (lvl : Level) (e₁ e₂ : Expr) : RExpr × RExpr × Expr :=
let ((r₁, r₂), ⟨_, atoms⟩) := (Reflect.reflectCore₂ e₁ e₂).run {};
(r₁, r₂, pushArray α [lvl.dec.getD levelZero] atoms)

open Lean.Meta

def ring (mvarId : MVarId) : MetaM Bool :=
withMVarContext mvarId $ do
  mvarType ← getMVarType mvarId;
  unless (mvarType.isAppOfArity `Eq 3) $ throwTacticEx `ring mvarId ("not an equality");
  let args : Array Lean.Expr := mvarType.getAppArgs;
  [α, e₁, e₂] ← pure args.toList | throwTacticEx `ring mvarId ("UNREACHABLE");
  lvl ← getLevel α;
  let instDecEqType := (mkApp (mkConst `DecidableEq [lvl]) α);
  instDecEq ← synthInstance instDecEqType;
  let instType := mkAppN (mkConst `Automation.ArithmeticRing [lvl]) #[α, instDecEq];
  inst ← synthInstance instType;
  let (r₁, r₂, xs) := reflect₂ α lvl e₁ e₂;
  let correctFn := mkConst `Automation.Arithmetic.HCorrect [lvl];
  let rfl := mkAppCN `Automation.Arithmetic.RExpr.toHExpr #[r₁.reflect, r₂.reflect];
  let proof : Expr := mkAppN correctFn #[α, instDecEq, inst, xs, r₁.reflect, r₂.reflect, rfl];
  assignExprMVar mvarId proof;
  pure true

-- open Lean.Elab.Tactic (Tactic liftMetaTactic)
-- @[builtinTactic ring] def evalRing : Tactic :=
-- fun stx => liftMetaTactic stx $ fun mvarId => do ring mvarId; pure []

end Tactic

end Arithmetic
end Automation
