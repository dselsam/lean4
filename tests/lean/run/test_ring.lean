import Init.Automation.Arithmetic.Ring

open Automation.Arithmetic
open Automation.Arithmetic.Tactic

open Lean
open Lean.Meta

--set_option pp.all true

namespace Lean
namespace KernelException
def hasToString : KernelException → String
| unknownConstant _ n => "unknownConstant: " ++ toString n
| alreadyDeclared _ n => "alreadyDeclared: " ++ toString n
| declTypeMismatch _ (Declaration.defnDecl val) gt => "declTypeMismatch: " ++ "\n\nDecl type: " ++ toString val.type ++ "\nGiven type: " ++ toString gt
| declTypeMismatch _ d gt => "declTypeMismatch: " ++ toString gt
| declHasMVars _ n _ => "declHasMVars: " ++ toString n
| declHasFVars _ n _ => "declHasFVars: " ++ toString n
| funExpected _ _ e => "funExpected: " ++ toString e
| typeExpected _ _ e => "typeExpected: " ++ toString e
| letTypeMismatch _ _ n gt et => "letTypeMismatch: " ++ toString n
| exprTypeMismatch _ _ e et => "exprTypeMismatch: " ++ toString e
| appTypeMismatch _ _ app ft argt => "appTypeMismatch: " ++ toString app ++ "\n\nfType: " ++ toString ft ++ "\nargType: " ++ toString argt
| invalidProj _ _ e => "invalidProj: " ++ toString e
| other msg => msg

instance : HasToString KernelException := ⟨hasToString⟩

end KernelException
end Lean

def solve (newName propName : Name) : MetaM Unit := do
  some cInfo ← getConst propName | throw $ Exception.other (toString propName ++ " not found");
  let thm : Expr := cInfo.value!;
  unless (thm.isAppOfArity `Eq 3) $ throw $ Exception.other (toString thm ++ " not an equality");
  let args : Array Lean.Expr := thm.getAppArgs;
  [α, e₁, e₂] ← pure args.toList | throw $ Exception.other "UNREACHABLE";
  lvl ← getLevel α;
  let instDecEqType := (mkApp (mkConst `DecidableEq [lvl]) α);
  instDecEq ← synthInstance instDecEqType;
  let lvlDec : Level := lvl.dec.getD levelZero;
  let instType := mkAppN (mkConst `Automation.Arithmetic.Ring [lvlDec]) #[α, instDecEq];
  inst ← synthInstance instType;
  let (r₁, r₂, xs) := reflect₂ α lvl e₁ e₂;
  let correctFn := mkConst `Automation.Arithmetic.HCorrect [lvlDec];
  let HRefl : Expr := mkConst `Automation.Arithmetic.HExpr [];
  let rfl := mkAppN (mkConst `Eq.refl [lvl])
             #[HRefl, Automation.mkAppC `Automation.Arithmetic.RExpr.toHExpr r₁.reflect];
  let proof : Expr := mkAppN correctFn #[α, instDecEq, inst, xs, r₁.reflect, r₂.reflect, rfl];
  proofType ← inferType proof;
  env ← getEnv;
  opts ← getOptions;
  dbgTrace (toString $ ppExpr env {} {} opts proofType) $ fun _ => do
  env ← getEnv;
  match env.addDecl $ Declaration.defnDecl (DefinitionVal.mk ⟨newName, [], thm⟩ proof ReducibilityHints.opaque false) with
  | Except.error ε => throw $ Exception.other $ toString ε
  | Except.ok _ => pure ()


namespace Test

axiom α : Type
axiom SKIP {α : Type} : α

noncomputable instance : DecidableEq α := λ (x y : α) => SKIP
noncomputable instance : Ring α := SKIP

axiom x : α
axiom y : α

def goal1 : Prop := (0 : α) = (0 : α)
def goal2 : Prop := x * (y + x) = x * x + y * x
#eval solve `ex1 `Test.goal2


end Test
