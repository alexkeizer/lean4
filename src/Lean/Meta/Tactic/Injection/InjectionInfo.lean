/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Basic
import Lean.Meta.Check
import Lean.ScopedEnvExtension
import Lean.Util.Recognizers

namespace Lean.Meta

structure InjectionInfo where
  /-- The name of the injectivity theorem -/
  declName : Name
  /-- The number of arguments *before* the final `f ... = f ...` hypothesis -/
  args : Nat
  /-- The consequents of the injectivity theorem. 
      E.g., if the resulting prop is `A ∧ B ∧ C`, then there are three consequents 
      (`A`, `B` and `C`) -/
  consequents : List Expr
  deriving Inhabited, Repr

structure CustomInjection where
  /-- The name of the right-hand-side function which the injectivity theorem applies to -/
  lhsName : Name
  /-- The name of the left-hand-side function which the injectivity theorem applies to -/
  rhsName : Name
  injInfo  : InjectionInfo
  deriving Inhabited, Repr

structure CustomInjections where
  map : SMap (Name × Name) InjectionInfo := {}
  deriving Inhabited, Repr

/-- 
  Apply the injection theorem to an equality of the right form. 
  All other arguments to the theorem are treated as implicit arguments and inferred -/
def InjectionInfo.applyTo (inj : InjectionInfo) (hEq : Expr) : MetaM Expr := do
  mkAppOptM inj.declName (Array.push ⟨List.replicate inj.args none⟩ <| some hEq)

def addCustomInjectionEntry (es : CustomInjections) (e : CustomInjection) : CustomInjections :=
  match es with
  | { map := map } => { map := map.insert (e.lhsName, e.rhsName) e.injInfo }

builtin_initialize customInjectionExt : SimpleScopedEnvExtension CustomInjection CustomInjections ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := addCustomInjectionEntry
    finalizeImport := fun { map := map } => { map := map.switch }
  }

open Expr in
/--
  Register a theorem which has an equality hypothesis of the form `f ... = g ...`, where 
  `f` and `g` are constants, as an injectivity theorem for the pair `(f, g)`
-/
partial def mkCustomInjection (declName : Name) : MetaM CustomInjection := do
  let info ← getConstInfo declName
  forallTelescopeReducing info.type fun xs resultType => do
    if xs.size = 0 then
      throwError "Expected a hypothesis of the form `f ... = g ...`, but {declName} is a constant"
    else
      let h ← inferType xs[xs.size-1]! -- this is OK, since we know that xs.size ≠ 0
      let some (_, x, y) := eq? h 
        | throwError f!"Expected equality, found {h}"

      let f₁ := getAppFn x
      let some (lhsName) := constName? f₁ | throwError f!"Expected constant, found {f₁}"

      let f₂ := getAppFn y
      let some (rhsName) := constName? f₂ | throwError f!"Expected constant, found {f₂}"

      return {
        lhsName, rhsName,
        injInfo := {
          declName
          args := xs.size - 1,
          -- consequents := consequents resultType
          consequents := [resultType]
        }
      }  
  where 
    consequents (e : Expr) : List Expr :=
      match and? e with
        | some (e₁, e₂) => e₁ :: consequents e₂
        | none => [e]

def addCustomInjection (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  let e ← mkCustomInjection declName
  customInjectionExt.add e attrKind

builtin_initialize
  registerBuiltinAttribute {
    name  := `injection
    descr := "custom injectivitiy theorem for the `injection` tactic"
    add   := fun declName _ attrKind => do
      discard <| addCustomInjection declName attrKind |>.run {} {}
  }

open Expr in
/-- Find a custom injectivity theorem for equation `lhs = rhs`, if registered -/
def getCustomInjection? (lhs rhs : Expr) : MetaM (Option InjectionInfo) := do
  let env ← getEnv
  let lhs := getAppFn (consumeMData lhs)
  let rhs := getAppFn (consumeMData rhs)
  trace[Meta.Tactic.injection] "Found head expressions: `{lhs}` and `{rhs}`"
  let (some lhsName, some rhsName) := (constName? (getAppFn lhs), constName? (getAppFn rhs))
    | return none
  trace[Meta.Tactic.injection] "Head expressions are constants: `{lhsName}` and `{rhsName}`"
  return customInjectionExt.getState env |>.map.find? (lhsName, rhsName)

end Lean.Meta