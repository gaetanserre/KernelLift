/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelLift.ForMathlib.MeasurableEquiv
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Kernel lifting utilities

This file provides helper functions for lifting and unlifting kernel expressions, including type
extraction and equivalence construction.

## Main declarations

* `getTypesFromKernel`: extracts carrier types and universe levels from kernel expressions.
* `constructMeasurableEquiv`: recursively builds measurable equivalences.
* `transformEquality`: transforms an equality expression to an other using a provided
  transformation function.
* `unfoldKernelOp`: unfolds kernel operations in an expression for easier matching.
-/

public meta section

open Lean Meta ProbabilityTheory Elab Term

/-- Convert a Level to Syntax for use in tactic quotations. -/
partial def levelToSyntax (lvl : Level) : MacroM (TSyntax `level) := do
  match lvl with
  | Level.zero => `(level| 0)
  | Level.succ l =>
    let lStx : TSyntax `level ← levelToSyntax l
    `(level| $lStx + 1)
  | Level.param n => `(level| $(mkIdent n):ident)
  | Level.mvar _ => Macro.throwError "Cannot convert mvar level to syntax"
  | Level.max l1 l2 =>
    let l1Stx : TSyntax `level ← levelToSyntax l1
    let l2Stx : TSyntax `level ← levelToSyntax l2
    `(level| max $l1Stx $l2Stx)
  | Level.imax l1 l2 =>
    let l1Stx : TSyntax `level ← levelToSyntax l1
    let l2Stx : TSyntax `level ← levelToSyntax l2
    `(level| imax $l1Stx $l2Stx)

/-- Convert an array of expressions to an array of syntax terms. -/
def exprsToSyntax (exprs : Array Expr) : TermElabM (Array Term) := do
  exprs.mapM Term.exprToSyntax

/-- Extract `(X, Y, u, v)` from an expression of type `Kernel X Y`. -/
def getTypesFromKernel (κ : Expr) : MetaM (Expr × Expr × Level × Level) := do
  let κType ← inferType κ
  match κType.getAppFn with
  | Expr.const ``Kernel univs =>
    let args := κType.getAppArgs
    if args.size < 2 then
      throwError "Kernel type with insufficient arguments: {κType}"
    let X := args[0]!
    let Y := args[1]!
    let xLevel := univs[0]!
    let yLevel := univs[1]!
    return (X, Y, xLevel, yLevel)
  | _ => throwError "Expected a kernel type, got: {κType}"

/-- Build a measurable equivalence for `e` into universe `maxLvl` (recursive on products). -/
partial def constructMeasurableEquiv (e : Expr) (eLevel maxLvl : Level) : MetaM Expr := do
  let ewhnf ← whnf e
  match ewhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    mkAppOptM' (Expr.const `MeasurableEquiv.punit [maxLvl, eLevel]) #[]
  | Expr.const ``Prod univs =>
    let args := ewhnf.getAppArgs
    let X := args[0]!
    let Y := args[1]!
    let xLevel := univs[0]!
    let yLevel := univs[1]!
    let ex ← constructMeasurableEquiv X xLevel maxLvl
    let ey ← constructMeasurableEquiv Y yLevel maxLvl
    let res ← mkAppOptM' (Expr.const ``MeasurableEquiv.prod [xLevel, yLevel, maxLvl, maxLvl])
      #[none, none, none, none, none, none, none, none, ex, ey]
    return res
  | _ => mkAppOptM' (Expr.const ``MeasurableEquiv.ulift [eLevel, maxLvl]) #[e, none]

/-- Get departure and target types from a `MeasurableEquiv` expression. -/
def getTypesFromMeasurableEquiv (e : Expr) : MetaM (Expr × Expr) := do
  let equivT ← (whnf (← inferType e))
  match equivT.getAppFn with
  | Expr.const ``MeasurableEquiv _ =>
    let args := equivT.getAppArgs
    return (args[0]!, args[1]!)
  | _ => throwError "Expected a MeasurableEquiv, got: {e}"

/-- Get the original type from a lifted type. -/
partial def getOriginalType (t : Expr) : MetaM (Expr × Level) := do
  let twhnf ← whnf t
  match twhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    return (Expr.const ``Unit [], 0)
  | Expr.const ``ULift univs =>
    return (twhnf.getAppArgs[0]!, univs[1]!)
  | Expr.const ``Prod _ =>
    let args := twhnf.getAppArgs
    let (X, xLvl) ← getOriginalType args[0]!
    let (Y, yLvl) ← getOriginalType args[1]!
    return (← mkAppM ``Prod #[X, Y], .max xLvl yLvl)
  | _ =>
    return (t, ← getDecLevel (← inferType t))

/-- Kernel operations recorded during transformation for later rewriting. -/
inductive KernelOP
  | Comp (ex ey ez κ η : Expr)
  | ParallelComp (ez ey ez et : Expr)
  | Prod (ex ey ez : Expr)
  | CompProd (ex ey ez : Expr)
  | Id (ex : Expr)
  | Discard (ex : Expr)
  | Copy (ex : Expr)
  | Swap (ex ey : Expr)

instance : ToMessageData KernelOP where
  toMessageData
    | .Comp ex ey ez κ η => m!"Composition with {ex}, {ey}, {ez}, {κ}, {η}"
    | .ParallelComp ex ey ez et =>
      m!"Parallel composition with {ex}, {ey}, {ez}, {et}"
    | .Prod ex ey ez => m!"Product with {ex}, {ey}, {ez}"
    | .CompProd ex ey ez => m!"CompProd with {ex}, {ey}, {ez}"
    | .Id ex => m!"Identity with {ex}"
    | .Discard ex => m!"Discard with {ex}"
    | .Copy ex => m!"Copy with {ex}"
    | .Swap ex ey => m!"Swap with {ex}, {ey}"

/-- Transform both sides of an equality and return the new equality plus metadata. -/
def transformEquality (e : Expr) (OP : Type)
    (transform : Expr → List OP → MetaM (Expr × List OP)) :
    MetaM (Expr × List OP × Expr × Expr) := do
  let e ← whnfR (← zetaReduce (← instantiateMVars e))
  let e := e.consumeMData
  let some (_, lhs, rhs) := e.eq? | throwError "Expected an equality, got: {e}"
  let (lhs', lh) ← transform lhs []
  let (rhs', rh) ← transform rhs lh
  return (← mkEq lhs' rhs', rh, lhs, rhs)

def Lean.MVarId.nth_rewrite (mvarId : MVarId) (n : Nat) (eq : Expr) : MetaM MVarId := do
  let r ← mvarId.rewrite (← mvarId.getType) eq (config := { occs := .pos [n] })
  mvarId.replaceTargetEq r.eNew r.eqProof
