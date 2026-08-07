/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelLift.Tactic.Test.Lift

public meta section

open Lean Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

def liftComposition (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.comp do
    throwError "Expected a composition of kernels, but got {e}"
  let args := e.getAppArgs
  let η := args[args.size - 2]!
  let κ := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
  let (Z, _, tLvl, _) ← getTypesFromKernel κ
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z tLvl maxLvl
  let comp_lift_expr ← mkAppM ``comp_lift #[ex, ey, ez, η, κ]
  let (η', proofs_η) ← liftExpr η maxLvl proofs
  let (κ', proofs_κ) ← liftExpr κ maxLvl proofs_η
  return (← mkAppM ``Kernel.comp #[η', κ'], comp_lift_expr :: proofs_κ)

--initialize registerLiftExpr liftComposition

def liftParallelComp (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.parallelComp do
    throwError "Expected a parallel composition of kernels, but got {e}"
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  let et ← constructMeasurableEquiv T tLvl maxLvl
  let parallelComp_lift_expr ← mkAppM ``parallelComp_lift #[ex, ey, ez, et, κ, η]
  let (κ', proofs_κ) ← liftExpr κ maxLvl proofs
  let (η', proofs_η) ← liftExpr η maxLvl proofs_κ
  return (← mkAppM ``Kernel.parallelComp #[κ', η'], parallelComp_lift_expr :: proofs_η)

--initialize registerLiftExpr liftParallelComp

def liftProd (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.prod do
    throwError "Expected a product of kernels, but got {e}"
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (_, Z, _, zLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  let prod_lift_expr ← mkAppM ``prod_lift #[ex, ey, ez, κ, η]
  let (κ', proofs_κ) ← liftExpr κ maxLvl proofs
  let (η', proofs_η) ← liftExpr η maxLvl proofs_κ
  return (← mkAppM ``Kernel.prod #[κ', η'], prod_lift_expr :: proofs_η)

--initialize registerLiftExpr liftProd

def liftCompProd (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.compProd do
    throwError "Expected a composition of product of kernels, but got {e}"
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (_, Z, _, zLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  let compProd_lift_expr ← mkAppM ``compProd_lift #[ex, ey, ez, κ, η]
  let (κ', proofs_κ) ← liftExpr κ maxLvl proofs
  let (η', proofs_η) ← liftExpr η maxLvl proofs_κ
  return (← mkAppM ``Kernel.compProd #[κ', η'], compProd_lift_expr :: proofs_η)

--initialize registerLiftExpr liftCompProd

def liftId (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.id do
    throwError "Expected the identity kernel, but got {e}"
  let (X, _, xLvl, _) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let mX' ← synthInstance (mkApp (Expr.const ``MeasurableSpace [maxLvl]) X')
  let id_lift_expr ← mkAppM ``id_lift #[ex]
  return (← mkAppOptM ``Kernel.id #[X', mX'], id_lift_expr :: proofs)

--initialize registerLiftExpr liftId

def liftDiscard (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  logInfo "TESTTTTT"
  unless e.isAppOf ``Kernel.discard do
    throwError "Expected the discard kernel, but got {e}"
  let (X, _, xLvl, _) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  logInfo m!"Discard"
  let discard_lift_expr ← mkAppM ``discard_lift #[ex]
  let discard_const := Expr.const ``Kernel.discard [maxLvl, maxLvl]
  return (← mkAppOptM' discard_const #[X', none], discard_lift_expr :: proofs)

initialize registerLiftExpr liftDiscard

def liftCopy (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.copy do
    throwError "Expected the copy kernel, but got {e}"
  let (X, _, xLvl, _) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let copy_lift_expr ← mkAppM ``copy_lift #[ex]
  return (← mkAppOptM ``Kernel.copy #[X', none], copy_lift_expr :: proofs)

--initialize registerLiftExpr liftCopy

def liftSwap (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  unless e.isAppOf ``Kernel.swap do
    throwError "Expected the swap kernel, but got {e}"
  let args := e.getAppArgs
  let X := args[0]!
  let Y := args[1]!
  let xLvl := (← getDecLevel X)
  let yLvl := (← getDecLevel Y)
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let (Y', _) ← getTypesFromMeasurableEquiv ey
  let swap_lift_expr ← mkAppM ``swap_lift #[ex, ey]
  return (← mkAppOptM ``Kernel.swap #[X', Y', none, none], swap_lift_expr :: proofs)

initialize registerLiftExpr liftSwap

def liftKernel (e : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM (Expr × List Expr) := do
  logInfo m!"TESTTTTT {e}"
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let expr ← mkAppOptM ``Kernel.lift
    #[none, none, none, none, none, none, none, none, ex, ey, e]
  return (expr, proofs)

--initialize registerLiftExpr liftKernel

def finisherKernel (lhs rhs : Expr) (maxLvl : Level) : MetaM Expr := do
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel lhs
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  mkAppM ``lift_congr #[ex, ey, lhs, rhs]

initialize registerLiftFinisher finisherKernel

end
