/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Lean.Meta.DecLevel
public import Lean.Meta.Transform
public import Lean.Util.Recognizers
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Universe level utilities

This file provides utilities for working with universe levels in metaprograms.
It includes conversion functions between levels and syntax, and universe level collection.

## Main declarations

* `collectExprUniverses`: recursively collects universe levels from expressions.
* `getUniverseFromEq`: extracts the universe level from the left-hand side of an equality
expression.
-/

public meta section

open Lean Meta ProbabilityTheory

/-- Recursively traverses a kernel expression and collects all universe levels. -/
partial def collectKernelLevels.aux (e : Expr) : MetaM (List Level) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let η := args[args.size - 2]!
    let κ := args[args.size - 1]!
    return (← collectKernelLevels.aux η) ++ (← collectKernelLevels.aux κ)
  | Expr.const ``Kernel.parallelComp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    return (← collectKernelLevels.aux κ) ++ (← collectKernelLevels.aux η)
  | Expr.const ``Kernel.prod _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    return (← collectKernelLevels.aux κ) ++ (← collectKernelLevels.aux η)
  | _ =>
    let t ← inferType e
    match t.getAppFn with
    | Expr.const ``Kernel univs => return univs
    | _ => throwError "Expected a kernel type, got: {e} : {t}"

/-- Recursively traverse an expression and collect universe levels found.
Returns a list of all unique universe levels encountered. -/
def collectKernelLevels (e : Expr) : MetaM (List Level) := do
  return (← collectKernelLevels.aux e).eraseDups

/-- Extract all universe levels appearing in a kernel equality expression. -/
def collectEqKernelLevels (eq : Expr) : MetaM (List Level) := do
  let eq ← whnf (← zetaReduce (← instantiateMVars eq))
  let eq := eq.consumeMData
  let some (_, lhs, rhs) := eq.eq? | throwError "Expected an equality, got: {eq}"
  let lhsKernelLevels ← collectKernelLevels lhs
  let rhsKernelLevels ← collectKernelLevels rhs
  return (lhsKernelLevels ++ rhsKernelLevels).eraseDups

/-- Compute the maximum universe level from a list of levels. -/
def computeMaxLevel (levels : List Level) : MetaM Level :=
  match levels with
    | [] => throwError "Expected at least one universe level, got an empty list"
    | head :: tail => pure (tail.foldl Level.max head)

/-- Extract the universe level from the left side of an equality expression. -/
def getLevelFromEq (eq : Expr) : MetaM Level := do
  let eq ← whnf (← zetaReduce (← instantiateMVars eq))
  let eq := eq.consumeMData
  let some (_, lhs, _) := eq.eq? | throwError "Expected an equality, got: {eq}"
  getDecLevel (← inferType lhs)
