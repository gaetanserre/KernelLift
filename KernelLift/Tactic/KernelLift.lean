/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Lean.Elab.Tactic.Location
public import KernelLift.Lift
public import KernelLift.Tactic.LocTactic
public import KernelLift.Tactic.Universe
public import KernelLift.Tactic.Utils

/-!
# `kernel_lift` tactic

This file implements the `kernel_lift` tactic, which transforms equalities of
kernels into equivalent equalities where the kernels are lifted to a common universe level.

## Main declarations

* `liftKernel`: the main function that recursively lifts kernels in an expression, recording the
  operations performed for later rewriting.
* `mkKernelLiftEqProof`: constructs the proof of equivalence between the original and lifted
  expressions, using the recorded operations to apply the appropriate lemmas.
* `ApplyKernelLift`: core implementation of `kernel_lift` on goals and hypotheses.
* `kernel_lift`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

/-- Recursive transformation from kernel expressions to lifted kernel expressions. -/
partial def liftKernel (maxLvl : Level) (e : Expr) (op_data : List KernelOP) :
    MetaM (Expr × List KernelOP) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let η := args[args.size - 2]!
    let κ := args[args.size - 1]!
    let (η', lη) ← liftKernel maxLvl η op_data
    let (κ', lκ) ← liftKernel maxLvl κ lη
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
    let (Z, _, tLvl, _) ← getTypesFromKernel κ
    let ex ← constructMeasurableEquiv X xLvl maxLvl
    let ey ← constructMeasurableEquiv Y yLvl maxLvl
    let ez ← constructMeasurableEquiv Z tLvl maxLvl
    let OPComp := .Comp ex ey ez
    return (← mkAppM ``Kernel.comp #[η', κ'], OPComp :: lκ)
  | Expr.const ``Kernel.parallelComp _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let(κ', lκ) ← liftKernel maxLvl κ op_data
    let (η', lη) ← liftKernel maxLvl η lκ
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
    let (T, Z, tLvl, zLvl) ← getTypesFromKernel η
    let ex ← constructMeasurableEquiv X xLvl maxLvl
    let ey ← constructMeasurableEquiv Y yLvl maxLvl
    let et ← constructMeasurableEquiv T tLvl maxLvl
    let ez ← constructMeasurableEquiv Z zLvl maxLvl
    let OPParallelComp := .ParallelComp ex ey et ez
    return (← mkAppM ``Kernel.parallelComp #[κ', η'], OPParallelComp :: lη)
  | Expr.const ``Kernel.prod _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 2]!
    let η := args[args.size - 1]!
    let (κ', lκ) ← liftKernel maxLvl κ op_data
    let (η', lη) ← liftKernel maxLvl η lκ
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
    let (_, Z, _, zLvl) ← getTypesFromKernel η
    let ex ← constructMeasurableEquiv X xLvl maxLvl
    let ey ← constructMeasurableEquiv Y yLvl maxLvl
    let ez ← constructMeasurableEquiv Z zLvl maxLvl
    let OPProd := .Prod ex ey ez
    return (← mkAppM ``Kernel.prod #[κ', η'], OPProd :: lη)
  | Expr.const ``Kernel.copy _ =>
    let (X, _, xLvl, _) ← getTypesFromKernel e
    let ex ← constructMeasurableEquiv X xLvl maxLvl
    let (X', _) ← getTypesFromMeasurableEquiv ex
    let OPCopy := .Copy ex
    return (← mkAppOptM ``Kernel.copy #[X', none], OPCopy :: op_data)
  | _ =>
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
    let ex ← constructMeasurableEquiv X xLvl maxLvl
    let ey ← constructMeasurableEquiv Y yLvl maxLvl
    let t ← mkAppOptM ``Kernel.lift
      #[none, none, none, none, none, none, none, none, ex, ey, e]
    return (t, op_data)

/-- Construct the proof of equivalence between the original kernel equality and the lifted one. -/
def mkKernelLiftEqProof (eqProofType : Expr) (maxLvl : Level)
    (op_data : List KernelOP) : TacticM Expr := do
  let maxLvlStx ← liftMacroM <| levelToSyntax maxLvl
  let savedGoals ← getGoals
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  setGoals [mvarId]
  let op_data := op_data.reverse
  evalTactic (← `(tactic| apply propext))
  evalTactic (← `(tactic| constructor))
  let goalsAfterConstructor ← getGoals
  match goalsAfterConstructor with
  | [forwardGoal, backwardGoal] =>
    setGoals [forwardGoal]
    evalTactic (← `(tactic| intro h))
    for op in op_data do
      match op with
      | .Comp equivX equivY equivZ =>
        let equivXStx ← Term.exprToSyntax equivX
        let equivYStx ← Term.exprToSyntax equivY
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          lift_comp (ex := $equivXStx) (ey := $equivYStx) (ez := $equivZStx)]))
      | .ParallelComp equivX equivY equivT equivZ =>
        let equivXStx ← Term.exprToSyntax equivX
        let equivYStx ← Term.exprToSyntax equivY
        let equivTStx ← Term.exprToSyntax equivT
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          parallelComp_lift
          (ex := $equivXStx)
          (ey := $equivYStx)
          (et := $equivTStx)
          (ez := $equivZStx)
        ]))
      | .Prod equivX equivY equivZ =>
        let equivXStx ← Term.exprToSyntax equivX
        let equivYStx ← Term.exprToSyntax equivY
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          prod_lift
          (ex := $equivXStx)
          (ey := $equivYStx)
          (ez := $equivZStx)
        ]))
      | .Copy equivX =>
        let equivXStx ← Term.exprToSyntax equivX
        evalTactic (← `(tactic| nth_rw 1 [
          copy_lift
          (ex := $equivXStx)
        ]))
    evalTactic (← `(tactic| rwa [lift_congr.{_, _, $maxLvlStx}]))

    setGoals [backwardGoal]
    evalTactic (← `(tactic| intro h))
    for op in op_data do
      match op with
      | .Comp equivX equivY equivZ =>
        let equivXStx ← Term.exprToSyntax equivX
        let equivYStx ← Term.exprToSyntax equivY
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          lift_comp (ex := $equivXStx) (ey := $equivYStx) (ez := $equivZStx)] at h))
      | .ParallelComp equivX equivY equivT equivZ =>
        let equivXStx ← Term.exprToSyntax equivX
        let equivYStx ← Term.exprToSyntax equivY
        let equivTStx ← Term.exprToSyntax equivT
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          parallelComp_lift
          (ex := $equivXStx)
          (ey := $equivYStx)
          (et := $equivTStx)
          (ez := $equivZStx)
        ] at h))
      | .Prod equivX equivY equivZ =>
        let equivXStx ← Term.exprToSyntax equivX
        let equivYStx ← Term.exprToSyntax equivY
        let equivZStx ← Term.exprToSyntax equivZ
        evalTactic (← `(tactic| nth_rw 1 [
          prod_lift
          (ex := $equivXStx)
          (ey := $equivYStx)
          (ez := $equivZStx)
        ] at h))
      | .Copy equivX =>
        let equivXStx ← Term.exprToSyntax equivX
        evalTactic (← `(tactic| nth_rw 1 [
          copy_lift
          (ex := $equivXStx)
        ] at h))
    evalTactic (← `(tactic| rwa [lift_congr.{_, _, $maxLvlStx}] at h))
  | _ =>
    setGoals savedGoals
    throwError "Expected exactly two goals after `constructor`"
  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_lift equivalence proof"
  setGoals savedGoals
  instantiateMVars mvar


/-- The `kernel_lift` tactic transforms a kernel equality to an equivalent equality in
which all kernels are lifted to a common universe level.

The tactic supports location specifiers like `rw` or `simp`:
* `kernel_lift` — applies to the goal
* `kernel_lift at h` — applies to hypothesis `h`
* `kernel_lift at h₁ h₂` — applies to multiple hypotheses
* `kernel_lift at h ⊢` — applies to hypothesis `h` and the goal
* `kernel_lift at *` — applies to all hypotheses and the goal
-/
def ApplyKernelLift (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let expr ← whnfR <| ← instantiateMVars expr
    let maxLvl ← computeMaxUniverse (← collectExprUniverses expr)
    let (homExpr, op_data, _, _) ← transformEquality maxLvl expr liftKernel
    let eqProofType ← mkEq expr homExpr
    let eqProof ← mkKernelLiftEqProof eqProofType maxLvl op_data
    match fvarId with
    | some fid => do
      let mvarId ← getMainGoal
      let hProof ← mkEqMP eqProof (mkFVar fid)
      let userName := (← fid.getDecl).userName
      let mvarId ← mvarId.assert userName homExpr hProof
      let mvarId ← mvarId.tryClear fid
      let (_, mvarId) ← mvarId.intro1P
      pure mvarId
    | none => do
      let mvarId ← getMainGoal
      mvarId.replaceTargetEq homExpr eqProof

@[inherit_doc ApplyKernelLift]
syntax (name := kernelLift) "kernel_lift" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_lift $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| ApplyKernelLift
