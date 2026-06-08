/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelLift.Tactic.KernelLift
import KernelLift.Tactic.Universe
public import KernelLift.Lift

/-!
# `kernel_unlift` tactic

This file implements the `kernel_unlift` tactic, the inverse of `kernel_lift`.
It transforms equalities of lifted kernels back into equalities of the original kernels.

## Main declarations
* `unliftKernel`: the main function that recursively transforms lifted kernel expressions back to
  their original form, recording the operations performed for later rewriting.
* `mkKernelUnliftEqProof`: constructs the proof of equivalence between the lifted and original
  expressions, using the recorded operations to apply the appropriate lemmas.
* `ApplyKernelUnlift`: core implementation of `kernel_unlift` on goals and hypotheses.
* `kernel_unlift`: user-facing tactic (with location support).
-/

public meta section

open Lean Elab Tactic Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

/-- Recursive transformation from lifted kernel expressions back to original kernel expressions. -/
partial def unliftKernel (eLvl : Level) (e : Expr) (op_data : List KernelOP) :
    MetaM (Expr × List KernelOP) := do
  match e.getAppFn with
  | Expr.const ``Kernel.comp _ =>
    let args := e.getAppArgs
    let η' := args[args.size - 2]!
    let κ' := args[args.size - 1]!
    let (η, lη) ← unliftKernel eLvl η' op_data
    let (κ, lκ) ← unliftKernel eLvl κ' lη
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
    let (Z, _, tLvl, _) ← getTypesFromKernel κ
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let ez ← constructMeasurableEquiv Z tLvl eLvl
    let OPComp := .Comp ex ey ez
    return (← mkAppM ``Kernel.comp #[η, κ], OPComp :: lκ)
  | Expr.const ``Kernel.parallelComp _ =>
    let args := e.getAppArgs
    let κ' := args[args.size - 2]!
    let η' := args[args.size - 1]!
    let (κ, lκ) ← unliftKernel eLvl κ' op_data
    let (η, lη) ← unliftKernel eLvl η' lκ
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
    let (T, Z, tLvl, zLvl) ← getTypesFromKernel η
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let et ← constructMeasurableEquiv T tLvl eLvl
    let ez ← constructMeasurableEquiv Z zLvl eLvl
    let OPParallelComp := .ParallelComp ex ey et ez
    return (← mkAppM ``Kernel.parallelComp #[κ, η], OPParallelComp :: lη)
  | Expr.const ``Kernel.prod _ =>
    let args := e.getAppArgs
    let κ' := args[args.size - 2]!
    let η' := args[args.size - 1]!
    let (κ, lκ) ← unliftKernel eLvl κ' op_data
    let (η, lη) ← unliftKernel eLvl η' lκ
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
    let (_, Z, _, zLvl) ← getTypesFromKernel η
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let ez ← constructMeasurableEquiv Z zLvl eLvl
    let OPProd := .Prod ex ey ez
    return (← mkAppM ``Kernel.prod #[κ, η], OPProd :: lη)
  | Expr.const ``Kernel.id _ =>
    let (X', _, _, _) ← getTypesFromKernel e
    let (X, xLvl) ← getOriginalType X'
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let mX ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLvl]) X)
    let OPId := .Id ex
    return (← mkAppOptM ``Kernel.id #[X, mX], OPId :: op_data)
  | Expr.const ``Kernel.discard _ =>
    let (X', _, _, _) ← getTypesFromKernel e
    let (X, xLvl) ← getOriginalType X'
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let OPDiscard := .Discard ex
    let discard_const := Expr.const ``Kernel.discard [xLvl, 0]
    return (← mkAppOptM' discard_const #[X, none], OPDiscard :: op_data)
  | Expr.const ``Kernel.copy _ =>
    let (X', _, _, _) ← getTypesFromKernel e
    let (X, xLvl) ← getOriginalType X'
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let OPCopy := .Copy ex
    return (← mkAppOptM ``Kernel.copy #[X, none], OPCopy :: op_data)
  | Expr.const ``Kernel.swap _ =>
    let args := e.getAppArgs
    let X' := args[0]!
    let Y' := args[1]!
    let (X, xLvl) ← getOriginalType X'
    let (Y, yLvl) ← getOriginalType Y'
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let OPSwap := .Swap ex ey
    return (← mkAppOptM ``Kernel.swap #[X, Y, none, none], OPSwap :: op_data)
  | Expr.const ``Kernel.lift _ =>
    let args := e.getAppArgs
    let κ := args[args.size - 1]!
    return (κ, op_data)
  | _ => return (e, op_data)

/-- Construct the proof of equivalence between the lifted kernel equality and the original one. -/
def mkKernelUnliftEqProof (eqProofType : Expr) (eLvl : Level) (op_data : List KernelOP) :
    TacticM Expr := do
  let eLvlStx ← liftMacroM <| levelToSyntax eLvl
  let savedGoals ← getGoals
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  setGoals [mvarId]
  let op_data := op_data.reverse
  evalTactic (← `(tactic| apply propext))
  for op in op_data do
    match op with
    | .Comp equivX equivY equivZ =>
      let equivXStx ← Term.exprToSyntax equivX
      let equivYStx ← Term.exprToSyntax equivY
      let equivZStx ← Term.exprToSyntax equivZ
      evalTactic (← `(tactic| nth_rw 1 [
        comp_lift (ex := $equivXStx) (ey := $equivYStx) (ez := $equivZStx)]))
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
    | .Id equivX =>
      let equivXStx ← Term.exprToSyntax equivX
      evalTactic (← `(tactic| nth_rw 1 [
        id_lift
        (ex := $equivXStx)
      ]))
    | .Discard equivX =>
      let equivXStx ← Term.exprToSyntax equivX
      evalTactic (← `(tactic| nth_rw 1 [
        discard_lift
        (ex := $equivXStx)
      ]))
    | .Copy equivX =>
      let equivXStx ← Term.exprToSyntax equivX
      evalTactic (← `(tactic| nth_rw 1 [
        copy_lift
        (ex := $equivXStx)
      ]))
    | .Swap equivX equivY =>
      let equivXStx ← Term.exprToSyntax equivX
      let equivYStx ← Term.exprToSyntax equivY
      evalTactic (← `(tactic| nth_rw 1 [
        swap_lift
        (ex := $equivXStx)
        (ey := $equivYStx)
      ]))
  evalTactic (← `(tactic| rw [lift_congr.{_, _, $eLvlStx}]))
  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_lift equivalence proof"
  setGoals savedGoals
  instantiateMVars mvar

/-- Extract the original kernel equality from a lifted kernel equality -/
def UnliftEquality (eq : Expr) : MetaM (Expr × List KernelOP × Level) := do
  let eq ← whnfR <| ← instantiateMVars eq
  let eLvl ← getLevelFromEq eq
  let (homExpr, op_data, _, _) ← transformEquality eq KernelOP <| unliftKernel eLvl
  return (homExpr, op_data, eLvl)

/-- The `kernel_unlift` tactic is the inverse of `kernel_lift`. It transforms equalities of lifted
kernels back into equalities of the original kernels.

The tactic supports location specifiers like `rw` or `simp`:
* `kernel_unlift` — applies to the goal
* `kernel_unlift at h` — applies to hypothesis `h`
* `kernel_unlift at h₁ h₂` — applies to multiple hypotheses
* `kernel_unlift at h ⊢` — applies to hypothesis `h` and the goal
* `kernel_unlift at *` — applies to all hypotheses and the goal
-/
def ApplyKernelUnlift (goal : MVarId) (fvarId : Option FVarId) : TacticM MVarId := do
  goal.withContext do
    let expr ← match fvarId with
        | some fid => do
          let decl ← fid.getDecl
          pure decl.type
        | none => goal.getType
    let expr ← whnfR <| ← instantiateMVars expr
    let (homExpr, op_data, eLvl) ← UnliftEquality expr
    let eqProofType ← mkEq expr homExpr
    let eqProof ← mkKernelUnliftEqProof eqProofType eLvl op_data
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

@[inherit_doc ApplyKernelUnlift]
syntax (name := kernelUnlift) "kernel_unlift" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_unlift $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| ApplyKernelUnlift
