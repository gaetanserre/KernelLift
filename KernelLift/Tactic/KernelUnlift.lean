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
    let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let ez ← constructMeasurableEquiv Z zLvl eLvl
    let et ← constructMeasurableEquiv T tLvl eLvl
    let OPParallelComp := .ParallelComp ex ey ez et
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
  | Expr.const ``Kernel.compProd _ =>
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
    let OPCompProd := .CompProd ex ey ez
    return (← mkAppM ``compProd #[κ, η], OPCompProd :: lη)
  | Expr.const ``Kernel.id _ =>
    let (X', _, _, _) ← getTypesFromKernel e
    let (X, xLvl) ← getOriginalType X'
    if X == X' then
      return (e, op_data)
    else
      let ex ← constructMeasurableEquiv X xLvl eLvl
      let mX ← synthInstance (mkApp (Expr.const ``MeasurableSpace [xLvl]) X)
      let OPId := .Id ex
      return (← mkAppOptM ``Kernel.id #[X, mX], OPId :: op_data)
  | Expr.const ``Kernel.discard _ =>
    let (X', _, _, _) ← getTypesFromKernel e
    let (X, xLvl) ← getOriginalType X'
    if X == X' then
      return (e, op_data)
    else
      let ex ← constructMeasurableEquiv X xLvl eLvl
      let OPDiscard := .Discard ex
      let discard_const := Expr.const ``Kernel.discard [xLvl, 0]
      return (← mkAppOptM' discard_const #[X, none], OPDiscard :: op_data)
  | Expr.const ``Kernel.copy _ =>
    let (X', _, _, _) ← getTypesFromKernel e
    let (X, xLvl) ← getOriginalType X'
    if X == X' then
      return (e, op_data)
    else
      let ex ← constructMeasurableEquiv X xLvl eLvl
      let OPCopy := .Copy ex
      return (← mkAppOptM ``Kernel.copy #[X, none], OPCopy :: op_data)
  | Expr.const ``Kernel.swap _ =>
    let args := e.getAppArgs
    let X' := args[0]!
    let Y' := args[1]!
    let (X, xLvl) ← getOriginalType X'
    let (Y, yLvl) ← getOriginalType Y'
    if X == X' && Y == Y' then
      return (e, op_data)
    else
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
    | .Comp ex ey ez =>
      let terms ← exprsToSyntax #[ex, ey, ez]
      evalTactic (← `(tactic| nth_rw 1 [
        comp_lift (ex := $(terms[0]!)) (ey := $(terms[1]!)) (ez := $(terms[2]!))]))
    | .ParallelComp ex ey ez et =>
      let terms ← exprsToSyntax #[ex, ey, ez, et]
      evalTactic (← `(tactic| nth_rw 1 [
        parallelComp_lift
        (ex := $(terms[0]!))
        (ey := $(terms[1]!))
        (ez := $(terms[2]!))
        (et := $(terms[3]!))
      ]))
    | .Prod ex ey ez =>
      let terms ← exprsToSyntax #[ex, ey, ez]
      evalTactic (← `(tactic| nth_rw 1 [
        prod_lift
        (ex := $(terms[0]!))
        (ey := $(terms[1]!))
        (ez := $(terms[2]!))
      ]))
    | .CompProd ex ey ez =>
      let terms ← exprsToSyntax #[ex, ey, ez]
      evalTactic (← `(tactic| nth_rw 1 [
        compProd_lift
        (ex := $(terms[0]!))
        (ey := $(terms[1]!))
        (ez := $(terms[2]!))
      ]))
    | .Id ex =>
      let exStx ← Term.exprToSyntax ex
      evalTactic (← `(tactic| nth_rw 1 [
        id_lift
        (ex := $exStx)
      ]))
    | .Discard ex =>
      let exStx ← Term.exprToSyntax ex
      evalTactic (← `(tactic| nth_rw 1 [
        discard_lift
        (ex := $exStx)
      ]))
    | .Copy ex =>
      let exStx ← Term.exprToSyntax ex
      evalTactic (← `(tactic| nth_rw 1 [
        copy_lift
        (ex := $exStx)
      ]))
    | .Swap ex ey =>
      let terms ← exprsToSyntax #[ex, ey]
      evalTactic (← `(tactic| nth_rw 1 [
        swap_lift
        (ex := $(terms[0]!))
        (ey := $(terms[1]!))
      ]))
  evalTactic (← `(tactic| rw [lift_congr.{_, _, $eLvlStx}]))
  if !(← getGoals).isEmpty then
    setGoals savedGoals
    throwError "Failed to solve all goals while building kernel_lift equivalence proof"
  setGoals savedGoals
  instantiateMVars mvar

/-- Extract the original kernel equality from a lifted kernel equality, returning the unlifted
expression and a proof of equivalence. -/
def UnliftEquality (eq : Expr) : TacticM (Expr × Expr) := do
  let eq ← whnfR <| ← instantiateMVars eq
  let eLvl ← getLevelFromEq eq
  let (unlift_expr, op_data, _, _) ← transformEquality eq KernelOP <| unliftKernel eLvl
  if unlift_expr == eq then
    throwError "The expression is not a lifted kernel equality, or it cannot be unlifted."
  else
    let eq_proof_type ← mkEq eq unlift_expr
    return (unlift_expr, ← mkKernelUnliftEqProof eq_proof_type eLvl op_data)

/-- The `kernel_unlift` tactic is the inverse of `kernel_lift`. It transforms equalities of lifted
kernels back into equalities of the original kernels.

The tactic supports location specifiers like `rw` or `simp`:
* `kernel_unlift` — applies to the goal
* `kernel_unlift at h` — applies to hypothesis `h`
* `kernel_unlift at h₁ h₂` — applies to multiple hypotheses
* `kernel_unlift at h ⊢` — applies to hypothesis `h` and the goal
* `kernel_unlift at *` — applies to all hypotheses and the goal
-/
syntax (name := kernelUnlift) "kernel_unlift" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| kernel_unlift $[$loc]?) =>
    expandOptLocation (Lean.mkOptionalNode loc) |> applyLocTactic <| UnliftEquality
