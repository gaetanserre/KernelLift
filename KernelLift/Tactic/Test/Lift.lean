/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

import Lean.Elab.Tactic.Location
public import KernelLift.Lift
public import KernelLift.Tactic.LocTactic
public import KernelLift.Tactic.Universe
public import KernelLift.Tactic.Utils
import KernelLift.Tactic.Utils

/-!
-/

public meta section

open Lean Elab Tactic Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

private initialize liftImplRef :
    IO.Ref (Array (Expr → Level → List Expr → MetaM (Expr × List Expr))) ← IO.mkRef #[]

def registerLiftExpr (f : Expr → Level → List Expr → MetaM (Expr × List Expr)) : IO Unit := do
  liftImplRef.modify (·.push f)

private initialize liftFinisherRef :
    IO.Ref (Array (Expr → Expr → Level → MetaM Expr)) ← IO.mkRef #[]

def registerLiftFinisher (f : Expr → Expr → Level → MetaM Expr) : IO Unit := do
  liftFinisherRef.modify (·.push f)

def liftExpr (e : Expr) (maxLvl : Level) (proofs : List Expr) : MetaM (Expr × List Expr) := do
  let handlers ← liftImplRef.get
  let (lift_expr, proofs) ← handlers[0]! e maxLvl proofs
  let (lift_expr, proofs) ← handlers.firstM (fun h => h e maxLvl proofs)
  return (lift_expr, proofs)

def constructProof (eqProofType lhs rhs : Expr) (maxLvl : Level) (proofs : List Expr) :
    MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProofType
  let mvarId := mvar.mvarId!
  let propext := mkConst ``propext
  match ← mvarId.apply propext with
  | [mvarId] =>
    let proofs := proofs.reverse
    let mut mvarId := mvarId
    for proof in proofs do
      mvarId ← mvarId.nth_rewrite 1 proof
    let handlers ← liftFinisherRef.get
    let e ← handlers.firstM (fun h => do
      let finisher ← h lhs rhs maxLvl
      unless ← isDefEq (← mvarId.getType) (← inferType finisher) do
        throwError "Type mismatch: expected {← mvarId.getType}, got {← inferType finisher}"
      mvarId.assign finisher
      logInfo m!"{← mvarId.getType}"
      instantiateMVars mvar
    ) <|> do
      throwError "Error finisher"
    return e
  | _ =>
    throwError "Failed to apply propext while building kernel_lift equivalence proof for
      {eqProofType}"

def liftEquality (eq : Expr) : MetaM (Expr × Expr) := do
  logInfo m!"Lifting equality: {eq}"
  let e ← whnfR (← zetaReduce (← instantiateMVars eq))
  let e := e.consumeMData
  let univs ← collectExprUniverses eq
  let maxLvl ← computeMaxLevel univs
  let some (_, lhs, rhs) := e.eq? | throwError "Expected an equality, got: {e}"
  let (lhs_lifted, proofs) ← liftExpr lhs maxLvl []
  let (rhs_lifted, proofs) ← liftExpr rhs maxLvl proofs
  let eq_lifted ← mkEq lhs_lifted rhs_lifted
  logInfo m!"Lifted equality: {eq_lifted}"
  logInfo m!"Proofs: {proofs}"
  let eq_proof_type ← mkEq eq eq_lifted
  let proof ← constructProof eq_proof_type lhs rhs maxLvl proofs
  return (eq_lifted, proof)

syntax (name := Eqlift) "lift_eq" (ppSpace location)? : tactic

elab_rules : tactic
  | `(tactic| lift_eq $[$loc]?) =>
    expandOptLocation (mkOptionalNode loc) |> applyLocTactic <| liftEquality
