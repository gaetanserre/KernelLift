/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelLift.Tactic.Test.Kernel
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Probability.Kernel.Deterministic

/-!
# Tests for `kernel_lift` and `kernel_unlift` tactics
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

variable {X Y Z T X' Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace T] [MeasurableSpace X'] [MeasurableSpace Y']
  [MeasurableSpace Z']

namespace ProbabilityTheory.Kernel

variable {κ : Kernel X Y} {ξ : Kernel Z T} {η : Kernel Y Z}

example : discard Y = 0 := by
  lift_eq
  sorry

lemma swap_parallelComp₀ : swap Y T ∘ₖ (κ ∥ₖ ξ) = ξ ∥ₖ κ ∘ₖ swap X Z := by
  lift_eq
  kernel_unlift
  exact swap_parallelComp

variable [IsSFiniteKernel η] [IsSFiniteKernel ξ]

lemma parallelComp_id_left_comp_parallelComp₀ :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  lift_eq
  kernel_unlift
  exact parallelComp_id_left_comp_parallelComp

lemma parallelComp_id_right_comp_parallelComp₀ :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  lift_eq
  kernel_unlift
  exact parallelComp_id_right_comp_parallelComp

variable [IsSFiniteKernel κ]

variable {κ' : Kernel X Y'} {η' : Kernel Y' Z'} [IsSFiniteKernel κ'] [IsSFiniteKernel η']

lemma parallelComp_comp_parallelComp₀ :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  lift_eq
  kernel_unlift
  exact parallelComp_comp_parallelComp

lemma parallelComp_comp_prod₀ :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  lift_eq
  kernel_unlift
  exact parallelComp_comp_prod

lemma discard_comp_deterministic {f : X → Y} (hf : Measurable f) :
    discard Y ∘ₖ (deterministic f hf) = discard X := by
  lift_eq
  kernel_unlift
  exact comp_discard _

variable {κ : Kernel X Y}

lemma parallelComp_self_comp_copy₀ [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ copy X = copy Y ∘ₖ κ := by
  lift_eq
  exact parallelComp_self_comp_copy

end ProbabilityTheory.Kernel
