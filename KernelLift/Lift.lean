/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import KernelLift.ForMathlib.Kernel
public import KernelLift.ForMathlib.MeasurableEquiv

/-!
# Kernel Lift

This file defines the `lift` operation on kernels, which allows to cast kernels to different types
in the same universe level, as long as there are measurable equivalences between the types.

## Main declarations
* `Kernel.lift`: the main definition of the lift operation.
* `Kernel.isSFinite_lift`: a kernel is s-finite if and only if its lift is s-finite.
* `Kernel.lift_congr`: two kernels are equal if and only if their lifts are equal.
* `Kernel.lift_comp`: the lift of a composition is the composition of the lifts.
* `Kernel.parallelComp_lift`: the lift of a parallel composition is the parallel composition of the
lifts.
* `Kernel.prod_lift`: the lift of a product is the product of the lifts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableEquiv

namespace ProbabilityTheory.Kernel

variable {X : Type x} [MeasurableSpace X] {Y : Type y} [MeasurableSpace Y]
  {X' : Type w} [MeasurableSpace X'] {Y' : Type w} [MeasurableSpace Y']
  {ex : X' ≃ᵐ X} {ey : Y' ≃ᵐ Y}

/-- Cast a kernel to different types in the same universe level, using measurable equivalences. -/
noncomputable def lift (κ : Kernel X Y) : Kernel X' Y' := (κ.map ey.symm).comap ex ex.measurable

lemma isSFinite_lift (κ : Kernel X Y) :
    IsSFiniteKernel κ ↔ IsSFiniteKernel (lift (ex := ex) (ey := ey) κ) := by
  constructor
  · intro h
    simp only [lift]
    infer_instance
  · rintro ⟨κs, hfinite_κs, h⟩
    simp only [lift] at h
    constructor
    let κs' (i : ℕ) := ((κs i).map ey).comap ex.symm ex.symm.measurable
    refine ⟨κs', ⟨fun i ↦ ?_, ?_⟩⟩
    · exact IsFiniteKernel.comap ((κs i).map ey) ex.symm.measurable
    · simp only [κs']
      ext a s hs
      replace h := DFunLike.congr (x := ey.symm '' s) (DFunLike.congr (x := ex.symm a) h rfl) rfl
      rw [sum_apply, Measure.sum_apply] at h ⊢
      · rw [comap_apply', map_apply'] at h
        · simp only [apply_symm_apply, preimage_image] at h
          convert h with x
          rw [comap_apply', map_apply']
          · congr 1
            exact (image_symm ey s).symm
          all_goals try fun_prop
          all_goals measurability
        all_goals try fun_prop
        all_goals measurability
      all_goals measurability

lemma lift_congr {κ : Kernel X Y} {η : Kernel X Y} :
    lift (ex := ex) (ey := ey) κ = lift (ex := ex) (ey := ey) η ↔ κ = η := by
  constructor
  · intro h
    ext a s hs
    replace h := DFunLike.congr (x := ex.symm a) h rfl
    simp only [lift, coe_comap, Function.comp_apply, apply_symm_apply] at h
    rw [map_apply, map_apply] at h
    · replace h := DFunLike.congr (x := ey.symm '' s) h rfl
      rw [Measure.map_apply, Measure.map_apply] at h
      · simpa using h
      all_goals try fun_prop
      all_goals measurability
    all_goals fun_prop
  · grind

variable {T : Type t} [MeasurableSpace T] {Z : Type z} [MeasurableSpace Z]
  {T' : Type w} [MeasurableSpace T'] {Z' : Type w} [MeasurableSpace Z']
  {et : T' ≃ᵐ T} {ez : Z' ≃ᵐ Z}

lemma lift_comp (η : Kernel X Y) (κ : Kernel Z X) :
  (lift (ex := ex) (ey := ey) η).comp (lift (ex := ez) (ey := ex) κ) =
    lift (ex := ez) (ey := ey) (η.comp κ) := by
  simp only [lift]
  ext
  rw [map_comp, ← comp_map, comap_apply, comp_apply', comp_apply', map_apply, comap_apply,
    map_apply]
  · simp
  all_goals try fun_prop
  all_goals measurability

lemma parallelComp_lift (κ : Kernel X Y) (η : Kernel T Z) :
  (lift (ex := ex) (ey := ey) κ) ∥ₖ (lift (ex := et) (ey := ez) η) =
    lift (ex := ex.prod et) (ey := ey.prod ez) (κ ∥ₖ η) := by
  by_cases hκ : IsSFiniteKernel <| lift (ex := ex) (ey := ey) κ
  swap
  · simp [hκ, (isSFinite_lift κ).not.mpr hκ]
    simp [lift]
  by_cases hη : IsSFiniteKernel <| lift (ex := et) (ey := ez) η
  swap
  · simp [hη, (isSFinite_lift η).not.mpr hη]
    simp [lift]
  simp only [lift]
  replace hκ := (isSFinite_lift κ).mpr hκ
  replace hη := (isSFinite_lift η).mpr hη
  rw [comap_parallelComp_comap, map_parallelComp_map]
  · rfl
  all_goals fun_prop

lemma prod_lift (κ : Kernel X Y) (η : Kernel X Z) :
  (lift (ex := ex) (ey := ey) κ) ×ₖ (lift (ex := ex) (ey := ez) η) =
    lift (ex := ex) (ey := ey.prod ez) (κ ×ₖ η) := by
  by_cases hκ : IsSFiniteKernel <| lift (ex := ex) (ey := ey) κ
  swap
  · simp [hκ, (isSFinite_lift κ).not.mpr hκ]
    simp [lift]
  by_cases hη : IsSFiniteKernel <| lift (ex := ex) (ey := ez) η
  swap
  · simp [hη, (isSFinite_lift η).not.mpr hη]
    simp [lift]
  simp only [prod]
  rw [← lift_comp (ex := ex.prod ex), ← parallelComp_lift]
  congr
  ext
  simp only [lift, coe_comap, Function.comp_apply]
  rw [copy_apply, Measure.dirac_apply', map_apply', copy_apply, Measure.dirac_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [MeasurableEquiv.prod]
  all_goals try fun_prop
  all_goals try measurability

lemma copy_lift : copy X' = lift (ex := ex) (ey := ex.prod ex) (copy X) := by
  sorry

instance {κ : Kernel X Y} [IsDeterministic κ] :
    IsDeterministic (lift (ex := ex) (ey := ey) κ) where
  parallelComp_self_comp_copy' := by
    have h := κ.parallelComp_self_comp_copy
    ext a s hs
    replace h := DFunLike.congr (x := ey.prod ey '' s) (DFunLike.congr (x := ex a) h rfl) rfl
    simp only [lift]
    rw [comp_apply', comp_apply', copy_apply, lintegral_dirac'] at h ⊢
    · convert h
      · rw [parallelComp_apply', parallelComp_apply', lintegral_comap, lintegral_map]
        · simp only [coe_comap, Function.comp_apply]
          congr with y
          rw [map_apply']
          · congr 1
            simp [MeasurableEquiv.prod]
            aesop
          all_goals try fun_prop
          all_goals measurability
        all_goals try fun_prop
        all_goals try measurability
        exact measurable_measure_prodMk_left hs
      · rw [lintegral_comap, lintegral_map]
        · congr with y
          simp only [copy_apply]
          rw [Measure.dirac_apply' _ hs, Measure.dirac_apply']
          · refine Set.indicator_eq_indicator ?_ rfl
            simp [MeasurableEquiv.prod]
            aesop
          · measurability
        · exact ey.symm.measurable
        · exact Kernel.measurable_coe _ hs
    · exact Kernel.measurable_coe _ hs
    · exact Kernel.measurable_coe _ (by measurability)
    all_goals measurability


end ProbabilityTheory.Kernel
