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

lemma lift_apply (κ : Kernel X Y) (a : X') :
    lift (ex := ex) (ey := ey) κ a = (κ.map ey.symm) (ex a) := rfl

lemma lift_apply' (κ : Kernel X Y) (a : X') {s : Set Y'} (hs : MeasurableSet s) :
    lift (ex := ex) (ey := ey) κ a s = (κ (ex a)) (⇑ey '' s) := by
  simp only [lift, coe_comap, Function.comp_apply]
  rw [map_apply' _ ey.symm.measurable _ hs, preimage_symm]

lemma isSFinite_lift (κ : Kernel X Y) :
    IsSFiniteKernel κ ↔ IsSFiniteKernel (lift (ex := ex) (ey := ey) κ) := by
  constructor
  · intro h
    simp only [lift]
    infer_instance
  · rintro ⟨κs, hfinite_κs, h⟩
    constructor
    let κs' (i : ℕ) := ((κs i).map ey).comap ex.symm ex.symm.measurable
    refine ⟨κs', ⟨fun i ↦ ?_, ?_⟩⟩
    · exact IsFiniteKernel.comap ((κs i).map ey) ex.symm.measurable
    · simp only [κs']
      ext a s hs
      replace h := DFunLike.congr (x := ey.symm '' s) (DFunLike.congr (x := ex.symm a) h rfl) rfl
      rw [sum_apply, Measure.sum_apply] at h ⊢
      · rw [lift_apply'] at h
        · convert h with x
          · simp
          · rw [image_symm]
            simp
          · simp only [coe_comap, Function.comp_apply]
            rw [map_apply' _ ey.measurable _ hs, image_symm]
        all_goals measurability
      all_goals measurability

instance (κ : Kernel X Y) [IsSFiniteKernel κ] : IsSFiniteKernel (lift (ex := ex) (ey := ey) κ) :=
  (isSFinite_lift κ).mp ‹_›

instance (κ : Kernel X Y) [IsMarkovKernel κ] : IsMarkovKernel (lift (ex := ex) (ey := ey) κ) := by
  simp only [lift]
  have := IsMarkovKernel.map κ ey.symm.measurable
  exact IsMarkovKernel.comap _ ex.measurable

lemma lift_congr {κ : Kernel X Y} {η : Kernel X Y} :
    lift (ex := ex) (ey := ey) κ = lift (ex := ex) (ey := ey) η ↔ κ = η := by
  constructor
  · intro h
    ext a s hs
    replace h := DFunLike.congr (x := ey.symm '' s) (DFunLike.congr (x := ex.symm a) h rfl) rfl
    rw [lift_apply', lift_apply'] at h
    · simp only [apply_symm_apply] at h
      rwa [image_symm, image_preimage] at h
    · measurability
    · measurability
  · grind

variable {T : Type t} [MeasurableSpace T] {Z : Type z} [MeasurableSpace Z]
  {T' : Type w} [MeasurableSpace T'] {Z' : Type w} [MeasurableSpace Z']
  {et : T' ≃ᵐ T} {ez : Z' ≃ᵐ Z}

lemma comp_lift (η : Kernel X Y) (κ : Kernel Z X) :
  (lift (ex := ex) (ey := ey) η).comp (lift (ex := ez) (ey := ex) κ) =
    lift (ex := ez) (ey := ey) (η.comp κ) := by
  ext _ _ hs
  rw [lift_apply', comp_apply', comp_apply', lift_apply, lintegral_map]
  · congr with y
    rw [lift_apply']
    · simp
    · exact hs
  all_goals try fun_prop
  all_goals try measurability
  · exact Kernel.measurable_coe _ hs

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

lemma id_lift : Kernel.id (α := X') = lift (ex := ex) (ey := ex) (Kernel.id (α := X)) := by
  ext _ _ hs
  rw [lift_apply' _ _ hs]
  simp only [id_apply]
  rw [Measure.dirac_apply' _ hs, Measure.dirac_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp_all only [Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  all_goals measurability

lemma discard_lift : discard.{_, w} X' = lift (ex := ex) (ey := punit) (discard X) := by
  ext _ _ hs
  rw [lift_apply' _ _ hs]
  simp only [discard_apply, MeasurableSpace.measurableSet_top, Measure.dirac_apply']
  refine Set.indicator_eq_indicator ?_ rfl
  grind

lemma copy_lift : copy X' = lift (ex := ex) (ey := ex.prod ex) (copy X) := by
  ext _ _ hs
  rw [lift_apply' _ _ hs]
  simp only [copy_apply]
  rw [Measure.dirac_apply' _ hs, Measure.dirac_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp [MeasurableEquiv.prod]
  · measurability

lemma swap_lift : swap X' Y' = lift (ex := ex.prod ey) (ey := ey.prod ex) (swap X Y) := by
  ext a s hs
  rw [lift_apply' _ _ hs]
  simp only [swap_apply]
  rw [Measure.dirac_apply' _ hs, Measure.dirac_apply']
  · refine Set.indicator_eq_indicator ?_ rfl
    simp only [MeasurableEquiv.prod, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Prod.swap_prod_mk,
      Set.mem_image, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Prod.exists,
      exists_eq_right_right, exists_eq_right]
    grind
  · measurability

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
  rw [← comp_lift (ex := ex.prod ex), ← parallelComp_lift, ← copy_lift]

instance {κ : Kernel X Y} [IsDeterministic κ] :
    IsDeterministic (lift (ex := ex) (ey := ey) κ) where
  parallelComp_self_comp_copy' := by
    rw [parallelComp_lift, copy_lift (ex := ex), copy_lift (ex := ey), comp_lift, comp_lift,
      lift_congr]
    exact κ.parallelComp_self_comp_copy

end ProbabilityTheory.Kernel
