-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceGradientCauchy

/-! The zero-order commutator error in the source entropy–resolvent
comparison is controlled by the actual weighted square energy. The
inequality is proved on the underlying measure, so it applies directly
to the globally normalized source tilt. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem weighted_defect_square_commutator_cauchy
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (k F U : E → ℝ)
    (hk : AEStronglyMeasurable k ν)
    (hF : AEStronglyMeasurable F ν)
    (hU : AEStronglyMeasurable U ν)
    (hFlo : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, 0 ≤ U z ∧ U z ≤ 1)
    (hK : Integrable (fun z => k z ^ 2 * (F z - 1)) ν)
    (hA : Integrable (fun z => F z * U z ^ 2) ν) :
    |∫ z, k z * (F z - 1) * U z ^ 2 ∂ν| ≤
      Real.sqrt ((∫ z, k z ^ 2 * (F z - 1) ∂ν) *
        (∫ z, F z * U z ^ 2 ∂ν)) := by
  let X : E → ℝ := fun z => k z * Real.sqrt (F z - 1)
  let Y : E → ℝ := fun z => Real.sqrt (F z - 1) * U z ^ 2
  have hXm : AEStronglyMeasurable X ν := by
    exact hk.mul (Real.continuous_sqrt.comp_aestronglyMeasurable (hF.sub aestronglyMeasurable_const))
  have hYm : AEStronglyMeasurable Y ν := by
    exact (Real.continuous_sqrt.comp_aestronglyMeasurable (hF.sub aestronglyMeasurable_const)).mul (hU.pow 2)
  have hXsq : (fun z => X z ^ 2) =ᵐ[ν] (fun z => k z ^ 2 * (F z - 1)) := by
    filter_upwards [hFlo] with z hz
    dsimp only [X]
    rw [mul_pow,Real.sq_sqrt (by linarith)]
  have hYsq : ∀ᵐ z ∂ν, Y z ^ 2 ≤ F z * U z ^ 2 := by
    filter_upwards [hFlo,hUb] with z hz hu
    dsimp only [Y]
    rw [mul_pow,Real.sq_sqrt (by linarith)]
    have hU2 : 0 ≤ U z ^ 2 := sq_nonneg _
    have hU2le : U z ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ 1 + U z by linarith)]
    have hU4 : (U z ^ 2) ^ 2 ≤ U z ^ 2 := by
      nlinarith [mul_nonneg hU2 (sub_nonneg.mpr hU2le)]
    have hs := mul_le_mul_of_nonneg_left hU4 (show 0 ≤ F z - 1 by linarith)
    nlinarith
  have hY2 : Integrable (fun z => Y z ^ 2) ν := by
    apply Integrable.mono_nonneg hA (by fun_prop) (by filter_upwards [] with z; positivity)
    exact hYsq
  have hX2 : Integrable (fun z => X z ^ 2) ν := hK.congr hXsq.symm
  have hYint : (∫ z, Y z ^ 2 ∂ν) ≤ ∫ z, F z * U z ^ 2 ∂ν :=
    integral_mono_ae hY2 hA hYsq
  have hXint : (∫ z, X z ^ 2 ∂ν) = ∫ z, k z ^ 2 * (F z - 1) ∂ν :=
    integral_congr_ae hXsq
  have hcross : (fun z => X z * Y z) =ᵐ[ν]
      (fun z => k z * (F z - 1) * U z ^ 2) := by
    filter_upwards [hFlo] with z hz
    dsimp only [X,Y]
    rw [← mul_assoc, mul_assoc (k z)]
    rw [← pow_two,Real.sq_sqrt (by linarith)]
  have h := integral_inner_abs_le_sqrt ν X Y hXm hYm
    (by simpa only [Real.norm_eq_abs, sq_abs] using hX2)
    (by simpa only [Real.norm_eq_abs, sq_abs] using hY2)
  simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sq_abs] at h
  have hXnonneg : 0 ≤ ∫ z, X z ^ 2 ∂ν := integral_nonneg fun z => sq_nonneg _
  have hmul : (∫ z, X z ^ 2 ∂ν) * (∫ z, Y z ^ 2 ∂ν) ≤
      (∫ z, X z ^ 2 ∂ν) * (∫ z, F z * U z ^ 2 ∂ν) :=
    mul_le_mul_of_nonneg_left hYint hXnonneg
  have h' := h.trans (Real.sqrt_le_sqrt hmul)
  rw [hXint] at h'
  have hreal : (∫ z, X z * Y z ∂ν) = ∫ z, k z * (F z - 1) * U z ^ 2 ∂ν :=
    integral_congr_ae hcross
  -- The real inner product is ordinary multiplication.
  have hcomm : (∫ z, Y z * X z ∂ν) = ∫ z, X z * Y z ∂ν := by
    apply integral_congr_ae
    exact .of_forall (fun z => mul_comm (Y z) (X z))
  rw [hcomm,hreal] at h'
  exact h'

end SlowEquilibration.ConditionedEntrance
