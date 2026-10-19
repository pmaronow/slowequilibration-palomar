-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceWeightedDefectCauchy

/-! The signed zero-order commutator belongs to L¹ once its square
moment and the physical weighted resolvent square are L¹. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem weighted_zero_defect_commutator_integrable
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (k F U : E → ℝ)
    (hk : Measurable k) (hF : Measurable F) (hU : Measurable U)
    (hFlo : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, 0 ≤ U z ∧ U z ≤ 1)
    (hK : Integrable (fun z => k z^2*(F z-1)) ν)
    (hA : Integrable (fun z => F z*U z^2) ν) :
    Integrable (fun z => k z*(F z-1)*U z^2) ν := by
  let C : E → ℝ := fun z => k z*(F z-1)*U z^2
  let X : E → ℝ := fun z => k z*Real.sqrt (F z-1)
  let Y : E → ℝ := fun z => Real.sqrt (F z-1)*U z^2
  have hCm : Measurable C := by
    dsimp only [C]
    fun_prop
  have hpoint : ∀ᵐ z ∂ν, ‖C z‖ ≤
      (k z^2*(F z-1)+F z*U z^2)/2 := by
    filter_upwards [hFlo,hUb] with z hz hu
    have hXsq : X z^2 = k z^2*(F z-1) := by
      dsimp only [X]
      rw [mul_pow,Real.sq_sqrt (by linarith)]
    have hYsq : Y z^2 ≤ F z*U z^2 := by
      dsimp only [Y]
      rw [mul_pow,Real.sq_sqrt (by linarith)]
      have hU2 : 0 ≤ U z^2 := sq_nonneg _
      have hU2le : U z^2 ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hu.2)
          (show 0 ≤ 1+U z by linarith)]
      have hU4 : (U z^2)^2 ≤ U z^2 := by
        nlinarith [mul_nonneg hU2 (sub_nonneg.mpr hU2le)]
      have hs := mul_le_mul_of_nonneg_left hU4 (show 0 ≤ F z-1 by linarith)
      nlinarith
    have hcross : C z = X z*Y z := by
      calc
        C z = k z*(Real.sqrt (F z-1))^2*U z^2 := by
          rw [Real.sq_sqrt (by linarith : 0 ≤ F z-1)]
        _ = X z*Y z := by dsimp only [X,Y]; ring
    have hxy : |X z*Y z| ≤ (X z^2+Y z^2)/2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|X z|-|Y z|),sq_abs (X z),sq_abs (Y z)]
    rw [Real.norm_eq_abs,hcross]
    rw [hXsq] at hxy
    linarith
  have hD : Integrable (fun z =>
      (k z^2*(F z-1)+F z*U z^2)/2) ν :=
    (hK.add hA).div_const 2
  exact hD.mono' hCm.aestronglyMeasurable hpoint

end SlowEquilibration.ConditionedEntrance
