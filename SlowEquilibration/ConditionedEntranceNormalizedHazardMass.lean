-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceTiltCommutator

/-! A quantitative killing-mass bound under a globally normalized tilt.
The killing rate is averaged over frozen axes before the spin, so a small
axis cap survives the change of reference measure. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 350000

/-- If `e^w ≤ W` and the axis-averaged killing rate is at most `K`, its
weighted mass under a global tilt with normalizer `M ≥ 1/2` is at most
`2 W K ∫ F`. The weight `F` is frozen in the axis label. -/
theorem normalizedTilt_killing_mass_le
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (θ : Measure U) (μ : Measure E)
    [IsProbabilityMeasure θ] [IsProbabilityMeasure μ]
    (w : U × E → ℝ) (hw : Measurable w)
    (κ : U × E → ℝ) (F : E → ℝ)
    (hF : Integrable F μ) (hFpos : ∀ x, 0 ≤ F x)
    (hκpos : ∀ z, 0 ≤ κ z)
    (hκF : Integrable (fun z => κ z * F z.2) (θ.prod μ))
    (hewκF : Integrable (fun z => Real.exp (w z) * (κ z * F z.2)) (θ.prod μ))
    {K W M : ℝ} (hK : 0 ≤ K) (hW : 0 ≤ W) (hM : 1/2 ≤ M)
    (hweight : ∀ᵐ z ∂θ.prod μ, Real.exp (w z) ≤ W)
    (haxis : ∀ᵐ x ∂μ, (∫ u, κ (u,x) ∂θ) ≤ K) :
    (∫ z, κ z * F z.2 ∂normalizedTilt (θ.prod μ) w M) ≤
      2 * W * K * (∫ x, F x ∂μ) := by
  have hMpos : 0 < M := by linarith
  have hweighted : (∫ z, κ z * F z.2 ∂θ.prod μ) ≤
      K * (∫ x, F x ∂μ) :=
    weighted_frozen_axis_integral_bound θ μ κ F hF
      (.of_forall hFpos) hκF haxis
  have hpoint : ∀ᵐ z ∂θ.prod μ, Real.exp (w z) * (κ z * F z.2) ≤
      W * (κ z * F z.2) := by
    filter_upwards [hweight] with z hz
    exact mul_le_mul_of_nonneg_right hz
      (mul_nonneg (hκpos z) (hFpos z.2))
  have hmono : (∫ z, Real.exp (w z) * (κ z * F z.2) ∂θ.prod μ) ≤
      W * (∫ z, κ z * F z.2 ∂θ.prod μ) := by
    simpa only [integral_const_mul] using
      integral_mono_ae hewκF (hκF.const_mul W) hpoint
  have hnum : (∫ z, Real.exp (w z) * (κ z * F z.2) ∂θ.prod μ) ≤
      W * K * (∫ x, F x ∂μ) := by
    calc
      _ ≤ W * (∫ z, κ z * F z.2 ∂θ.prod μ) := hmono
      _ ≤ W * (K * (∫ x, F x ∂μ)) := mul_le_mul_of_nonneg_left hweighted hW
      _ = _ := by ring
  have hFmass : 0 ≤ (∫ x, F x ∂μ) := integral_nonneg hFpos
  rw [integral_normalizedTilt (θ.prod μ) w hw hMpos]
  apply (div_le_iff₀ hMpos).2
  have hA : 0 ≤ W * K * (∫ x, F x ∂μ) := by positivity
  have hm := mul_le_mul_of_nonneg_left hM (show 0 ≤ 2 * (W * K * (∫ x, F x ∂μ)) by positivity)
  nlinarith

end SlowEquilibration.ConditionedEntrance
