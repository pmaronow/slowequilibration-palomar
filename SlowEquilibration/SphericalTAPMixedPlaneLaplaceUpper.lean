-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedShiftedPlaneGaussian

@[expose] public section

/-! A literal two-dimensional Lebesgue Laplace bound for the physical
radial-mark/latitude plane. The Gaussian normalizer is exact. -/

namespace SlowEquilibration.SphericalTAPMixedPlaneLaplaceUpper
noncomputable section
open Set MeasureTheory StrongFieldComplexity
open SphericalTAPMixedShiftedPlaneGaussian
set_option autoImplicit false

theorem plane_weighted_laplace_upper {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) {f : ℝ × ℝ → ℝ}
    (hfm : AEStronglyMeasurable f (planeVolume.restrict S))
    {N c W H K q : ℝ} (hN : 0 < N) (hc : 0 < c) (hW : 0 ≤ W)
    (hpos : ∀ z ∈ S, 0 ≤ f z)
    (henv : ∀ z ∈ S,
      f z ≤ W*Real.exp (N*H)*shiftedGaussianPlane (c*N) K q z) :
    (∫ z in S, f z ∂planeVolume) ≤ (W*Real.pi/c)*Real.exp (N*H)/N := by
  have hcN : 0 < c*N := mul_pos hc hN
  have hdom : Integrable
      (fun z => W*Real.exp (N*H)*shiftedGaussianPlane (c*N) K q z) planeVolume :=
    (shiftedGaussianPlane_integrable hcN K q).const_mul _
  have hfi : IntegrableOn f S planeVolume := by
    apply hdom.restrict.mono' hfm
    filter_upwards [ae_restrict_mem hS] with z hz
    rw [Real.norm_of_nonneg (hpos z hz)]
    exact henv z hz
  calc
    (∫ z in S, f z ∂planeVolume) ≤
        ∫ z in S, W*Real.exp (N*H)*shiftedGaussianPlane (c*N) K q z ∂planeVolume :=
      setIntegral_mono_on hfi hdom.restrict hS henv
    _ ≤ ∫ z, W*Real.exp (N*H)*shiftedGaussianPlane (c*N) K q z ∂planeVolume :=
      setIntegral_le_integral hdom (ae_of_all _ (fun z =>
        mul_nonneg (mul_nonneg hW (Real.exp_pos _).le)
          (Real.exp_pos _).le))
    _ = (W*Real.pi/c)*Real.exp (N*H)/N := by
      rw [integral_const_mul, integral_shiftedGaussianPlane hcN]
      field_simp

end
end SlowEquilibration.SphericalTAPMixedPlaneLaplaceUpper
