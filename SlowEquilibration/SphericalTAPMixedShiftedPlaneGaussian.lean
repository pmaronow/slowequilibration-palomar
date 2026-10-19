-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedNearbyGaussianCenter
public import SlowEquilibration.StrongFieldLaplace
public import SlowEquilibration.RadialGaussianBounds

@[expose] public section

/-! The exact two-dimensional Gaussian normalizer in the literal radial
mark and physical latitude coordinates, centered at arbitrary marks. -/

namespace SlowEquilibration.SphericalTAPMixedShiftedPlaneGaussian
noncomputable section
open MeasureTheory StrongFieldComplexity RadialGaussianBounds
set_option autoImplicit false

def shiftedGaussianPlane (c K q : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-c*((z.1-K)^2+(z.2-q)^2))

theorem shiftedGaussianPlane_eq_prod (c K q : ℝ) (z : ℝ × ℝ) :
    shiftedGaussianPlane c K q z = gaussian c K z.1*gaussian c q z.2 := by
  unfold shiftedGaussianPlane gaussian
  rw [←Real.exp_add]
  congr 1
  ring

theorem shiftedGaussianPlane_integrable {c : ℝ} (hc : 0 < c) (K q : ℝ) :
    Integrable (shiftedGaussianPlane c K q) planeVolume := by
  have hh := (gaussian_integrable hc K).smul_prod (gaussian_integrable hc q)
  simpa only [smul_eq_mul,←shiftedGaussianPlane_eq_prod,planeVolume] using hh

/-- The joint Gaussian width is exactly `π/c`, hence order `N⁻¹` when
`c` is proportional to the dimension. -/
theorem integral_shiftedGaussianPlane {c : ℝ} (hc : 0 < c) (K q : ℝ) :
    (∫ z, shiftedGaussianPlane c K q z ∂planeVolume) = Real.pi/c := by
  simp only [shiftedGaussianPlane_eq_prod,planeVolume]
  calc
    _ = (∫ k : ℝ,gaussian c K k)*(∫ a : ℝ,gaussian c q a) :=
      integral_prod_mul (μ := (volume : Measure ℝ)) (ν := volume)
        (gaussian c K) (gaussian c q)
    _ = Real.pi/c := by
      rw [gaussian_integral,gaussian_integral,←pow_two,
        Real.sq_sqrt (by positivity)]

end
end SlowEquilibration.SphericalTAPMixedShiftedPlaneGaussian
