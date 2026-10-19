-- SPDX-License-Identifier: Apache-2.0
module

public import SphericalAging.SphereSurfaceIdentification
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-! Genuine radial/angular independence of the actual finite-dimensional
Gaussian generating the normalized spherical reference measure. This is
the product structure needed for a spherical, rather than Ising, cavity
disintegration. It follows from the actual Euclidean polar coarea formula. -/

namespace SlowEquilibration.SphericalParisiRadialIndependence

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open SphericalAging.SphereSurfaceIdentification
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def angularIntegral (N : ℕ) (f : Vector N → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ θ : sphere (0 : Vector N) 1, f (Real.sqrt N • θ.1) ∂unitSurface N

private def radialIntegral (N : ℕ) (g : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (radialDensity N r)*g r.1 ∂radialMeasure N

private theorem actual_polar_product {N : ℕ} (hN : 1 ≤ N)
    (f : Vector N → ℝ≥0∞) (g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Vector N, f (normalize N x)*g ‖x‖ ∂gaussianLaw N) =
      angularIntegral N f*radialIntegral N g := by
  have hpol : (∫⁻ x : Vector N, f (normalize N x)*g ‖x‖ ∂gaussianLaw N) =
      ∫⁻ θ : sphere (0 : Vector N) 1, ∫⁻ r : Ioi (0 : ℝ),
        ENNReal.ofReal (radialDensity N r)*(f (normalize N (r.1 • θ.1))*g ‖r.1 • θ.1‖)
          ∂radialMeasure N ∂unitSurface N :=
    gaussian_polar_lintegral hN (fun x => f (normalize N x)*g ‖x‖)
      ((hf.comp (normalize_measurable N)).mul (hg.comp measurable_norm))
  rw [hpol]
  have hnorm (θ : sphere (0 : Vector N) 1) (r : Ioi (0 : ℝ)) : ‖r.1 • θ.1‖=r.1 := by
    have hθ : ‖θ.1‖=1 := by simpa only [mem_sphere_zero_iff_norm] using θ.2
    rw [norm_smul, Real.norm_of_nonneg r.2.le, hθ, mul_one]
  simp_rw [normalize_polar, hnorm]
  have hslice (θ : sphere (0 : Vector N) 1) :
      (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (radialDensity N r)*
          (f (Real.sqrt N • θ.1)*g r.1) ∂radialMeasure N) =
        f (Real.sqrt N • θ.1)*radialIntegral N g := by
    simp_rw [mul_left_comm (ENNReal.ofReal (radialDensity N _))]
    exact lintegral_const_mul _ (by fun_prop)
  simp_rw [hslice]
  exact lintegral_mul_const _ (by fun_prop)

/-- The real radial and angular Gaussian functionals factor, with both
actual marginal measures rather than a supplied radial distribution. -/
theorem gaussian_radial_angular_factorization {N : ℕ} (hN : 1 ≤ N)
    (f : Vector N → ℝ≥0∞) (g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Vector N, f (normalize N x)*g ‖x‖ ∂gaussianLaw N) =
      (∫⁻ x : Vector N, f (normalize N x) ∂gaussianLaw N)*
        (∫⁻ x : Vector N, g ‖x‖ ∂gaussianLaw N) := by
  have hfg := actual_polar_product hN f g hf hg
  have hf1 := actual_polar_product hN f (fun _ => 1) hf measurable_const
  have h1g := actual_polar_product hN (fun _ => 1) g measurable_const hg
  have h11 := actual_polar_product hN (fun _ => 1) (fun _ => 1)
    measurable_const measurable_const
  simp only [mul_one, one_mul, lintegral_one, measure_univ] at hf1 h1g h11
  rw [hfg, hf1, h1g]
  have hmass : angularIntegral N (fun _ => 1)*radialIntegral N (fun _ => 1)=1 := h11.symm
  calc
    _ = angularIntegral N f*(angularIntegral N (fun _ => 1)*radialIntegral N (fun _ => 1))*
        radialIntegral N g := by rw [hmass, mul_one]
    _ = _ := by ac_rfl

/-- The actual normalized spherical point and its generating Gaussian
radius are independent. No angular law or radial law is postulated. -/
theorem normalize_independent_radius {N : ℕ} (hN : 1 ≤ N) :
    IndepFun (normalize N) (fun x : Vector N => ‖x‖) (gaussianLaw N) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hh := gaussian_radial_angular_factorization hN (s.indicator (fun _ => 1))
    (t.indicator (fun _ => 1)) (measurable_const.indicator hs) (measurable_const.indicator ht)
  have he : (fun x : Vector N => s.indicator (fun _ => (1 : ℝ≥0∞)) (normalize N x)*
      t.indicator (fun _ => (1 : ℝ≥0∞)) ‖x‖) =
      (normalize N ⁻¹' s ∩ (fun x : Vector N => ‖x‖) ⁻¹' t).indicator (fun _ => 1) := by
    funext x
    by_cases hx : normalize N x ∈ s <;> by_cases hr : ‖x‖ ∈ t <;> simp [hx, hr]
  rw [he] at hh
  change (∫⁻ x : Vector N, _ ∂gaussianLaw N) =
    (∫⁻ x : Vector N, (normalize N ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) x ∂gaussianLaw N)*
      (∫⁻ x : Vector N, ((fun x : Vector N => ‖x‖) ⁻¹' t).indicator (fun _ => (1 : ℝ≥0∞)) x
        ∂gaussianLaw N) at hh
  simpa only [lintegral_indicator ((hs.preimage (normalize_measurable N)).inter
    (ht.preimage measurable_norm)), lintegral_indicator (hs.preimage (normalize_measurable N)),
    lintegral_indicator (ht.preimage measurable_norm), lintegral_one, Measure.restrict_apply MeasurableSet.univ,
    univ_inter] using hh

end
end SlowEquilibration.SphericalParisiRadialIndependence
