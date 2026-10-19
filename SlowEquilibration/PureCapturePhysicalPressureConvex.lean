-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairPressureDerivative
public import SlowEquilibration.GaussianSpinLogConvex

/-! Convexity of the genuine finite-volume spherical quenched pressure
as a function of inverse temperature. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPressureConvex

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem quenchedPressure_convexOn (μ : FiniteMixture) {N : ℕ}
    (hN : 1 ≤ N) : ConvexOn ℝ univ (quenchedPressure N μ) := by
  let c := mixtureCoefficients μ
  let L := sphereLinear (N := N) c
  let ν := sphereLaw N
  letI : IsProbabilityMeasure ν := sphereLaw_probability N
  have hL : Measurable L := sphereLinear_measurable c
  have hb := sphereLinear_bound hN c (mixtureCoefficients_nonnegative μ)
  have hpoint (g : EuclideanDisorder N μ.maxDegree) :
      ConvexOn ℝ univ (fun t : ℝ =>
        GaussianSpinInterpolation.logPartition ν L (t • g)) := by
    simpa only [zero_add] using
      GaussianSpinInterpolation.logPartition_line_convex ν L hL
        (Real.sqrt_nonneg _) hb 0 g
  have hint (t : ℝ) : Integrable (fun g : EuclideanDisorder N μ.maxDegree =>
      GaussianSpinInterpolation.logPartition ν L (t • g))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) :=
    GaussianSpinInterpolation.logPartition_radial_gaussian_integrable
      ν L hL (Real.sqrt_nonneg _) hb t
  have hconv : ConvexOn ℝ univ (fun t : ℝ =>
      ∫ g : EuclideanDisorder N μ.maxDegree,
        GaussianSpinInterpolation.logPartition ν L (t • g)
          ∂SYK.standardGaussianMeasureOnEuclidean
            (Coordinate N μ.maxDegree)) :=
    integral_convexOn_of_integrand_ae convex_univ (.of_forall hpoint)
      (fun t _ => hint t)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hdiv := hconv.smul (inv_nonneg.mpr hNpos.le)
  have heq : (fun t => (N : ℝ)⁻¹ •
      (∫ g : EuclideanDisorder N μ.maxDegree,
        GaussianSpinInterpolation.logPartition ν L (t • g)
          ∂SYK.standardGaussianMeasureOnEuclidean
            (Coordinate N μ.maxDegree))) = quenchedPressure N μ := by
    funext t
    rw [smul_eq_mul, inv_mul_eq_div]
    exact gaussianMeanLogPartition_eq_quenchedPressure hN μ t
  rwa [heq] at hdiv

end SlowEquilibration.PureCapturePhysicalPressureConvex
