-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCompactFeatureComparison
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Actual Gaussian norm second moment and expected norm bound
-/

@[expose] public section

namespace SlowEquilibration.GaussianNormMean

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The true squared norm of an ordinary standard Gaussian has expectation
equal to the actual Euclidean dimension. -/
theorem integral_norm_sq_stdGaussian :
    (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) = (Module.finrank ℝ E : ℝ) := by
  let e := stdOrthonormalBasis ℝ E
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x : E => (inner ℝ (e i) x) ^ 2) (stdGaussian E) := by
    exact ((IsGaussian.memLp_two_id (μ := stdGaussian E)).continuousLinearMap_comp
      (innerSL ℝ (e i))).integrable_sq
  have he (i : Fin (Module.finrank ℝ E)) :
      (∫ x : E, (inner ℝ (e i) x) ^ 2 ∂stdGaussian E) = 1 := by
    change (∫ x : E, (innerSL ℝ (e i) x) ^ 2 ∂stdGaussian E) = 1
    rw [← variance_of_integral_eq_zero (innerSL ℝ (e i)).continuous.measurable.aemeasurable
      (integral_strongDual_stdGaussian (innerSL ℝ (e i))),
      variance_dual_stdGaussian, innerSL_apply_norm, e.norm_eq_one, one_pow]
  simp_rw [← e.sum_sq_inner_right]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp [he]

/-- Cauchy--Schwarz for the genuine standard Gaussian norm, obtained from
its exact second moment and nonnegative variance. -/
theorem integral_norm_stdGaussian_le_sqrt_finrank :
    (∫ x : E, ‖x‖ ∂stdGaussian E) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := by
  have hv := variance_nonneg (fun x : E => ‖x‖) (stdGaussian E)
  have hLp : MemLp (fun x : E => ‖x‖) 2 (stdGaussian E) := IsGaussian.memLp_two_id.norm
  rw [variance_eq_sub hLp] at hv
  change 0 ≤ (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) - (∫ x : E, ‖x‖ ∂stdGaussian E) ^ 2 at hv
  rw [integral_norm_sq_stdGaussian] at hv
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity)
  have hsp := Real.sqrt_nonneg (Module.finrank ℝ E : ℝ)
  nlinarith

variable (ι : Type*) [Fintype ι]

/-- Coordinate form for the actual Gaussian law used in the interpolation. -/
theorem standardGaussian_integral_norm_sq :
    (∫ x : EuclideanSpace ℝ ι, ‖x‖ ^ 2 ∂SYK.standardGaussianMeasureOnEuclidean ι) =
      (Fintype.card ι : ℝ) := by
  rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian,
    integral_norm_sq_stdGaussian, finrank_euclideanSpace]

/-- The expected norm of the actual coefficient Gaussian is at most the
square root of its actual number of coordinates. -/
theorem standardGaussian_integral_norm_le_sqrt_card :
    (∫ x : EuclideanSpace ℝ ι, ‖x‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      Real.sqrt (Fintype.card ι : ℝ) := by
  rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]
  simpa only [finrank_euclideanSpace] using
    (integral_norm_stdGaussian_le_sqrt_finrank (E := EuclideanSpace ℝ ι))

end
end SlowEquilibration.GaussianNormMean
