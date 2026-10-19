-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadratic
public import SphericalAging.SphereInitialLaw

/-! Exponentially small lower radial tails for the genuine Gaussian seed of
spherical latitude concentration. The estimate follows from the exact
Gaussian quadratic exponential integral, rather than a variance bound. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.EntranceLatitudeGaussianRadius
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The exact negative quadratic Laplace transform of the original Gaussian. -/
theorem integral_exp_neg_half_norm_sq :
    (∫ x : E, Real.exp (-‖x‖ ^ 2 / 2) ∂stdGaussian E) =
      (2 : ℝ) ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
  have he (x : E) : inner ℝ (0 : E) x - (2 - 1) / 2 * ‖x‖ ^ 2 = -‖x‖ ^ 2 / 2 := by
    simp only [inner_zero_left]
    ring
  simpa only [he, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, Real.exp_zero,
    mul_one] using GaussianQuadratic.integral_exp_quadratic
      (E := E) (z := 2) (by norm_num) (0 : E)

/-- The small-radius event has an exponential bound in the actual dimension.
This includes zero-dimensional spaces, where both sides equal one. -/
theorem small_radius_probability_real :
    (stdGaussian E).real {x | ‖x‖ ≤ Real.sqrt (Module.finrank ℝ E : ℝ) / 2} ≤
      Real.exp (-(Module.finrank ℝ E : ℝ) / 8) := by
  let d : ℝ := Module.finrank ℝ E
  let b : ℝ := Real.exp (-d / 8)
  let F : E → ℝ := fun x => Real.exp (-‖x‖ ^ 2 / 2)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hb : 0 < b := Real.exp_pos _
  have hF : Integrable F (stdGaussian E) := by
    have he (x : E) : inner ℝ (0 : E) x - (2 - 1) / 2 * ‖x‖ ^ 2 = -‖x‖ ^ 2 / 2 := by
      simp only [inner_zero_left]
      ring
    simpa only [he] using GaussianQuadratic.integrable_exp_quadratic
      (E := E) (z := 2) (by norm_num) (0 : E)
  have hsub : {x : E | ‖x‖ ≤ Real.sqrt d / 2} ⊆ {x | b ≤ F x} := by
    intro x hx
    change ‖x‖ ≤ Real.sqrt d / 2 at hx
    apply Real.exp_le_exp.mpr
    have hs := Real.sq_sqrt hd
    have hr := Real.sqrt_nonneg d
    have hn := norm_nonneg x
    nlinarith
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x : E => (Real.exp_pos (-‖x‖ ^ 2 / 2)).le)
    hF b
  have hbound : b * (stdGaussian E).real {x | ‖x‖ ≤ Real.sqrt d / 2} ≤
      (2 : ℝ) ^ (-(d / 2)) := by
    apply le_trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hb.le)
    simpa [F, d] using hm.trans_eq (integral_exp_neg_half_norm_sq (E := E))
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hquot : (2 : ℝ) ^ (-(d / 2)) / b ≤ Real.exp (-d / 8) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [b]
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlog hd]
  exact ((le_div_iff₀ hb).mpr (by simpa [mul_comm] using hbound)).trans hquot

/-- ENNReal form, suitable for probability and restriction estimates. -/
theorem small_radius_probability :
    (stdGaussian E) {x | ‖x‖ ≤ Real.sqrt (Module.finrank ℝ E : ℝ) / 2} ≤
      ENNReal.ofReal (Real.exp (-(Module.finrank ℝ E : ℝ) / 8)) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact small_radius_probability_real

/-- The precise Gaussian seed law used by the spherical dynamics. -/
theorem spherical_seed_small_radius_probability_real (N : ℕ) :
    (SphericalAging.SphereInitialLaw.gaussianLaw N).real
      {x | ‖x‖ ≤ Real.sqrt (N : ℝ) / 2} ≤ Real.exp (-(N : ℝ) / 8) := by
  simpa [SphericalAging.SphereInitialLaw.gaussianLaw, finrank_euclideanSpace] using
    (small_radius_probability_real (E := EuclideanSpace ℝ (Fin N)))

/-- The Gaussian seed event in its ordinary measure-valued form. -/
theorem spherical_seed_small_radius_probability (N : ℕ) :
    (SphericalAging.SphereInitialLaw.gaussianLaw N)
      {x | ‖x‖ ≤ Real.sqrt (N : ℝ) / 2} ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 8)) := by
  simpa [SphericalAging.SphereInitialLaw.gaussianLaw, finrank_euclideanSpace] using
    (small_radius_probability (E := EuclideanSpace ℝ (Fin N)))

end SlowEquilibration.EntranceLatitudeGaussianRadius
