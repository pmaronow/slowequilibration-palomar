-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact finite dimensional Gaussian quadratic exponential integrals. These
are the Gaussian integrals used by the spherical linear-field endpoint. -/

@[expose] public section

namespace SlowEquilibration.GaussianQuadratic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integrable_quadratic_lebesgue {b : ℝ} (hb : 0 < b) (w : E) :
    Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2 + inner ℝ w x)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (b : ℂ)) (by simpa using hb) 1 w).re
  convert h using 1
  ext x
  simp only [one_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_add]
  exact (Complex.exp_ofReal_re _).symm

theorem integral_quadratic_lebesgue {b : ℝ} (hb : 0 < b) (w : E) :
    (∫ x : E, Real.exp (-b * ‖x‖ ^ 2 + inner ℝ w x)) =
      (Real.pi / b) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (‖w‖ ^ 2 / (4 * b)) := by
  rw [← Complex.ofReal_inj]
  calc
    _ = ∫ x : E, Complex.exp (-(b : ℂ) * ‖x‖ ^ 2 + 1 * inner ℝ w x) := by
      rw [← integral_complex_ofReal]
      congr 1
      ext x
      simp only [one_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        ← Complex.ofReal_neg, ← Complex.ofReal_add, Complex.ofReal_exp]
    _ = _ := by
      rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb)]
      simp only [one_pow, one_mul]
      rw [← Complex.ofReal_div]
      have he : ((Module.finrank ℝ E : ℂ) / 2) = (((Module.finrank ℝ E : ℝ) / 2) : ℝ) := by push_cast; rfl
      rw [he, ← Complex.ofReal_cpow (by positivity)]
      push_cast
      rfl

omit [MeasurableSpace E] [BorelSpace E] in

theorem weighted_density_eq (z : ℝ) (w x : E) :
    GaussianDensity.density x * Real.exp (inner ℝ w x - (z - 1) / 2 * ‖x‖ ^ 2) =
      GaussianDensity.normalizer E * Real.exp (-(z / 2) * ‖x‖ ^ 2 + inner ℝ w x) := by
  unfold GaussianDensity.density
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integrable_exp_quadratic {z : ℝ} (hz : 0 < z) (w : E) :
    Integrable (fun x => Real.exp (inner ℝ w x - (z - 1) / 2 * ‖x‖ ^ 2))
      (stdGaussian E) := by
  rw [GaussianDensity.stdGaussian_eq_withDensity]
  apply (integrable_withDensity_iff_integrable_smul'
    GaussianDensity.density_continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (GaussianDensity.density_pos _).le,
    smul_eq_mul, weighted_density_eq] using
      (integrable_quadratic_lebesgue (by positivity : 0 < z / 2) w).const_mul
        (GaussianDensity.normalizer E)

theorem integral_exp_quadratic {z : ℝ} (hz : 0 < z) (w : E) :
    (∫ x, Real.exp (inner ℝ w x - (z - 1) / 2 * ‖x‖ ^ 2) ∂stdGaussian E) =
      z ^ (-((Module.finrank ℝ E : ℝ) / 2)) * Real.exp (‖w‖ ^ 2 / (2 * z)) := by
  rw [GaussianDensity.stdGaussian_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      GaussianDensity.density_continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (GaussianDensity.density_pos _).le,
    smul_eq_mul, weighted_density_eq]
  rw [integral_const_mul, integral_quadratic_lebesgue (by positivity : 0 < z / 2)]
  have harg : (4 : ℝ) * (z / 2) = 2 * z := by ring
  rw [harg, ← mul_assoc]
  congr 1
  unfold GaussianDensity.normalizer
  rw [show Real.pi / (z / 2) = (2 * Real.pi) / z by field_simp,
    Real.div_rpow (by positivity) hz.le, Real.rpow_neg hz.le]
  field_simp

end
end SlowEquilibration.GaussianQuadratic
