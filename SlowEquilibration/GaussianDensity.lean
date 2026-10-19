-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.FunProp

/-!
# The genuine standard Gaussian Lebesgue density

The explicit radial density is identified with Mathlib's actual standard Gaussian
law by Gaussian integration, completing the square, and uniqueness of transforms.
The proof follows the genuine finite-dimensional method in OAI's
`Probability/Perceptron/Sphere/GaussianPolar.lean` at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, using current Mathlib directly.
-/

@[expose] public section

namespace SlowEquilibration.GaussianDensity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The usual positive finite standard-Gaussian normalization constant. -/
def normalizer (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : ℝ :=
  ((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹

/-- The ordinary standard-Gaussian Lebesgue density. -/
def density (x : E) : ℝ := normalizer E * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)

/-- The law with this actual explicit Lebesgue density, before identification. -/
def densityLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  volume.withDensity (fun x => ENNReal.ofReal (density x))

omit [MeasurableSpace E] [BorelSpace E] in
lemma normalizer_pos : 0 < normalizer E := by
  unfold normalizer
  positivity

omit [MeasurableSpace E] [BorelSpace E] in
lemma density_pos (x : E) : 0 < density x := mul_pos normalizer_pos (Real.exp_pos _)

omit [MeasurableSpace E] [BorelSpace E] in
lemma density_continuous : Continuous (density (E := E)) := by
  unfold density
  fun_prop

lemma density_integrable : Integrable (density (E := E)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := ((1 / 2 : ℝ) : ℂ)) (by norm_num) 0 (0 : E)).re
  have hr : Integrable (fun x : E => Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) := by
    convert h using 1
    ext x
    simp only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
    exact (Complex.exp_ofReal_re _).symm
  exact hr.const_mul _

lemma density_integral : (∫ x : E, density x) = 1 := by
  unfold density
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num)]
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
  unfold normalizer
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos (by positivity) _).ne'

instance densityLaw_probability : IsProbabilityMeasure (densityLaw E) where
  measure_univ := by
    rw [densityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal density_integrable
        (Eventually.of_forall fun x => (density_pos x).le), density_integral]
    norm_num

omit [MeasurableSpace E] [BorelSpace E] in
/-- Completing the square for the actual radial density. -/
lemma density_complete_square (z x : E) :
    density x * Real.exp (inner ℝ z x) =
      Real.exp (‖z‖ ^ 2 / 2) * density (x - z) := by
  have he : -(1 / 2 : ℝ) * ‖x‖ ^ 2 + inner ℝ z x =
      ‖z‖ ^ 2 / 2 - (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm x z]
    ring
  unfold density
  calc
    _ = normalizer E * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2 + inner ℝ z x) := by
      rw [Real.exp_add]
      ring
    _ = _ := by
      rw [he, Real.exp_sub, neg_mul, Real.exp_neg]
      ring

lemma densityLaw_laplace (z : E) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ z x)) ∂densityLaw E) =
      ENNReal.ofReal (Real.exp (‖z‖ ^ 2 / 2)) := by
  rw [densityLaw, lintegral_withDensity_eq_lintegral_mul _
    density_continuous.measurable.ennreal_ofReal (by fun_prop)]
  simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (density_pos _).le, density_complete_square]
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (density x)) z,
    ← ofReal_integral_eq_lintegral_ofReal density_integrable
      (Eventually.of_forall fun x => (density_pos x).le), density_integral]
  simp

lemma densityLaw_exp_integrable (z : E) :
    Integrable (fun x => Real.exp (inner ℝ z x)) (densityLaw E) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp
  rw [densityLaw_laplace]
  exact ENNReal.ofReal_ne_top

lemma densityLaw_exp_integral (z : E) :
    (∫ x, Real.exp (inner ℝ z x) ∂densityLaw E) = Real.exp (‖z‖ ^ 2 / 2) := by
  have h := densityLaw_laplace z
  rw [← ofReal_integral_eq_lintegral_ofReal (densityLaw_exp_integrable z)
    (Eventually.of_forall fun x => (Real.exp_pos _).le)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => (Real.exp_pos _).le)
    (Real.exp_pos _).le).mp h

lemma integral_exp_inner_stdGaussian (v : E) (a : ℝ) :
    (∫ x, Real.exp (a * inner ℝ v x) ∂stdGaussian E) = Real.exp (a ^ 2 * ‖v‖ ^ 2 / 2) := by
  have H := mgf_gaussianReal
    ⟨(innerSL ℝ v).continuous.measurable.aemeasurable,
      IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)⟩ a
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm,
    Real.coe_toNNReal (‖v‖ ^ 2) (sq_nonneg ‖v‖), zero_mul, zero_add] at H
  change (∫ x, Real.exp (a * inner ℝ v x) ∂stdGaussian E) = Real.exp (‖v‖ ^ 2 * a ^ 2 / 2) at H
  convert H using 1
  congr 1
  ring

/-- Identification with Mathlib's actual standard Gaussian, proved rather than assumed. -/
theorem densityLaw_eq_stdGaussian : densityLaw E = stdGaussian E := by
  apply Measure.ext_of_charFun
  funext z
  have hm : mgf (fun x => inner ℝ z x) (densityLaw E) =
      mgf (fun x => inner ℝ z x) (stdGaussian E) := by
    funext t
    change (∫ x, Real.exp (t * inner ℝ z x) ∂densityLaw E) =
      (∫ x, Real.exp (t * inner ℝ z x) ∂stdGaussian E)
    rw [integral_exp_inner_stdGaussian]
    have h := densityLaw_exp_integral (t • z)
    simp only [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    exact h
  have hs : integrableExpSet (fun x => inner ℝ z x) (densityLaw E) = univ := by
    apply eq_univ_of_forall
    intro t
    change Integrable (fun x => Real.exp (t * inner ℝ z x)) _
    simpa only [real_inner_smul_left] using densityLaw_exp_integrable (t • z)
  have h := eqOn_complexMGF_of_mgf hm (show (Complex.I : ℂ) ∈
    {w | w.re ∈ interior (integrableExpSet (fun x => inner ℝ z x) (densityLaw E))} by simp [hs])
  simpa only [complexMGF, charFun_apply, real_inner_comm z, mul_comm Complex.I] using h

/-- The genuine explicit, positive, smooth radial Lebesgue density of `stdGaussian`. -/
theorem stdGaussian_eq_withDensity :
    stdGaussian E = volume.withDensity (fun x => ENNReal.ofReal (density x)) :=
  densityLaw_eq_stdGaussian.symm

end
end SlowEquilibration.GaussianDensity
