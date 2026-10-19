-- SPDX-License-Identifier: Apache-2.0
module

public import OAI.Probability.GaussianPropeller.Quantile

@[expose] public section

noncomputable section

namespace SlowEquilibration.GaussianQuantileConvolution

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

private noncomputable def normalCDF (a : ℝ) : ℝ := (gaussianReal 0 1).real (Iic a)

private theorem normalCDF_convolution (a : ℝ) :
    ∫ x, normalCDF (a + x) ∂gaussianReal 0 1 = (gaussianReal 0 2).real (Iic a) := by
  let g := gaussianReal 0 1
  have hi : Integrable ((Iic a).indicator (1 : ℝ → ℝ)) (g ∗ g) :=
    integrable_const _ |>.indicator measurableSet_Iic
  have hc := integral_conv hi
  have hconv : g ∗ g = gaussianReal 0 2 := by
    simpa [g, show (1 : ℝ≥0) + 1 = 2 by norm_num] using (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0)
      (v₁ := 1) (v₂ := 1))
  rw [hconv, integral_indicator_one measurableSet_Iic] at hc
  have hinner (x : ℝ) :
      ∫ y, (Iic a).indicator (1 : ℝ → ℝ) (x + y) ∂g = normalCDF (a - x) := by
    have heq : (fun y => (Iic a).indicator (1 : ℝ → ℝ) (x + y)) =
        (Iic (a - x)).indicator 1 := by
      funext y
      simp only [indicator_apply, mem_Iic, Pi.one_apply]
      split_ifs <;> first | rfl | (exfalso; linarith)
    rw [heq, integral_indicator_one measurableSet_Iic]
    rfl
  simp_rw [hinner] at hc
  change ∫ x, normalCDF (a + x) ∂g = _
  rw [hc]
  have hneg : g.map (fun x : ℝ => -x) = g := by simpa [g] using
    (gaussianReal_map_neg (μ := 0) (v := 1))
  have hmc : Measurable normalCDF := by
    have heq : normalCDF = cdf (gaussianReal 0 1) := by
      funext x
      exact (cdf_eq_real (gaussianReal 0 1) x).symm
    rw [heq]
    exact (monotone_cdf (gaussianReal 0 1)).measurable
  have hm : AEStronglyMeasurable (fun x => normalCDF (a + x)) (g.map (fun x : ℝ => -x)) := by
    exact (hmc.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  have he := integral_map (by fun_prop : AEMeasurable (fun x : ℝ => -x) g) hm
  rw [hneg] at he
  simpa only [sub_eq_add_neg] using he

private theorem normalCDF_variance_two (a : ℝ) :
    (gaussianReal 0 2).real (Iic a) = normalCDF (a / Real.sqrt 2) := by
  have hv : NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) * 1 = (2 : ℝ≥0) := by
    apply NNReal.eq
    change (Real.sqrt 2)^2 * 1 = (2 : ℝ)
    norm_num [Real.sq_sqrt]
  have hm := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt 2)
  rw [hv, mul_zero] at hm
  have heq : (fun x : ℝ => Real.sqrt 2 * x) ⁻¹' Iic a = Iic (a / Real.sqrt 2) := by
    ext x
    simp only [mem_preimage, mem_Iic, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    rw [mul_comm]
  rw [← hm, measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic, heq]
  rfl

private theorem normalCDF_neg_le_exp {r : ℝ} (hr : 0 ≤ r) :
    normalCDF (-r) ≤ Real.exp (-r^2 / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id)
    (t := -r) (-r) (by linarith : -r ≤ 0) (integrable_exp_mul_gaussianReal (-r))
  rw [mgf_id_gaussianReal] at h
  simp only [id_eq, zero_mul, NNReal.coe_one, one_mul, zero_add] at h
  rw [← Real.exp_add] at h
  have he : - -r * -r + (-r)^2 / 2 = -r^2 / 2 := by ring
  rw [he] at h
  exact h

open OAI.GaussianPropeller.Quantile

/-- The Gaussian quantile library's analytic CDF agrees with Gaussian measure. -/
theorem Φ_eq_gaussianReal (a : ℝ) : Φ a = (gaussianReal 0 1).real (Iic a) := by
  have hp : gaussianPDFReal 0 1 = φ := by
    funext x
    simp [gaussianPDFReal, φ]
  have he := gaussianReal_apply_eq_integral (0 : ℝ) (v := 1) (by norm_num) (Iic a)
  rw [hp] at he
  change gaussianReal 0 1 (Iic a) = ENNReal.ofReal (Φ a) at he
  rw [measureReal_def, he, ENNReal.toReal_ofReal (Φ_pos a).le]

/-- Adding independent standard Gaussian noise rescales the Gaussian CDF. -/
theorem integral_Φ_add (a : ℝ) :
    ∫ x, Φ (a + x) ∂gaussianReal 0 1 = Φ (a / Real.sqrt 2) := by
  simp_rw [Φ_eq_gaussianReal]
  exact (normalCDF_convolution a).trans (normalCDF_variance_two a)

/-- Standard Gaussian Chernoff bound, in the analytic CDF convention. -/
theorem Φ_neg_le_exp {r : ℝ} (hr : 0 ≤ r) : Φ (-r) ≤ Real.exp (-r^2 / 2) := by
  rw [Φ_eq_gaussianReal]
  exact normalCDF_neg_le_exp hr

end SlowEquilibration.GaussianQuantileConvolution
