module
public import Paper.GaussianPositivity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Gaussian bridge identity underlying the forward heat step. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace FRSB

/-- The actual positive-time Gaussian heat density. -/
def heatDensity (t x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (2 * t))

lemma heatDensity_eq_gaussianPDFReal {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    heatDensity t x = gaussianPDFReal 0 t.toNNReal x := by
  simp only [heatDensity, gaussianPDFReal, Real.coe_toNNReal _ ht, sub_zero]

lemma heatDensity_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatDensity t x := by
  unfold heatDensity
  positivity

lemma gaussian_bridge_exponent {r t : ℝ} (hr : 0 < r) (hrt : r < t) (x y : ℝ) :
    -(x - y) ^ 2 / (2 * (t - r)) - y ^ 2 / (2 * r) =
      -x ^ 2 / (2 * t) - (y - r / t * x) ^ 2 / (2 * (r * (t - r) / t)) := by
  have ht : 0 < t := hr.trans hrt
  field_simp [ht.ne', hr.ne', (sub_pos.mpr hrt).ne']
  <;> ring

lemma gaussian_bridge_prefactor {r t : ℝ} (hr : 0 < r) (hrt : r < t) :
    (Real.sqrt (2 * Real.pi * (t - r)))⁻¹ * (Real.sqrt (2 * Real.pi * r))⁻¹ =
      (Real.sqrt (2 * Real.pi * t))⁻¹ * (Real.sqrt (2 * Real.pi * (r * (t - r) / t)))⁻¹ := by
  have ht : 0 < t := hr.trans hrt
  rw [← mul_inv, ← mul_inv]
  congr 1
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp [ht.ne', hr.ne', (sub_pos.mpr hrt).ne']
  <;> ring

/-- Completing the square gives the exact Gaussian bridge factorization. -/
theorem gaussian_bridge_density {r t : ℝ} (hr : 0 < r) (hrt : r < t) (x y : ℝ) :
    heatDensity (t - r) (x - y) * heatDensity r y =
      heatDensity t x * heatDensity (r * (t - r) / t) (y - r / t * x) := by
  unfold heatDensity
  calc
    _ = ((Real.sqrt (2 * Real.pi * (t - r)))⁻¹ * (Real.sqrt (2 * Real.pi * r))⁻¹) *
        (Real.exp (-(x - y) ^ 2 / (2 * (t - r))) * Real.exp (-y ^ 2 / (2 * r))) := by ring
    _ = ((Real.sqrt (2 * Real.pi * t))⁻¹ * (Real.sqrt (2 * Real.pi * (r * (t - r) / t)))⁻¹) *
        (Real.exp (-x ^ 2 / (2 * t)) * Real.exp (-(y - r / t * x) ^ 2 / (2 * (r * (t - r) / t)))) := by
      rw [← Real.exp_add, ← Real.exp_add, gaussian_bridge_prefactor hr hrt]
      congr 1
      apply congrArg Real.exp
      simpa only [sub_eq_add_neg, neg_div] using gaussian_bridge_exponent hr hrt x y
    _ = _ := by ring

lemma heatDensity_sub_eq_gaussianPDFReal {t : ℝ} (ht : 0 ≤ t) (m y : ℝ) :
    heatDensity t (y - m) = gaussianPDFReal m t.toNNReal y := by
  simp only [heatDensity, gaussianPDFReal, Real.coe_toNNReal _ ht]

/-- Exact convolution-to-expectation identity for the Gaussian bridge. -/
theorem gaussian_bridge_convolution {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (x : ℝ) (F : ℝ → ℝ) (hF : Measurable F) :
    (∫ y, heatDensity (t - r) (x - y) * heatDensity r y * F y) =
      heatDensity t x * Paper.gaussianExpectation
        (fun z => F (r / t * x + Real.sqrt (r * (t - r) / t) * z)) := by
  have ht : 0 < t := hr.trans hrt
  have hv : 0 < r * (t - r) / t := by positivity
  simp_rw [gaussian_bridge_density hr hrt x]
  rw [Paper.gaussianExpectation_shift_eq_integral _ _ hv.le F hF,
    integral_gaussianReal_eq_integral_smul (show (r * (t - r) / t).toNNReal ≠ 0 by
      exact ne_of_gt (Real.toNNReal_pos.mpr hv))]
  simp only [smul_eq_mul, ← heatDensity_sub_eq_gaussianPDFReal hv.le]
  rw [← integral_const_mul]
  congr 1
  ext y
  ring

/-- The heat-step correction is the negative logarithm of a real Gaussian
expectation with its exact bridge mean and variance. -/
def forwardHeatCorrection (r t : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  -Real.log (Paper.gaussianExpectation
    (fun z => Real.exp (-w (r / t * x + Real.sqrt (r * (t - r) / t) * z))))

lemma forwardHeat_average_integrable (r t x : ℝ) (w : ℝ → ℝ)
    (hw : Continuous w) (hnon : ∀ y, 0 ≤ w y) :
    Integrable (fun z => Real.exp (-w (r / t * x + Real.sqrt (r * (t - r) / t) * z)))
      (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono'
    (by fun_prop)
  exact .of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnon _))

lemma forwardHeat_average_pos (r t x : ℝ) (w : ℝ → ℝ)
    (hw : Continuous w) (hnon : ∀ y, 0 ≤ w y) :
    0 < Paper.gaussianExpectation
      (fun z => Real.exp (-w (r / t * x + Real.sqrt (r * (t - r) / t) * z))) := by
  apply (integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le)
    (forwardHeat_average_integrable r t x w hw hnon)).mpr
  have he : Function.support (fun z => Real.exp (-w (r / t * x + Real.sqrt (r * (t - r) / t) * z))) = univ := by
    ext z
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.exp_pos _).ne'
  rw [he]
  simp

lemma forwardHeatCorrection_nonneg (r t x : ℝ) (w : ℝ → ℝ)
    (hw : Continuous w) (hnon : ∀ y, 0 ≤ w y) :
    0 ≤ forwardHeatCorrection r t w x := by
  unfold forwardHeatCorrection
  apply neg_nonneg.mpr
  apply Real.log_nonpos (forwardHeat_average_pos r t x w hw hnon).le
  have hi := integral_mono (forwardHeat_average_integrable r t x w hw hnon)
    (integrable_const (1 : ℝ)) (fun z => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnon _)))
  simpa [Paper.gaussianExpectation] using hi

/-- Re-exponentiation recovers the genuine weighted forward heat density. -/
theorem forwardHeatCorrection_density {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (x : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (hnon : ∀ y, 0 ≤ w y) :
    heatDensity t x * Real.exp (-forwardHeatCorrection r t w x) =
      ∫ y, heatDensity (t - r) (x - y) * heatDensity r y * Real.exp (-w y) := by
  rw [gaussian_bridge_convolution hr hrt x _ (by fun_prop)]
  unfold forwardHeatCorrection
  rw [neg_neg, Real.exp_log (forwardHeat_average_pos r t x w hw hnon)]

end FRSB
