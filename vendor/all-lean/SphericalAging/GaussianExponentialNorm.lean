module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

public section

/-! Linear-exponential growth is integrable under an actual Gaussian
measure. This supplies domination for the rotation concentration proof. -/
noncomputable section
namespace SphericalAging.GaussianExponentialNorm
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_exp_norm (μ : Measure E) [IsGaussian μ] (b : ℝ) :
    Integrable (fun x => Real.exp (b*‖x‖)) μ := by
  obtain ⟨C,hC,hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hDom := hI.const_mul (Real.exp (b^2/C))
  apply hDom.mono' (by fun_prop)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _),←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : C*(b^2/C)=b^2 := by field_simp
    have hh := sq_nonneg (C*‖x‖-b)
    have hn : 0≤C*‖x‖^2+b^2/C := by positivity
    nlinarith [sq_nonneg b])

theorem integrable_exp_lipschitz
    (μ : Measure E) [IsGaussian μ] (f : E→ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) (t : ℝ) :
    Integrable (fun x => Real.exp (t*f x)) μ := by
  have hI := (integrable_exp_norm μ (|t| * (L:ℝ))).const_mul (Real.exp (|t| * |f 0|))
  apply hI.mono' ((hf.continuous.measurable.const_mul t).exp.aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _),←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hfl : |f x-f 0|≤(L:ℝ)*‖x‖ := by
      simpa only [Real.dist_eq,dist_zero_right] using hf.dist_le_mul x 0
    have hfa : |f x| ≤ |f 0| + (L:ℝ)*‖x‖ := by
      have hh := abs_add_le (f x-f 0) (f 0)
      rw [sub_add_cancel] at hh
      linarith
    have ht := mul_le_mul_of_nonneg_left hfa (abs_nonneg t)
    have hh := le_abs_self (t*f x)
    rw [abs_mul] at hh
    nlinarith)

end SphericalAging.GaussianExponentialNorm
