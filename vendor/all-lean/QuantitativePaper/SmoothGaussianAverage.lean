module
public import QuantitativePaper.GaussianDerivativeBounds

@[expose] public section

/-! Actual zero-mass Gaussian steps, including local integrable domination
and global bounds for all positive-order derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussianShiftAverage {n : ℕ} (A : Field n →L[ℝ] E) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z,f (x+A z) ∂fieldGaussian n

theorem integrable_fieldGaussian_norm (n : ℕ) : Integrable (fun z : Field n => ‖z‖) (fieldGaussian n) := by
  apply (SYK.integrable_exp_mul_norm (ι := Fin n) 1).mono' continuous_norm.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [Real.norm_of_nonneg (norm_nonneg _),one_mul]
    linarith [Real.add_one_le_exp ‖z‖]

theorem gaussianShiftAverage_smooth_inputs {n : ℕ} (N : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ j,1 ≤ j → j ≤ N → ∀ x,‖iteratedFDeriv ℝ j f x‖ ≤ K^j)
    (A : Field n →L[ℝ] E) :
    (∀ z,ContDiff ℝ N (fun x => f (x+A z))) ∧
    (∀ j,j ≤ N → ∀ x,AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun y => f (y+A z)) x) (fieldGaussian n)) ∧
    (∀ x,∃ s ∈ 𝓝 x,∃ B : ℕ → Field n → ℝ,
      (∀ j,j ≤ N → Integrable (B j) (fieldGaussian n)) ∧
      ∀ j,j ≤ N → ∀ y ∈ s,∀ z,‖iteratedFDeriv ℝ j (fun u => f (u+A z)) y‖ ≤ B j z) := by
  refine ⟨fun z => hf.comp (contDiff_id.add contDiff_const),?_,?_⟩
  · intro j hj x
    simp_rw [iteratedFDeriv_comp_add_right]
    exact ((hf.continuous_iteratedFDeriv (by norm_cast)).comp
      (continuous_const.add A.continuous)).aestronglyMeasurable
  · intro x
    let B : ℕ → Field n → ℝ := fun j z =>
      if j = 0 then |f x|+(L : ℝ)*(1+‖A‖*‖z‖) else K^j
    refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),B,?_,?_⟩
    · intro j hj
      by_cases hj0 : j = 0
      · simp only [B,hj0,ite_true]
        exact (integrable_const |f x|).add
          (((integrable_const (1 : ℝ)).add ((integrable_fieldGaussian_norm n).const_mul ‖A‖)).const_mul L)
      · simp only [B,hj0,ite_false]
        exact integrable_const _
    · intro j hj y hy z
      rw [iteratedFDeriv_comp_add_right]
      by_cases hj0 : j = 0
      · subst j
        simp only [B,ite_true,norm_iteratedFDeriv_zero,Real.norm_eq_abs]
        exact gaussian_shift_abs_le f L hlip A x y z hy
      · simp only [B,hj0,ite_false]
        exact hjets j (by omega) hj _

theorem contDiff_gaussianShiftAverage {n : ℕ} (N : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ j,1 ≤ j → j ≤ N → ∀ x,‖iteratedFDeriv ℝ j f x‖ ≤ K^j)
    (A : Field n →L[ℝ] E) : ContDiff ℝ N (gaussianShiftAverage A f) := by
  obtain ⟨h₁,h₂,h₃⟩ := gaussianShiftAverage_smooth_inputs N f hf L hlip K hK hjets A
  exact contDiff_integral_of_dominated_derivatives N (fieldGaussian n) _ h₁ h₂ h₃

theorem norm_iteratedFDeriv_gaussianShiftAverage_le {n : ℕ} (N j : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 0 ≤ K)
    (hjets : ∀ i,1 ≤ i → i ≤ N → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (A : Field n →L[ℝ] E) (hj0 : 1 ≤ j) (hj : j ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (gaussianShiftAverage A f) x‖ ≤ K^j := by
  obtain ⟨h₁,h₂,h₃⟩ := gaussianShiftAverage_smooth_inputs N f hf L hlip K hK hjets A
  rw [show iteratedFDeriv ℝ j (gaussianShiftAverage A f) x =
      ∫ z,iteratedFDeriv ℝ j (fun y => f (y+A z)) x ∂fieldGaussian n from
    iteratedFDeriv_integral_of_dominated_derivatives N (fieldGaussian n) _ h₁ h₂ h₃ j hj x]
  have hh := norm_integral_le_of_norm_le_const
    (μ := fieldGaussian n) (C := K^j)
    (f := fun z => iteratedFDeriv ℝ j (fun y => f (y+A z)) x)
    (Eventually.of_forall fun z => by rw [iteratedFDeriv_comp_add_right];exact hjets j hj0 hj _)
  simpa using hh

end QuantitativePaper
