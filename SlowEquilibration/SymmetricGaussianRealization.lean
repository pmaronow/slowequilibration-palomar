-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCovarianceRepresentation

/-! Actual centered Gaussian symmetric matrix laws admit a fixed-dimensional
linear realization under the manuscript's covariance domination on symmetric
test matrices. Symmetry is required only almost surely for the original law. -/

@[expose] public section
namespace SlowEquilibration.SymmetricGaussianRealization
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianCovarianceRepresentation
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m : ℕ}

def symmetrizeLinear : GOEAsymptotics.GaussianMatrix m →ₗ[ℝ] GOEAsymptotics.GaussianMatrix m where
  toFun A := (1/2 : ℝ) • (A + transposeGaussianMatrix A)
  map_add' A B := by ext i j; change (1/2 : ℝ)*((A i j+B i j)+(A j i+B j i)) = _; change _ = (1/2 : ℝ)*(A i j+A j i)+(1/2 : ℝ)*(B i j+B j i); ring
  map_smul' r A := by ext i j; change (1/2 : ℝ)*(r*A i j+r*A j i) = r*((1/2 : ℝ)*(A i j+A j i)); ring

def symmetrize : GOEAsymptotics.GaussianMatrix m →L[ℝ] GOEAsymptotics.GaussianMatrix m where
  toLinearMap := symmetrizeLinear
  cont := symmetrizeGaussianMatrix_continuous (ι := Fin m) (1/2)

@[simp] lemma symmetrize_apply (A : GOEAsymptotics.GaussianMatrix m) (i j : Fin m) :
    symmetrize A i j = (A i j + A j i)/2 := by
  change (1/2 : ℝ) * (A i j + A j i) = _
  ring

lemma symmetrize_symmetric (A : GOEAsymptotics.GaussianMatrix m) :
    ∀ i j, symmetrize A i j = symmetrize A j i := by
  intro i j
  simp only [symmetrize_apply, add_comm]

lemma symmetrize_eq_self (A : GOEAsymptotics.GaussianMatrix m)
    (hA : ∀ i j, A i j = A j i) : symmetrize A = A := by
  ext i j
  simp only [symmetrize_apply, hA i j]
  ring

lemma symmetrize_norm_le (A : GOEAsymptotics.GaussianMatrix m) : ‖symmetrize A‖ ≤ ‖A‖ := by
  change ‖(1/2 : ℝ) • (A + transposeGaussianMatrix A)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  calc
    _ ≤ (1/2 : ℝ) * (‖A‖ + ‖transposeGaussianMatrix A‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

lemma symmetrize_inner (M A : GOEAsymptotics.GaussianMatrix m)
    (hA : ∀ i j, A i j = A j i) : inner ℝ (symmetrize M) A = inner ℝ M A := by
  have ht : transposeGaussianMatrix A = A := by ext i j; exact hA j i
  have hi := (transposeGaussianMatrix (ι := Fin m)).inner_map_map M A
  rw [ht] at hi
  change inner ℝ ((1/2 : ℝ) • (M + transposeGaussianMatrix M)) A = _
  rw [inner_smul_left, conj_trivial, inner_add_left, hi]
  ring

lemma covariance_domination_all (μ : Measure (GOEAsymptotics.GaussianMatrix m)) [IsGaussian μ]
    (hmean : ∫ A, A ∂μ = 0) (hSym : ∀ᵐ A ∂μ, ∀ i j, A i j = A j i)
    {σ : ℝ} (hcov : ∀ M : GOEAsymptotics.GaussianMatrix m,
      (∀ i j, M i j = M j i) → covarianceBilin μ M M ≤ σ^2 * ‖M‖^2)
    (M : GOEAsymptotics.GaussianMatrix m) : covarianceBilin μ M M ≤ σ^2 * ‖M‖^2 := by
  have he : covarianceBilin μ M M = covarianceBilin μ (symmetrize M) (symmetrize M) := by
    simp only [covarianceBilin_apply IsGaussian.memLp_two_id, id_eq, hmean, sub_zero]
    apply integral_congr_ae
    filter_upwards [hSym] with A hA
    rw [symmetrize_inner M A hA]
  rw [he]
  exact (hcov _ (symmetrize_symmetric M)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (symmetrize_norm_le M) 2)
      (sq_nonneg σ))

/-- The source Gaussian matrix itself, including degenerate covariance, is
the pushforward of a standard Gaussian in a fixed ambient dimension. -/
theorem exists_symmetric_bounded_realization
    (μ : Measure (GOEAsymptotics.GaussianMatrix m)) [IsGaussian μ]
    (hmean : ∫ A, A ∂μ = 0) (hSym : ∀ᵐ A ∂μ, ∀ i j, A i j = A j i)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hcov : ∀ M : GOEAsymptotics.GaussianMatrix m,
      (∀ i j, M i j = M j i) → covarianceBilin μ M M ≤ σ^2 * ‖M‖^2) :
    ∃ W : EuclideanSpace ℝ (Fin (Module.finrank ℝ (GOEAsymptotics.GaussianMatrix m))) →L[ℝ]
        GOEAsymptotics.GaussianMatrix m,
      ‖W‖ ≤ σ ∧ (∀ z i j, W z i j = W z j i) ∧
      (SYK.standardGaussianMeasureOnEuclidean
        (Fin (Module.finrank ℝ (GOEAsymptotics.GaussianMatrix m)))).map W = μ := by
  obtain ⟨L, hL, hμ⟩ := exists_fixed_bounded_gaussian_realization μ hmean hσ
    (covariance_domination_all μ hmean hSym hcov)
  let W := (symmetrize (m := m)).comp L
  refine ⟨W, ?_, fun z => symmetrize_symmetric (L z), ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ hσ
    intro z
    exact (symmetrize_norm_le (L z)).trans
      ((L.le_opNorm z).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg z)))
  · change (SYK.standardGaussianMeasureOnEuclidean
      (Fin (Module.finrank ℝ (GOEAsymptotics.GaussianMatrix m)))).map
      (symmetrize ∘ L) = μ
    rw [← Measure.map_map (symmetrize (m := m)).continuous.measurable L.continuous.measurable, hμ]
    have he : symmetrize =ᵐ[μ] id := hSym.mono (fun A hA => symmetrize_eq_self A hA)
    rw [Measure.map_congr he, Measure.map_id]

end
end SlowEquilibration.SymmetricGaussianRealization
