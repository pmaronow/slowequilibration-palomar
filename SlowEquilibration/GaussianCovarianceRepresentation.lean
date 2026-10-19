-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDominatedEdge
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! Every genuine centered finite-dimensional Gaussian law with bounded
covariance is an actual linear image of a standard Gaussian with the stated
operator norm. Degenerate covariance is allowed. -/

@[expose] public section
namespace SlowEquilibration.GaussianCovarianceRepresentation
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma centered_covarianceOperator_inner (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) (x y : E) :
    inner ℝ (covarianceOperator μ x) y = covarianceBilin μ x y := by
  rw [covarianceOperator_inner IsGaussian.memLp_two_id,
    covarianceBilin_apply IsGaussian.memLp_two_id]
  simp only [id_eq, hmean, sub_zero]

/-- Synthesis map for an actual positive covariance factorization. -/
def synthesis {m : ℕ} (u : Fin m → E) : EuclideanSpace ℝ (Fin m) →L[ℝ] E :=
  ∑ i, (EuclideanSpace.proj i).smulRight (u i)

@[simp] lemma synthesis_apply {m : ℕ} (u : Fin m → E) (g : EuclideanSpace ℝ (Fin m)) :
    synthesis u g = ∑ i, g i • u i := by
  simp [synthesis]

@[simp] lemma synthesis_adjoint_apply {m : ℕ} (u : Fin m → E) (x : E) (i : Fin m) :
    (synthesis u).adjoint x i = inner ℝ (u i) x := by
  have h := ContinuousLinearMap.adjoint_inner_left (synthesis u)
    (EuclideanSpace.single i 1) x
  simpa [synthesis_apply, PiLp.inner_apply, EuclideanSpace.single_apply, real_inner_comm] using h

lemma synthesis_comp_adjoint {m : ℕ} (u : Fin m → E) :
    (synthesis u).comp (synthesis u).adjoint = ∑ i, InnerProductSpace.rankOne ℝ (u i) (u i) := by
  ext x
  simp [synthesis_apply, InnerProductSpace.rankOne_apply]

/-- Fixed-dimensional version of Mathlib's positive rank-one factorization;
we expose the actual finrank so later bounds are uniform over covariance laws. -/
lemma positive_fixed_factor (T : E →L[ℝ] E) (hT : T.IsPositive) :
    ∃ u : Fin (Module.finrank ℝ E) → E,
      T = ∑ i, InnerProductSpace.rankOne ℝ (u i) (u i) := by
  let u (i : Fin (Module.finrank ℝ E)) : E :=
    Real.sqrt (hT.isSymmetric.eigenvalues rfl i) • hT.isSymmetric.eigenvectorBasis rfl i
  refine ⟨u, ContinuousLinearMap.ext fun x => ?_⟩
  calc
    T x = T (∑ i, (hT.isSymmetric.eigenvectorBasis rfl).repr x i •
        hT.isSymmetric.eigenvectorBasis rfl i) := by
      rw [OrthonormalBasis.sum_repr]
    _ = ∑ i, inner ℝ (hT.isSymmetric.eigenvectorBasis rfl i) x •
        (hT.isSymmetric.eigenvalues rfl i • hT.isSymmetric.eigenvectorBasis rfl i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      have he : T (hT.isSymmetric.eigenvectorBasis rfl i) =
          hT.isSymmetric.eigenvalues rfl i • hT.isSymmetric.eigenvectorBasis rfl i :=
        hT.isSymmetric.apply_eigenvectorBasis rfl i
      rw [map_smul, he, OrthonormalBasis.repr_apply_apply]
    _ = _ := by
      simp only [_root_.sum_apply, InnerProductSpace.rankOne_apply, u]
      apply Finset.sum_congr rfl
      intro i _
      simp only [inner_smul_left, conj_trivial, smul_smul]
      congr 1
      calc
        _ = inner ℝ (hT.isSymmetric.eigenvectorBasis rfl i) x *
            (Real.sqrt (hT.isSymmetric.eigenvalues rfl i))^2 := by
          rw [Real.sq_sqrt (hT.toLinearMap.nonneg_eigenvalues rfl i)]
        _ = _ := by ring


/-- A concrete standard-Gaussian realization with the exact covariance
operator bound. This includes singular covariance without an invertibility
assumption or an assumed realization. -/
theorem exists_fixed_bounded_gaussian_realization (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcov : ∀ x : E, covarianceBilin μ x x ≤ σ^2 * ‖x‖^2) :
    ∃ W : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E,
      ‖W‖ ≤ σ ∧ (SYK.standardGaussianMeasureOnEuclidean (Fin (Module.finrank ℝ E))).map W = μ := by
  have hpos : (covarianceOperator μ).IsPositive :=
    isPositive_covarianceOperator
  let m := Module.finrank ℝ E
  obtain ⟨u, hu⟩ := positive_fixed_factor (covarianceOperator μ) hpos
  let W := synthesis u
  have hWW : W.comp W.adjoint = covarianceOperator μ := (synthesis_comp_adjoint u).trans hu.symm
  have hadj (x : E) : ‖W.adjoint x‖^2 = covarianceBilin μ x x := by
    rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_left]
    change inner ℝ x (W (W.adjoint x)) = _
    rw [← ContinuousLinearMap.comp_apply, hWW, real_inner_comm]
    exact centered_covarianceOperator_inner μ hmean x x
  have hnormAdj : ‖W.adjoint‖ ≤ σ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hσ
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hσ (norm_nonneg x))).mp
    rw [hadj, mul_pow]
    exact hcov x
  have hnorm : ‖W‖ ≤ σ := by
    simpa only [LinearIsometryEquiv.norm_map] using hnormAdj
  refine ⟨W, hnorm, ?_⟩
  rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero, hmean]
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left]
    change inner ℝ x (W (W.adjoint y)) = _
    rw [← ContinuousLinearMap.comp_apply, hWW, real_inner_comm]
    rw [centered_covarianceOperator_inner μ hmean, covarianceBilin_comm]


theorem exists_bounded_gaussian_realization (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcov : ∀ x : E, covarianceBilin μ x x ≤ σ^2 * ‖x‖^2) :
    ∃ m : ℕ, ∃ W : EuclideanSpace ℝ (Fin m) →L[ℝ] E,
      ‖W‖ ≤ σ ∧ (SYK.standardGaussianMeasureOnEuclidean (Fin m)).map W = μ := by
  obtain ⟨W, hW, hμ⟩ := exists_fixed_bounded_gaussian_realization μ hmean hσ hcov
  exact ⟨Module.finrank ℝ E, W, hW, hμ⟩

end
end SlowEquilibration.GaussianCovarianceRepresentation
