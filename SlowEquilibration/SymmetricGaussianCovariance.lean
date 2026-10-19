-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SymmetricGaussianRealization
public import SlowEquilibration.GaussianSpectralNorm

/-! The manuscript's literal trace-variance hypothesis supplies the proved
Gaussian realization, including singular covariance and almost-sure symmetry. -/

@[expose] public section
namespace SlowEquilibration.SymmetricGaussianCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianDominatedEdge SymmetricGaussianRealization
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m : ℕ}

def entries (A : GOEAsymptotics.GaussianMatrix m) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => A i j

lemma trace_mul_eq_inner (A M : GOEAsymptotics.GaussianMatrix m)
    (hM : ∀ i j, M i j = M j i) :
    Matrix.trace (entries A * entries M) = inner ℝ M A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, entries,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hM j i]

lemma trace_sq_eq_norm_sq (M : GOEAsymptotics.GaussianMatrix m)
    (hM : ∀ i j, M i j = M j i) :
    Matrix.trace (entries M * entries M) = ‖M‖^2 := by
  rw [trace_mul_eq_inner M M hM, real_inner_self_eq_norm_sq]

lemma trace_covariance_bound (μ : Measure (GOEAsymptotics.GaussianMatrix m)) [IsGaussian μ]
    {c : ℝ}
    (hvar : ∀ M : GOEAsymptotics.GaussianMatrix m, (∀ i j, M i j = M j i) →
      Var[fun A => Matrix.trace (entries A * entries M); μ] ≤
        c * Matrix.trace (entries M * entries M))
    (M : GOEAsymptotics.GaussianMatrix m) (hM : ∀ i j, M i j = M j i) :
    covarianceBilin μ M M ≤ c * ‖M‖^2 := by
  have h := hvar M hM
  simp_rw [trace_mul_eq_inner _ M hM] at h
  rw [real_inner_self_eq_norm_sq] at h
  rwa [covarianceBilin_self IsGaussian.memLp_two_id]

theorem exists_realization_of_trace_variance
    (μ : Measure (GOEAsymptotics.GaussianMatrix m)) [IsGaussian μ]
    (hmean : ∫ A, A ∂μ = 0) (hSym : ∀ᵐ A ∂μ, ∀ i j, A i j = A j i)
    {N : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hvar : ∀ M : GOEAsymptotics.GaussianMatrix m, (∀ i j, M i j = M j i) →
      Var[fun A => Matrix.trace (entries A * entries M); μ] ≤
        (2*b/N) * Matrix.trace (entries M * entries M)) :
    ∃ W : EuclideanSpace ℝ (Fin (Module.finrank ℝ (GOEAsymptotics.GaussianMatrix m))) →L[ℝ]
        GOEAsymptotics.GaussianMatrix m,
      ‖W‖ ≤ Real.sqrt (2*b/N) ∧ (∀ z i j, W z i j = W z j i) ∧
      (SYK.standardGaussianMeasureOnEuclidean
        (Fin (Module.finrank ℝ (GOEAsymptotics.GaussianMatrix m)))).map W = μ := by
  apply exists_symmetric_bounded_realization μ hmean hSym (Real.sqrt_nonneg _)
  intro M hM
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*b/N)]
  exact trace_covariance_bound μ hvar M hM

/-- The actual Gaussian matrix law, with precisely the source trace-variance
hypothesis, satisfies the sharp upper spectral tail. -/
theorem upper_edge_tail {n N : ℕ} (hN : n+1 ≤ N)
    (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsGaussian μ]
    (hmean : ∫ A, A ∂μ = 0) (hSym : ∀ᵐ A ∂μ, ∀ i j, A i j = A j i)
    {b : ℝ} (hb : 0 < b)
    (hvar : ∀ M : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, M i j = M j i) →
      Var[fun A => Matrix.trace (entries A * entries M); μ] ≤
        (2*b/N) * Matrix.trace (entries M * entries M))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {A | 2*Real.sqrt b+t ≤ matrixOrderedEigenvalues A 0} ≤
      Real.exp (-(N : ℝ)*t^2/(4*b)) := by
  obtain ⟨W, hW, hWs, hμ⟩ := exists_realization_of_trace_variance μ hmean hSym hb.le hvar
  have hs : MeasurableSet {A : GOEAsymptotics.GaussianMatrix (n+1) |
      2*Real.sqrt b+t ≤ matrixOrderedEigenvalues A 0} :=
    measurableSet_le measurable_const ((measurable_pi_apply 0).comp (matrixOrderedEigenvalues_measurable _))
  unfold Measure.real
  rw [← hμ, Measure.map_apply W.continuous.measurable hs]
  exact upperEigenvalue_tail_covarianceScale W hWs hN hb hW ht

lemma edge_scale_eq {n N : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    (Real.sqrt 2 * Real.sqrt (2*b/N)) * Real.sqrt (n+1 : ℝ) =
      2*Real.sqrt (b*(n+1)/N) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*b/N),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n+1),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ b*(n+1)/N)]
  ring

theorem mean_upper_edge {n N : ℕ}
    (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsGaussian μ]
    (hmean : ∫ A, A ∂μ = 0) (hSym : ∀ᵐ A ∂μ, ∀ i j, A i j = A j i)
    {b : ℝ} (hb : 0 ≤ b)
    (hvar : ∀ M : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, M i j = M j i) →
      Var[fun A => Matrix.trace (entries A * entries M); μ] ≤
        (2*b/N) * Matrix.trace (entries M * entries M)) :
    (∫ A, matrixOrderedEigenvalues A 0 ∂μ) ≤ 2*Real.sqrt (b*(n+1)/N) := by
  obtain ⟨W, hW, hWs, hμ⟩ := exists_realization_of_trace_variance μ hmean hSym hb hvar
  rw [← hμ, integral_map W.continuous.measurable.aemeasurable
    (matrixOrderedEigenvalues_continuous (n := n+1) 0).aestronglyMeasurable]
  exact (mean_upperEigenvalue_le W hWs (Real.sqrt_nonneg _) hW).trans_eq (edge_scale_eq hb)

/-- Full source covariance-dominated Gaussian operator-norm bound, with
degenerate covariance allowed and the actual operator norm. -/
theorem operator_norm_tail {n N : ℕ} (hN : n+1 ≤ N)
    (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsGaussian μ]
    (hmean : ∫ A, A ∂μ = 0) (hSym : ∀ᵐ A ∂μ, ∀ i j, A i j = A j i)
    {b : ℝ} (hb : 0 < b)
    (hvar : ∀ M : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, M i j = M j i) →
      Var[fun A => Matrix.trace (entries A * entries M); μ] ≤
        (2*b/N) * Matrix.trace (entries M * entries M))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {A | 2*Real.sqrt b+t < ‖gaussianMatrixCLM A‖} ≤
      2*Real.exp (-(N : ℝ)*t^2/(4*b)) := by
  obtain ⟨W, hW, hWs, hμ⟩ := exists_realization_of_trace_variance μ hmean hSym hb.le hvar
  have hs : MeasurableSet {A : GOEAsymptotics.GaussianMatrix (n+1) |
      2*Real.sqrt b+t < ‖gaussianMatrixCLM A‖} :=
    measurableSet_lt measurable_const (gaussianMatrixCLM_continuous (n+1)).norm.measurable
  unfold Measure.real
  rw [← hμ, Measure.map_apply W.continuous.measurable hs]
  exact GaussianSpectralNorm.operator_norm_tail W hWs hN hb hW ht

end
end SlowEquilibration.SymmetricGaussianCovariance
