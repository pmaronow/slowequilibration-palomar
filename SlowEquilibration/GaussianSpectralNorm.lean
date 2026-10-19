-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDominatedEdge

/-! The actual two-sided operator norm tail follows from the proved Gaussian
upper-edge bound for a matrix and its negative. -/

@[expose] public section
namespace SlowEquilibration.GaussianSpectralNorm
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK GaussianDominatedEdge
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma symmetric_norm_le_of_eigenvalues {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) {m : ℕ}
    (hm : Module.finrank ℝ E = m) {r : ℝ} (hr : 0 ≤ r)
    (he : ∀ i : Fin m, |hT.eigenvalues hm i| ≤ r) : ‖T‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg x))).mp
  let B := hT.eigenvectorBasis hm
  have hdiag (i : Fin m) : B.repr (T x) i = hT.eigenvalues hm i * B.repr x i :=
    hT.eigenvectorBasis_apply_self_apply hm x i
  rw [mul_pow, ← B.repr.norm_map (T x), ← B.repr.norm_map x]
  simp only [PiLp.norm_sq_eq_of_L2, hdiag, Real.norm_eq_abs, sq_abs, mul_pow,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr (he i)

lemma neg_eigenvalue_le_upper {n : ℕ} (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (i : Fin (n+1)) :
    -matrixOrderedEigenvalues A i ≤ matrixOrderedEigenvalues (-A) 0 := by
  have hnA : ∀ i j, (-A) i j = (-A) j i := by intro i j; change -A i j = -A j i; rw [hA]
  let h := gaussianMatrixCLM_symmetric A hA
  let hn := gaussianMatrixCLM_symmetric (-A) hnA
  let hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let v := h.eigenvectorBasis hd i
  have hv : v ≠ 0 := (h.eigenvectorBasis hd).orthonormal.ne_zero i
  have he : gaussianMatrixCLM A v = h.eigenvalues hd i • v := h.apply_eigenvectorBasis hd i
  have hneg : gaussianMatrixCLM (-A) = -(gaussianMatrixCLM A) :=
    (gaussianMatrixToCLM (n+1)).map_neg A
  have hen : gaussianMatrixCLM (-A) v = (-h.eigenvalues hd i) • v := by
    rw [hneg, ContinuousLinearMap.neg_apply, he, neg_smul]
  have hHas : Module.End.HasEigenvalue (gaussianMatrixCLM (-A)).toLinearMap
      (-h.eigenvalues hd i) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hen, hv⟩
  obtain ⟨j, hj⟩ := hn.exists_eigenvalues_eq hd hHas
  rw [matrixOrderedEigenvalues_eq A hA, matrixOrderedEigenvalues_eq (-A) hnA]
  exact hj ▸ hn.eigenvalues_antitone hd (Fin.zero_le j)

lemma operator_norm_le_edges {n : ℕ} (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) {r : ℝ} (hr : 0 ≤ r)
    (hp : matrixOrderedEigenvalues A 0 ≤ r)
    (hn : matrixOrderedEigenvalues (-A) 0 ≤ r) : ‖gaussianMatrixCLM A‖ ≤ r := by
  apply symmetric_norm_le_of_eigenvalues (gaussianMatrixCLM A)
    (gaussianMatrixCLM_symmetric A hA) (m := n+1) (by simp) hr
  intro i
  have hupper := (eigenvalue_le_upper A hA i).trans hp
  have hlower := (neg_eigenvalue_le_upper A hA i).trans hn
  rw [matrixOrderedEigenvalues_eq A hA] at hupper hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem operator_norm_tail {ι : Type*} [Fintype ι] [DecidableEq ι] {n N : ℕ}
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hSym : ∀ z i j, W z i j = W z j i) (hN : n+1 ≤ N)
    {b : ℝ} (hb : 0 < b) (hW : ‖W‖ ≤ Real.sqrt (2*b/N))
    {t : ℝ} (ht : 0 ≤ t) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {z | 2*Real.sqrt b+t < ‖gaussianMatrixCLM (W z)‖} ≤
        2*Real.exp (-(N : ℝ)*t^2/(4*b)) := by
  have hneg : ∀ z i j, (-W) z i j = (-W) z j i := by
    intro z i j
    change -(W z i j) = -(W z j i)
    rw [hSym]
  have hWn : ‖-W‖ ≤ Real.sqrt (2*b/N) := by simpa only [norm_neg] using hW
  have hp := upperEigenvalue_tail_covarianceScale W hSym hN hb hW ht
  have hn := upperEigenvalue_tail_covarianceScale (-W) hneg hN hb hWn ht
  have hsub : {z | 2*Real.sqrt b+t < ‖gaussianMatrixCLM (W z)‖} ⊆
      {z | 2*Real.sqrt b+t ≤ upperEigenvalue W z} ∪
      {z | 2*Real.sqrt b+t ≤ upperEigenvalue (-W) z} := by
    intro z hz
    by_cases hpz : 2*Real.sqrt b+t ≤ upperEigenvalue W z
    · exact Or.inl hpz
    right
    by_contra hnz
    have he := operator_norm_le_edges (W z) (hSym z) (by positivity : 0 ≤ 2*Real.sqrt b+t)
      (not_le.mp hpz).le (not_le.mp hnz).le
    exact (not_le.mpr hz) he
  calc
    _ ≤ (SYK.standardGaussianMeasureOnEuclidean ι).real
        ({z | 2*Real.sqrt b+t ≤ upperEigenvalue W z} ∪
         {z | 2*Real.sqrt b+t ≤ upperEigenvalue (-W) z}) := measureReal_mono hsub
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

end
end SlowEquilibration.GaussianSpectralNorm
