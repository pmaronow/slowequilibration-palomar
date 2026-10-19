-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEEdgeConcentration

@[expose] public section

/-! Actual extremal eigenvalue convergence: outer confinement is supplemented
with the proved Jacobi edge approximation, rather than interpreted as inclusion. -/

namespace SlowEquilibration.GOEExtremalEdges

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

def upperEdgeBad (n : ℕ) (eps : ℝ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  {W | eps < |eigenvalues n W 0 - 2|}

lemma upperEdgeBad_measurable (n : ℕ) (eps : ℝ) : MeasurableSet (upperEdgeBad n eps) :=
  measurableSet_lt measurable_const ((((measurable_pi_apply 0).comp (eigenvalues_measurable n)).sub_const 2).abs)

/-- The true top Jacobi gap tends to zero; this is not a spectral-limit assumption. -/
lemma topJacobiGap_tendsto :
    Tendsto (fun n : ℕ => orderedJacobiGaps n 0) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n : ℕ in atTop, orderedJacobiGaps n 0 ≤ naturalEdgeScale n 212 := by
    filter_upwards [edgeLength_tents_eventually] with n hn
    exact orderedJacobiGaps_natural_top hn 0 (by norm_num)
  exact squeeze_zero' (Eventually.of_forall (fun n => orderedJacobiGaps_nonneg n 0))
    hupper (naturalEdgeScale_tendsto 212)

lemma upper_edge_bad_probability_eventually {h eps : ℝ} (hh : 0 ≤ h) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (upperEdgeBad n eps) ≤
        32 * Real.exp (-h ^ 2) := by
  have hcost := (traceCost_fixed_tendsto hh (by norm_num : (0 : ℝ) < 1)).eventually
    (gt_mem_nhds (by positivity : 0 < eps / 10))
  have hgap := topJacobiGap_tendsto.eventually (gt_mem_nhds (by positivity : 0 < eps / 2))
  filter_upwards [hcost, hgap,
    goodEvent_failure_probability_eventually hh (by norm_num : (0 : ℝ) < 1)] with n hcost hgap hprob
  have hsub : upperEdgeBad n eps ⊆ (goodEvent n h 1)ᶜ := by
    intro W hW hgood
    have hdiff := spectralGood_relative_error n hh (by norm_num : (0 : ℝ) < 1) le_rfl
      hcost.le hgood 0
    have hg0 := orderedJacobiGaps_nonneg n 0
    have hg4 := orderedJacobiGaps_le_four n 0
    have hdiff' : |eigenvalues n W 0 - (2 - orderedJacobiGaps n 0)| ≤ eps / 2 :=
      hdiff.trans (by nlinarith)
    have htri : |eigenvalues n W 0 - 2| ≤
        |eigenvalues n W 0 - (2 - orderedJacobiGaps n 0)| + |orderedJacobiGaps n 0| := by
      calc
        _ = |(eigenvalues n W 0 - (2 - orderedJacobiGaps n 0)) + (-orderedJacobiGaps n 0)| :=
          congrArg abs (by ring)
        _ ≤ _ := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    rw [abs_of_nonneg hg0] at htri
    exact (not_lt_of_ge (htri.trans (by linarith))) hW
  exact (measureReal_mono hsub).trans hprob

/-- The actual largest GOE eigenvalue converges in probability to 2,
including the lower edge inclusion missing from outer confinement alone. -/
theorem largest_eigenvalue_converges_in_probability {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ =>
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (upperEdgeBad n eps))
      atTop (𝓝 0) :=
  tendsto_zero_of_gaussian_tail_envelope (fun _ => measureReal_nonneg)
    (fun _ hh => upper_edge_bad_probability_eventually hh heps)

lemma matrixToGaussian_neg {k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ) :
    matrixToGaussian (-W) = -matrixToGaussian W := by ext i j; rfl

lemma matrixOrderedEigenvalues_neg_exists {k : ℕ} (A : GOEAsymptotics.GaussianMatrix k) (i : Fin k) :
    ∃ j, matrixOrderedEigenvalues (-A) j = -matrixOrderedEigenvalues A i := by
  let B := symmetrizeGaussianMatrix (1 / 2 : ℝ) A
  let C := symmetrizeGaussianMatrix (1 / 2 : ℝ) (-A)
  have hB := gaussianMatrixCLM_symmetric B (symmetrize_half_symmetric A)
  have hC := gaussianMatrixCLM_symmetric C (symmetrize_half_symmetric (-A))
  have hneg : C = -B := by
    ext j l
    change (1 / 2 : ℝ) * (-A j l + -A l j) = -((1 / 2 : ℝ) * (A j l + A l j))
    ring
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
  let x := hB.eigenvectorBasis hn i
  have hx : x ≠ 0 := (hB.eigenvectorBasis hn).toBasis.ne_zero i
  have hvec : Module.End.HasEigenvector (gaussianMatrixCLM C).toLinearMap
      (-hB.eigenvalues hn i) x := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hx⟩
    rw [hneg, show gaussianMatrixCLM (-B) = -gaussianMatrixCLM B from
      (gaussianMatrixToCLM k).map_neg B]
    change -(gaussianMatrixCLM B x) = (-hB.eigenvalues hn i) • x
    have he := hB.apply_eigenvectorBasis hn i
    change gaussianMatrixCLM B x = hB.eigenvalues hn i • x at he
    rw [he, neg_smul]
  obtain ⟨j, hj⟩ := hC.exists_eigenvalues_eq hn (Module.End.hasEigenvalue_of_hasEigenvector hvec)
  exact ⟨j, hj⟩

lemma eigenvalues_neg_exists (n : ℕ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    ∃ j, eigenvalues n (-W) j = -eigenvalues n W i := by
  simpa only [eigenvalues, matrixToGaussian_neg] using matrixOrderedEigenvalues_neg_exists (matrixToGaussian W) i

lemma eigenvalues_antitone (n : ℕ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Antitone (eigenvalues n W) := by
  unfold eigenvalues matrixOrderedEigenvalues
  exact LinearMap.IsSymmetric.eigenvalues_antitone _ _

lemma smallest_eigenvalue_eq_neg_largest (n : ℕ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    eigenvalues n W (Fin.last n) = -eigenvalues n (-W) 0 := by
  obtain ⟨j, hj⟩ := eigenvalues_neg_exists n W (Fin.last n)
  have hlo := eigenvalues_antitone n (-W) (show (0 : Fin (n + 1)) ≤ j by exact Fin.zero_le j)
  rw [hj] at hlo
  obtain ⟨l, hl⟩ := eigenvalues_neg_exists n (-W) 0
  rw [neg_neg] at hl
  have hhi := eigenvalues_antitone n W (show l ≤ Fin.last n by exact Fin.le_last l)
  rw [hl] at hhi
  linarith

lemma realization_neg (n : ℕ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    GOEDeterminantMoments.realization n (-A) = -GOEDeterminantMoments.realization n A := by
  ext i j
  change goeScale n * (-A i j + -A j i) = -(goeScale n * (A i j + A j i))
  ring

lemma goeLaw_neg (n : ℕ) :
    (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).map (fun W => -W) =
      SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1 := by
  have hneg : (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).map (fun A => -A) =
      stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) :=
    stdGaussian_map (LinearIsometryEquiv.neg ℝ)
  rw [← GOEDeterminantMoments.realization_law n,
    Measure.map_map (show Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => -W) by fun_prop)
      (GOEDeterminantMoments.realization_measurable n)]
  have heq : (fun W => -W) ∘ GOEDeterminantMoments.realization n =
      GOEDeterminantMoments.realization n ∘ (fun A => -A) := by
    funext A
    exact (realization_neg n A).symm
  rw [heq, ← Measure.map_map (GOEDeterminantMoments.realization_measurable n)
    (show Measurable (fun A : GOEAsymptotics.GaussianMatrix (n + 1) => -A) by fun_prop), hneg]

def lowerEdgeBad (n : ℕ) (eps : ℝ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  {W | eps < |eigenvalues n W (Fin.last n) + 2|}

lemma lower_edge_bad_probability (n : ℕ) (eps : ℝ) :
    (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (lowerEdgeBad n eps) =
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (upperEdgeBad n eps) := by
  have heq : lowerEdgeBad n eps = (fun W => -W) ⁻¹' upperEdgeBad n eps := by
    ext W
    simp only [lowerEdgeBad, upperEdgeBad, mem_preimage, mem_ofPred_eq,
      smallest_eigenvalue_eq_neg_largest]
    rw [show -eigenvalues n (-W) 0 + 2 = -(eigenvalues n (-W) 0 - 2) by ring, abs_neg]
  rw [heq]
  conv_rhs => rw [← goeLaw_neg n]
  simp only [Measure.real]
  rw [Measure.map_apply (show Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => -W) by fun_prop)
    (upperEdgeBad_measurable n eps)]

/-- The actual smallest GOE eigenvalue converges in probability to -2. -/
theorem smallest_eigenvalue_converges_in_probability {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ =>
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (lowerEdgeBad n eps))
      atTop (𝓝 0) := by
  simpa only [lower_edge_bad_probability] using largest_eigenvalue_converges_in_probability heps

end
end SlowEquilibration.GOEExtremalEdges
