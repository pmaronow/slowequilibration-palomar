-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEDeterminantMoments

@[expose] public section

/-!
# Exponentially small actual GOE edge failure

Eigenvalue Lipschitz estimates and genuine Gaussian concentration strengthen
proved spectral confinement in probability to an eventual exponential tail.
-/

namespace SlowEquilibration.GOEEdgeConcentration

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology Matrix.Norms.Frobenius

lemma gaussianMatrixCLM_norm_le {k : ℕ} (A : GOEAsymptotics.GaussianMatrix k) :
    ‖gaussianMatrixCLM A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  let V : Matrix (Fin k) (Fin 1) ℝ := Matrix.replicateCol (Fin 1) x.ofLp
  have h := Matrix.frobenius_norm_mul (gaussianToMatrix A) V
  have hV : ‖V‖ = ‖x‖ := Matrix.frobenius_norm_replicateCol _
  have hAV : ‖gaussianToMatrix A * V‖ = ‖gaussianMatrixCLM A x‖ := by
    have heq : gaussianToMatrix A * V = Matrix.replicateCol (Fin 1) (gaussianMatrixCLM A x).ofLp := by
      ext i j
      rfl
    rw [heq, Matrix.frobenius_norm_replicateCol]
  rw [hAV, hV, GOEDeterminantMoments.frobenius_gaussianToMatrix] at h
  exact h

lemma symmetric_gaussian_eigenvalue_lipschitz {k : ℕ} (A B : GOEAsymptotics.GaussianMatrix k)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) (i : Fin k) :
    |matrixOrderedEigenvalues A i - matrixOrderedEigenvalues B i| ≤ ‖A - B‖ := by
  rw [matrixOrderedEigenvalues_eq A hA, matrixOrderedEigenvalues_eq B hB]
  have h := symmetric_eigenvalue_norm_bound (gaussianMatrixCLM A) (gaussianMatrixCLM B)
    (gaussianMatrixCLM_symmetric A hA) (gaussianMatrixCLM_symmetric B hB)
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k) i
  have heq : gaussianMatrixCLM A - gaussianMatrixCLM B = gaussianMatrixCLM (A - B) := by
    exact (gaussianMatrixToCLM k).map_sub A B |>.symm
  rw [heq] at h
  exact h.trans (gaussianMatrixCLM_norm_le (A - B))

def edgeLip (n : ℕ) : ℝ≥0 := ⟨2 * |goeScale n|, by positivity⟩

def realizedEigenvalues (n : ℕ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : Fin (n + 1) → ℝ :=
  matrixOrderedEigenvalues (symmetrizeGaussianMatrix (goeScale n) A)

lemma realizedEigenvalues_difference (n : ℕ) (A B : GOEAsymptotics.GaussianMatrix (n + 1))
    (i : Fin (n + 1)) :
    |realizedEigenvalues n A i - realizedEigenvalues n B i| ≤ (edgeLip n : ℝ) * ‖A - B‖ := by
  have hs (C : GOEAsymptotics.GaussianMatrix (n + 1)) :
      ∀ i j, symmetrizeGaussianMatrix (goeScale n) C i j =
        symmetrizeGaussianMatrix (goeScale n) C j i := by
    intro i j
    change goeScale n * (C i j + C j i) = goeScale n * (C j i + C i j)
    ring
  exact (symmetric_gaussian_eigenvalue_lipschitz _ _ (hs A) (hs B) i).trans
    (GOEDeterminantMoments.symmetrize_difference_norm (goeScale n) A B)

/-- Maximum absolute ordered eigenvalue of the actual symmetrized Gaussian realization. -/
def realizedRadius (n : ℕ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |realizedEigenvalues n A i|)

lemma abs_eigenvalue_le_realizedRadius (n : ℕ) (A : GOEAsymptotics.GaussianMatrix (n + 1))
    (i : Fin (n + 1)) : |realizedEigenvalues n A i| ≤ realizedRadius n A := by
  exact Finset.le_sup' (fun j => |realizedEigenvalues n A j|) (Finset.mem_univ i)

lemma realizedRadius_lipschitz (n : ℕ) : LipschitzWith (edgeLip n) (realizedRadius n) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  change |realizedRadius n A - realizedRadius n B| ≤ (edgeLip n : ℝ) * ‖A - B‖
  have hupper (C D : GOEAsymptotics.GaussianMatrix (n + 1)) :
      realizedRadius n C ≤ realizedRadius n D + (edgeLip n : ℝ) * ‖C - D‖ := by
    apply Finset.sup'_le _ _ (fun i _ => ?_)
    have he := realizedEigenvalues_difference n C D i
    have ha := abs_abs_sub_abs_le (realizedEigenvalues n C i) (realizedEigenvalues n D i)
    have hi := abs_eigenvalue_le_realizedRadius n D i
    linarith [(abs_le.mp (ha.trans he)).2]
  apply abs_le.mpr
  have hAB := hupper A B
  have hBA := hupper B A
  rw [norm_sub_rev B A] at hBA
  constructor <;> linarith

lemma edgeLip_square (n : ℕ) : (edgeLip n : ℝ) ^ 2 = 2 / (n + 1 : ℝ) := by
  change (2 * |goeScale n|) ^ 2 = _
  rw [mul_pow, sq_abs]
  have h := goeScale_square n
  rw [show (2 : ℝ) ^ 2 = 2 * 2 by norm_num, mul_assoc, h]
  ring

lemma realizedRadius_subGaussian (n : ℕ) :
    HasSubgaussianMGF (fun A => realizedRadius n A -
      ∫ B, realizedRadius n B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
      (Real.pi ^ 2 / (2 * (n + 1 : ℝ))).toNNReal
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) := by
  have h := SphericalAging.GaussianLipschitzConcentration.centered_hasSubgaussianMGF _
    (realizedRadius_lipschitz n)
  have hc : SphericalAging.GaussianSmoothConcentration.rotationConstant (edgeLip n) =
      (Real.pi ^ 2 / (2 * (n + 1 : ℝ))).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity)]
    change (Real.pi / 2) ^ 2 * (edgeLip n : ℝ) ^ 2 = _
    rw [edgeLip_square]
    field_simp
  rw [hc] at h
  exact h

lemma edgeBad_measurable (n : ℕ) (eps : ℝ) : MeasurableSet (edgeBad n eps) := by
  simpa only [edgeBad, ofPred_exists, Function.comp_def] using MeasurableSet.iUnion (fun i : Fin (n + 1) =>
    measurableSet_lt measurable_const
      (((measurable_pi_apply i).comp (eigenvalues_measurable n)).abs))

lemma realizedRadius_bad_iff (n : ℕ) (eps : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    2 + eps < realizedRadius n A ↔ GOEDeterminantMoments.realization n A ∈ edgeBad n eps := by
  have heig : eigenvalues n (GOEDeterminantMoments.realization n A) = realizedEigenvalues n A := by
    unfold eigenvalues GOEDeterminantMoments.realization realizedEigenvalues
    rw [matrixToGaussian_gaussianToMatrix]
  rw [edgeBad]
  simp only [mem_ofPred_eq, heig]
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : Fin (n + 1) => |realizedEigenvalues n A i|)
    exact ⟨i, by simpa only [realizedRadius, hi] using h⟩
  · rintro ⟨i, hi⟩
    exact hi.trans_le (abs_eigenvalue_le_realizedRadius n A i)

lemma realizedRadius_bad_probability (n : ℕ) (eps : ℝ) :
    (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real {A | 2 + eps < realizedRadius n A} =
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (edgeBad n eps) := by
  rw [← GOEDeterminantMoments.realization_law n]
  simp only [Measure.real]
  rw [Measure.map_apply (GOEDeterminantMoments.realization_measurable n) (edgeBad_measurable n eps)]
  apply congrArg ENNReal.toReal
  apply congrArg (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
  ext A
  exact realizedRadius_bad_iff n eps A

lemma realizedRadius_bad_tendsto {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ =>
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real {A | 2 + eps < realizedRadius n A})
      atTop (𝓝 0) := by
  simpa only [realizedRadius_bad_probability] using spectrum_converges_to_semicircle_support heps

lemma realizedRadius_centered_right_tail (n : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real
      {A | delta ≤ realizedRadius n A -
        ∫ B, realizedRadius n B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))} ≤
      Real.exp (-(n + 1 : ℝ) * delta ^ 2 / Real.pi ^ 2) := by
  have h := (realizedRadius_subGaussian n).measure_ge_le hdelta
  rw [Real.coe_toNNReal _ (by positivity)] at h
  convert h using 1
  congr 1
  field_simp

lemma realizedRadius_centered_left_tail (n : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real
      {A | delta ≤ (∫ B, realizedRadius n B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) -
        realizedRadius n A} ≤ Real.exp (-(n + 1 : ℝ) * delta ^ 2 / Real.pi ^ 2) := by
  have h := (realizedRadius_subGaussian n).neg.measure_ge_le hdelta
  simp only [Pi.neg_apply, neg_sub] at h
  rw [Real.coe_toNNReal _ (by positivity)] at h
  convert h using 1
  congr 1
  field_simp

lemma gaussian_edge_tail_tendsto {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun n : ℕ => Real.exp (-(n + 1 : ℝ) * delta ^ 2 / Real.pi ^ 2)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hcoef : 0 < delta ^ 2 / Real.pi ^ 2 := div_pos (sq_pos_of_pos hdelta) (sq_pos_of_pos Real.pi_pos)
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hn.atTop_mul_const hcoef)
  convert hh using 1
  funext n
  congr 1
  ring

/-- The mean edge location is derived from the proved actual confinement law
and Gaussian concentration; no expected spectral barrier is an input. -/
theorem mean_realizedRadius_eventually_le {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (∫ A, realizedRadius n A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) ≤ 2 + eps := by
  have hprob := (realizedRadius_bad_tendsto (by positivity : 0 < eps / 2)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have htail := (gaussian_edge_tail_tendsto (by positivity : 0 < eps / 2)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hprob, htail] with n hprob htail
  by_contra hmean
  have hm : 2 + eps < ∫ A, realizedRadius n A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)) :=
    lt_of_not_ge hmean
  have hsub : {A | 2 + eps / 2 < realizedRadius n A}ᶜ ⊆
      {A | eps / 2 ≤ (∫ B, realizedRadius n B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) -
        realizedRadius n A} := by
    intro A hA
    have hA' : realizedRadius n A ≤ 2 + eps / 2 := le_of_not_gt hA
    change eps / 2 ≤ _
    linarith
  have hlarge := measureReal_mono (μ := stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) hsub
  have hsmall := realizedRadius_centered_left_tail n (by positivity : 0 ≤ eps / 2)
  have hcompl := measureReal_compl (μ := stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
    (s := {A | 2 + eps / 2 < realizedRadius n A}) (measurableSet_lt measurable_const (realizedRadius_lipschitz n).continuous.measurable)
  rw [probReal_univ] at hcompl
  rw [hcompl] at hlarge
  linarith

/-- Actual exponentially small fixed-gap GOE edge failure for all sufficiently
large dimensions, with an explicit (non-sharp) Gaussian rotation constant. -/
theorem exponential_edge_failure_eventually {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (edgeBad n eps) ≤
        Real.exp (-(n + 1 : ℝ) * eps ^ 2 / (4 * Real.pi ^ 2)) := by
  filter_upwards [mean_realizedRadius_eventually_le (by positivity : 0 < eps / 2)] with n hmean
  have hsub : {A | 2 + eps < realizedRadius n A} ⊆
      {A | eps / 2 ≤ realizedRadius n A -
        ∫ B, realizedRadius n B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))} := by
    intro A hA
    change eps / 2 ≤ _
    change 2 + eps < realizedRadius n A at hA
    linarith
  rw [← realizedRadius_bad_probability n eps]
  calc
    _ ≤ _ := measureReal_mono hsub
    _ ≤ Real.exp (-(n + 1 : ℝ) * (eps / 2) ^ 2 / Real.pi ^ 2) :=
      realizedRadius_centered_right_tail n (by positivity : 0 ≤ eps / 2)
    _ = _ := congrArg Real.exp (by ring)

end
end SlowEquilibration.GOEEdgeConcentration
