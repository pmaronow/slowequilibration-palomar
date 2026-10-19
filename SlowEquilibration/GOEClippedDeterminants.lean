-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SpectralTraceLipschitz

@[expose] public section

/-!
# Actual clipped GOE determinant logarithms

The clipped logarithm is the literal sum over actual ordered GOE eigenvalues.
Its Gaussian Lipschitz constant, centered MGF, exact relation to the ordinary
absolute determinant, and equality on the actual spectral confinement event
are derived. A fixed regularization is not substituted for the determinant.
-/

namespace SlowEquilibration.GOEClippedDeterminants

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics GOEEdgeConcentration SpectralTraceLipschitz
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

lemma symmetrize_symmetric {k : ℕ} (sigma : ℝ) (A : GOEAsymptotics.GaussianMatrix k) :
    ∀ i j, symmetrizeGaussianMatrix sigma A i j = symmetrizeGaussianMatrix sigma A j i := by
  intro i j
  change sigma * (A i j + A j i) = sigma * (A j i + A i j)
  ring

def clippedTrace (n : ℕ) (k rho : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  ∑ i, clippedLog k rho (realizedEigenvalues n A i)

def clippedLip (n : ℕ) (rho : ℝ) : ℝ≥0 :=
  ⟨Real.sqrt (n + 1 : ℝ) * (1 / |rho|) * (2 * |goeScale n|), by positivity⟩

lemma clippedTrace_lipschitz (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    LipschitzWith (clippedLip n rho) (clippedTrace n k rho) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  change |clippedTrace n k rho A - clippedTrace n k rho B| ≤ (clippedLip n rho : ℝ) * ‖A - B‖
  have h := spectral_trace_difference
    (symmetrizeGaussianMatrix (goeScale n) A) (symmetrizeGaussianMatrix (goeScale n) B)
    (symmetrize_symmetric _ _) (symmetrize_symmetric _ _) (clippedLog k rho) (clippedLog_lipschitz k hrho)
  have hh := h.trans (mul_le_mul_of_nonneg_left
    (GOEDeterminantMoments.symmetrize_difference_norm (goeScale n) A B) (by positivity))
  change |(∑ i, clippedLog k rho (matrixOrderedEigenvalues (symmetrizeGaussianMatrix (goeScale n) A) i)) -
    (∑ i, clippedLog k rho (matrixOrderedEigenvalues (symmetrizeGaussianMatrix (goeScale n) B) i))| ≤
    Real.sqrt ((n + 1 : ℕ) : ℝ) * (1 / rho) * (2 * |goeScale n| * ‖A - B‖) at hh
  change _ ≤ (Real.sqrt (n + 1 : ℝ) * (1 / |rho|) * (2 * |goeScale n|)) * ‖A - B‖
  simpa only [clippedTrace, realizedEigenvalues, NNReal.coe_mk, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, abs_of_pos hrho, mul_assoc] using hh

lemma clippedLip_square (n : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    (clippedLip n rho : ℝ) ^ 2 = 2 / rho ^ 2 := by
  change (Real.sqrt (n + 1 : ℝ) * (1 / |rho|) * (2 * |goeScale n|)) ^ 2 = _
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), one_div_pow, sq_abs, mul_pow, sq_abs]
  have hscale := goeScale_square n
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hs : 2 * goeScale n ^ 2 * (n + 1 : ℝ) = 1 := by rw [hscale, inv_mul_cancel₀ hn]
  field_simp
  nlinarith [hs]

/-- The exact actual clipped logdet has a dimension-independent centered Gaussian MGF. -/
theorem clippedTrace_centered_subGaussian (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    HasSubgaussianMGF (fun A => clippedTrace n k rho A -
        ∫ B, clippedTrace n k rho B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
      (Real.pi ^ 2 / (2 * rho ^ 2)).toNNReal (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) := by
  have h := SphericalAging.GaussianLipschitzConcentration.centered_hasSubgaussianMGF _
    (clippedTrace_lipschitz n k hrho)
  have hc : SphericalAging.GaussianSmoothConcentration.rotationConstant (clippedLip n rho) =
      (Real.pi ^ 2 / (2 * rho ^ 2)).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity)]
    change (Real.pi / 2) ^ 2 * (clippedLip n rho : ℝ) ^ 2 = _
    rw [clippedLip_square n hrho]
    ring
  rw [hc] at h
  exact h

lemma shifted_det_eq_prod {m : ℕ} (k : ℝ) (B : GOEAsymptotics.GaussianMatrix m)
    (hB : ∀ i j, B i j = B j i) :
    (k • (1 : Matrix (Fin m) (Fin m) ℝ) - gaussianToMatrix B).det =
      ∏ i, (k - matrixOrderedEigenvalues B i) := by
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
  let hS := gaussianMatrixCLM_symmetric B hB
  have hchar : (gaussianMatrixCLM B).toLinearMap.charpoly = (gaussianToMatrix B).charpoly := by
    exact Matrix.charpoly_toLin (gaussianToMatrix B) (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  have h := hS.charpoly_eq hn
  rw [hchar] at h
  have he := congrArg (Polynomial.eval k) h
  rw [Matrix.eval_charpoly] at he
  simpa only [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    matrixOrderedEigenvalues_eq B hB, RCLike.ofReal_real_eq_id, id_eq] using he

/-- The literal ordinary absolute determinant, before expectation normalization. -/
def absoluteDet (n : ℕ) (k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  |(k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - GOEDeterminantMoments.realization n A).det|

lemma absoluteDet_eq_prod (n : ℕ) (k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    absoluteDet n k A = ∏ i, |k - realizedEigenvalues n A i| := by
  rw [absoluteDet, GOEDeterminantMoments.realization,
    shifted_det_eq_prod k _ (symmetrize_symmetric _ _), Finset.abs_prod]
  rfl

lemma exp_clippedTrace (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho)
    (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    Real.exp (clippedTrace n k rho A) = ∏ i, max |k - realizedEigenvalues n A i| rho := by
  unfold clippedTrace clippedLog
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (hrho.trans_le (le_max_right _ _))

lemma absoluteDet_le_exp_clippedTrace (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho)
    (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    absoluteDet n k A ≤ Real.exp (clippedTrace n k rho A) := by
  rw [absoluteDet_eq_prod, exp_clippedTrace n k hrho]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => le_max_left _ _)

/-- On the actual fixed-gap spectral confinement event, the clipped determinant
is exactly the ordinary absolute determinant. -/
lemma absoluteDet_eq_exp_clippedTrace_of_gap (n : ℕ) {k rho g : ℝ}
    (hrho : 0 < rho) (hgap : 2 + g + rho ≤ k)
    (A : GOEAsymptotics.GaussianMatrix (n + 1)) (hA : realizedRadius n A ≤ 2 + g) :
    absoluteDet n k A = Real.exp (clippedTrace n k rho A) := by
  rw [absoluteDet_eq_prod, exp_clippedTrace n k hrho]
  apply Finset.prod_congr rfl
  intro i _
  apply (max_eq_left ?_).symm
  have hi := (le_abs_self (realizedEigenvalues n A i)).trans
    ((abs_eigenvalue_le_realizedRadius n A i).trans hA)
  exact (by linarith : rho ≤ k - realizedEigenvalues n A i).trans (le_abs_self _)

lemma clippedTrace_integrable (n : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (clippedTrace n k rho) (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) :=
  SphericalAging.GaussianSmoothConcentration.integrable_lipschitz _ (clippedTrace_lipschitz n k hrho)

lemma absoluteDet_nonneg (n : ℕ) (k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    0 ≤ absoluteDet n k A := abs_nonneg _

lemma absoluteDet_measurable (n : ℕ) (k : ℝ) : Measurable (absoluteDet n k) := by
  unfold absoluteDet
  have hreal := GOEDeterminantMoments.realization_measurable n
  fun_prop

def gapBad (n : ℕ) (g : ℝ) : Set (GOEAsymptotics.GaussianMatrix (n + 1)) :=
  {A | 2 + g / 2 < realizedRadius n A}

lemma gapBad_measurable (n : ℕ) (g : ℝ) : MeasurableSet (gapBad n g) :=
  measurableSet_lt measurable_const (realizedRadius_lipschitz n).continuous.measurable

lemma absoluteDet_eq_clipped_of_not_bad (n : ℕ) {k g : ℝ} (hg : 0 < g) (hk : 2 + g ≤ k)
    (A : GOEAsymptotics.GaussianMatrix (n + 1)) (hA : A ∉ gapBad n g) :
    absoluteDet n k A = Real.exp (clippedTrace n k (g / 2) A) := by
  apply absoluteDet_eq_exp_clippedTrace_of_gap n (g := g / 2) (by positivity) (by linarith) A
  exact le_of_not_gt hA

lemma gapBad_exponential_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real (gapBad n g) ≤
        Real.exp (-(n + 1 : ℝ) * g ^ 2 / (16 * Real.pi ^ 2)) := by
  filter_upwards [exponential_edge_failure_eventually (by positivity : 0 < g / 2)] with n hn
  change (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real
    {A | 2 + g / 2 < realizedRadius n A} ≤ _
  rw [realizedRadius_bad_probability]
  exact hn.trans_eq (congrArg Real.exp (by ring))

end
end SlowEquilibration.GOEClippedDeterminants
