-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedDeterminants

@[expose] public section

/-! Exact scaling from the actual standard GOE law to the variance `b/N`
literal Matrix law used by the canonical spherical Hessian. -/

namespace SlowEquilibration.GOEScaling

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics GOEClippedDeterminants
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

def scaleFactor (n N : ℕ) (b : ℝ) : ℝ := Real.sqrt (b * (n + 1 : ℝ) / N)

lemma scaleFactor_pos (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 < b) :
    0 < scaleFactor n N b := Real.sqrt_pos.mpr (div_pos (mul_pos hb (by positivity)) (by exact_mod_cast hN))

lemma scaleFactor_square (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    scaleFactor n N b ^ 2 = b * (n + 1 : ℝ) / N := by
  apply Real.sq_sqrt
  positivity

lemma scaleFactor_le_sqrt {n N : ℕ} (hN : 0 < N) (hmN : n + 1 ≤ N) {b : ℝ} (hb : 0 ≤ b) :
    scaleFactor n N b ≤ Real.sqrt b := by
  apply Real.sqrt_le_sqrt
  apply (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmN) hb

lemma scaleFactor_goeScale (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    2 * (scaleFactor n N b * goeScale n) ^ 2 = b / (N : ℝ) := by
  rw [mul_pow, scaleFactor_square n hN hb]
  have hs := goeScale_square n
  have hm : (n + 1 : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  have hs' : 2 * goeScale n ^ 2 * (n + 1 : ℝ) = 1 := by rw [hs, inv_mul_cancel₀ hm]
  nlinarith [hs']

lemma symmetrize_scalar {m : ℕ} (a sigma : ℝ) (A : GOEAsymptotics.GaussianMatrix m) :
    a • symmetrizeGaussianMatrix sigma A = symmetrizeGaussianMatrix (a * sigma) A := by
  rw [symmetrizeGaussianMatrix, symmetrizeGaussianMatrix, smul_smul]

lemma gaussianToMatrix_scalar {m : ℕ} (a : ℝ) (A : GOEAsymptotics.GaussianMatrix m) :
    gaussianToMatrix (a • A) = a • gaussianToMatrix A := by ext i j; rfl

lemma matrixToGaussian_scalar {m : ℕ} (a : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) :
    matrixToGaussian (a • W) = a • matrixToGaussian W := by ext i j; rfl

/-- Exact scaled Gaussian realization of the literal variance-`b/N` GOE law. -/
lemma scaled_realization_law (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).map
        (fun A => scaleFactor n N b • GOEDeterminantMoments.realization n A) =
      SphericalGaussianJet.goeLaw (n + 1) N b := by
  have h := congrArg (fun μ => μ.map (gaussianToMatrix (k := n + 1)))
    (goeLaw_bridge (n + 1) N b (scaleFactor n N b * goeScale n) (scaleFactor_goeScale n hN hb))
  rw [Measure.map_map (gaussianToMatrix_measurable (n + 1)) (matrixToGaussian_measurable (n + 1))] at h
  simp only [Function.comp_def, gaussianToMatrix_matrixToGaussian, Measure.map_id'] at h
  rw [OAI.CriticalSK.goeLaw, Measure.map_map (gaussianToMatrix_measurable (n + 1))
    (symmetrizeGaussianMatrix_continuous _).measurable] at h
  convert h.symm using 1
  congr 1
  funext A
  simp only [Function.comp_def]
  rw [← symmetrize_scalar, gaussianToMatrix_scalar]
  rfl

/-- Exact pushforward from the same actual standard Matrix GOE construction. -/
theorem goeLaw_scale (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).map
        (fun W => scaleFactor n N b • W) = SphericalGaussianJet.goeLaw (n + 1) N b := by
  rw [← GOEDeterminantMoments.realization_law n,
    Measure.map_map (show Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => scaleFactor n N b • W) by fun_prop)
      (GOEDeterminantMoments.realization_measurable n)]
  exact scaled_realization_law n hN hb

lemma shifted_scaled_matrix {m : ℕ} {a : ℝ} (ha : a ≠ 0) (k : ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ) :
    k • (1 : Matrix (Fin m) (Fin m) ℝ) - a • W = a • ((k / a) • 1 - W) := by
  rw [smul_sub, smul_smul, mul_div_cancel₀ k ha]

/-- The ordinary absolute determinant scales by the actual deterministic factor. -/
theorem absolute_determinant_scale {m : ℕ} {a : ℝ} (ha : 0 < a) (k : ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ) :
    |(k • (1 : Matrix (Fin m) (Fin m) ℝ) - a • W).det| =
      a ^ m * |((k / a) • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det| := by
  rw [shifted_scaled_matrix ha.ne' k W, Matrix.det_smul, Fintype.card_fin, abs_mul,
    abs_of_pos (pow_pos ha m)]

/-- A fixed physical gap becomes at least the indicated standard-GOE gap,
uniformly over all dimensions not exceeding the ambient normalization. -/
theorem scaled_shift_gap {n N : ℕ} (hN : 0 < N) (hmN : n + 1 ≤ N)
    {b g k : ℝ} (hb : 0 < b) (hg : 0 < g) (hk : 2 * Real.sqrt b + g ≤ k) :
    2 + g / Real.sqrt b ≤ k / scaleFactor n N b := by
  have ha := scaleFactor_pos n hN hb
  have haB := scaleFactor_le_sqrt hN hmN hb.le
  have hB := Real.sqrt_pos.mpr hb
  apply (le_div_iff₀ ha).mpr
  calc
    _ ≤ (2 + g / Real.sqrt b) * Real.sqrt b :=
      mul_le_mul_of_nonneg_left haB (by positivity)
    _ = 2 * Real.sqrt b + g := by field_simp
    _ ≤ k := hk

end
end SlowEquilibration.GOEScaling
