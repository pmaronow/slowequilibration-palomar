-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NegativeDefiniteOperators

/-! Actual matrix and orthonormal-coordinate criteria for quadratic negativity. -/
@[expose] public section
namespace SlowEquilibration.NegativeDefiniteOperators
open Set MeasureTheory Matrix
open OAI.CriticalSK GOEAsymptotics GOEMaximumDeterminant
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma matrix_operator_shift {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (k : ℝ) :
    gaussianMatrixCLM (matrixToGaussian (W - k • 1)) =
      gaussianMatrixCLM (matrixToGaussian W) - k • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext v i
  change ((W-k•1) *ᵥ v.ofLp) i = (W *ᵥ v.ofLp) i - k*v i
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

lemma negativeDefinite_shifted_matrix_iff {n : ℕ} (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hW : ∀ i j, W i j = W j i) (k : ℝ) :
    NegativeDefinite (gaussianMatrixCLM (matrixToGaussian (W-k•1))) ↔ W ∈ maximumEvent n k := by
  have hA : ∀ i j, matrixToGaussian W i j = matrixToGaussian W j i := hW
  rw [matrix_operator_shift, negativeDefinite_shift_iff _ (gaussianMatrixCLM_symmetric _ hA)
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1)]
  change (∀ i, _) ↔ matrixOrderedEigenvalues (matrixToGaussian W) 0 < k
  rw [matrixOrderedEigenvalues_eq _ hA]
  constructor
  · exact fun h => h 0
  · intro h i
    exact ((gaussianMatrixCLM_symmetric _ hA).eigenvalues_antitone _ (Fin.zero_le i)).trans_lt h

lemma matrix_operator_toMatrix_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (B : OrthonormalBasis (Fin n) ℝ E) (T : E →L[ℝ] E) (v : EuclideanSpace ℝ (Fin n)) :
    gaussianMatrixCLM (matrixToGaussian (LinearMap.toMatrix B.toBasis B.toBasis T.toLinearMap)) v =
      B.repr (T (B.repr.symm v)) := by
  have h := T.toLinearMap.toMatrix_mulVec_repr B.toBasis B.toBasis (B.repr.symm v)
  apply PiLp.ext
  intro i
  have hi := congrFun h i
  change ((LinearMap.toMatrix B.toBasis B.toBasis T.toLinearMap) *ᵥ
    (fun j => B.repr (B.repr.symm v) j)) i = B.repr (T (B.repr.symm v)) i at hi
  rw [B.repr.apply_symm_apply] at hi
  exact hi

lemma negativeDefinite_toMatrix_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (B : OrthonormalBasis (Fin n) ℝ E) (T : E →L[ℝ] E) :
    NegativeDefinite (gaussianMatrixCLM (matrixToGaussian (LinearMap.toMatrix B.toBasis B.toBasis T.toLinearMap))) ↔
      NegativeDefinite T := by
  have he (v : EuclideanSpace ℝ (Fin n)) :
      inner ℝ v (gaussianMatrixCLM (matrixToGaussian
        (LinearMap.toMatrix B.toBasis B.toBasis T.toLinearMap)) v) =
        inner ℝ (B.repr.symm v) (T (B.repr.symm v)) := by
    rw [matrix_operator_toMatrix_apply]
    exact (B.repr.inner_map_map (B.repr.symm v) (T (B.repr.symm v))).symm.trans
      (by rw [B.repr.apply_symm_apply]) |>.symm
  constructor
  · intro h v hv
    have hh := h (B.repr v) (by intro h0; apply hv; exact B.repr.injective (h0.trans (map_zero _).symm))
    rw [he, B.repr.symm_apply_apply] at hh
    exact hh
  · intro h v hv
    rw [he]
    exact h (B.repr.symm v) (by intro h0; apply hv; simpa using congrArg B.repr h0)

end
end SlowEquilibration.NegativeDefiniteOperators
