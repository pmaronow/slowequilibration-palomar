-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedInverseOnGap
public import SlowEquilibration.BorderSchurExpectation

/-! # Full bordered determinant on the actual spectral gap

The continuous clipped inverse becomes the ordinary inverse on a genuine
spectral gap. The resulting Schur identity and error are pointwise statements
about the literal full matrix, including the actual row and corner values.
-/

@[expose] public section
namespace SlowEquilibration.BorderClippedSchurIdentity

noncomputable section
open Matrix GOEClippedResolvent
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma symmetricEntries_eq_of_hermitian {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W.IsHermitian) : symmetricEntries W = W := by
  ext i j
  have hs : W j i = W i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using congrFun (congrFun hW i) j
  change (1 / 2 : ℝ) * (W i j + W j i) = W i j
  rw [hs]
  ring

/-- A true spectral gap forces the shifted bulk determinant to be nonzero;
this conclusion is proved from its actual eigenvalue product. -/
lemma shifted_det_ne_zero_of_spectral_gap {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : W.IsHermitian) (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hgap : ∀ z ∈ spectrum ℝ W, ρ ≤ k - z) :
    (k • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det ≠ 0 := by
  rw [OneBorderDeterminant.shifted_unitary_diagonalization W hW k,
    OneBorderDeterminant.unitary_diagonal_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact ne_of_gt (lt_of_lt_of_le hρ (hgap _ (hW.eigenvalues_mem_spectrum_real i)))

lemma euclideanCLM_inverse {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.det ≠ 0) :
    (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)) T⁻¹ =
      ((Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)) T).inverse := by
  let φ := Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)
  have hdet : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  have hunit : IsUnit (φ T) := (Matrix.isUnit_iff_isUnit_det T).mpr hdet |>.map φ.toAlgEquiv.toAlgHom
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  apply hunit.mul_left_cancel
  rw [← map_mul, Matrix.mul_nonsing_inv T hdet, map_one,
    Ring.mul_inverse_cancel (φ T) hunit]

/-- Literal Euclidean row quadratic forms agree with the usual matrix
dot product, with no coordinate norm substitution. -/
lemma inner_euclideanCLM {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m)) :
    inner ℝ u ((Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)) T u) =
      (WithLp.ofLp u) ⬝ᵥ (T *ᵥ WithLp.ofLp u) := by
  rw [← WithLp.toLp_ofLp 2 u, Matrix.toEuclideanCLM_toLp,
    EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial]
  exact dotProduct_comm _ _

/-- Exact full absolute Schur identity for the actual continuous clipped
inverse on the genuine spectral gap. -/
theorem border_abs_eq_clipped_schur_of_spectral_gap {m : ℕ}
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.IsHermitian)
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hgap : ∀ z ∈ spectrum ℝ W, ρ ≤ k - z)
    (a : ℝ) (u : EuclideanSpace ℝ (Fin m)) :
    |(GOEBorderedDeterminant.border a (WithLp.ofLp u) (WithLp.ofLp u)
      (k • (1 : Matrix (Fin m) (Fin m) ℝ) - W)).det| =
      |(k • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det| *
        |a - inner ℝ u (clippedInverseOperator k ρ W u)| := by
  have hdet := shifted_det_ne_zero_of_spectral_gap W hW k hρ hgap
  have hgap' : ∀ z ∈ spectrum ℝ (symmetricEntries W), ρ ≤ k - z := by
    simpa only [symmetricEntries_eq_of_hermitian W hW] using hgap
  have hclip := clippedInverseOperator_eq_inverse_of_spectral_gap k hρ W hgap'
  have hlin : (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ))
      (k • (1 : Matrix (Fin m) (Fin m) ℝ) - W) =
      k • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) -
        (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)) W := by
    simp only [map_sub, map_smul, map_one, ContinuousLinearMap.one_def]
  rw [symmetricEntries_eq_of_hermitian W hW] at hclip
  rw [OneBorderMoments.one_border_schur_det _ hdet, abs_mul,
    hclip, ← hlin, ← euclideanCLM_inverse _ hdet, inner_euclideanCLM]

/-- The actual full determinant error is controlled by the clipped Schur
scalar error, multiplied by the literal raw bulk determinant. -/
theorem border_abs_error_of_spectral_gap {m : ℕ}
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.IsHermitian)
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hgap : ∀ z ∈ spectrum ℝ W, ρ ≤ k - z)
    (a s : ℝ) (u : EuclideanSpace ℝ (Fin m)) :
    abs (|(GOEBorderedDeterminant.border a (WithLp.ofLp u) (WithLp.ofLp u)
      (k • (1 : Matrix (Fin m) (Fin m) ℝ) - W)).det| -
      |s| * |(k • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det|) ≤
        |(k • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det| *
          |a - inner ℝ u (clippedInverseOperator k ρ W u) - s| := by
  rw [border_abs_eq_clipped_schur_of_spectral_gap W hW k hρ hgap a u]
  calc
    _ = |(k • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det| *
        abs (|a - inner ℝ u (clippedInverseOperator k ρ W u)| - |s|) := by
      have he : |(k • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det| *
          |a - inner ℝ u (clippedInverseOperator k ρ W u)| -
          |s| * |(k • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det| =
          |(k • (1 : Matrix (Fin m) (Fin m) ℝ) - W).det| *
          (|a - inner ℝ u (clippedInverseOperator k ρ W u)| - |s|) := by ring
      rw [he, abs_mul, abs_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (abs_abs_sub_abs_le_abs_sub _ _) (abs_nonneg _)

/-- The literal operator norm gap implies the full bordered error bound,
so the actual GOE edge theorem may be used without an assumed inverse law. -/
theorem border_abs_error_of_norm_gap {n : ℕ}
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hW : W.IsHermitian)
    (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hgap : ‖(Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ)) W‖ ≤ k - ρ)
    (a s : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    abs (|(GOEBorderedDeterminant.border a (WithLp.ofLp u) (WithLp.ofLp u)
      (k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - W)).det| -
      |s| * |(k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - W).det|) ≤
        |(k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - W).det| *
          |a - inner ℝ u (clippedInverseOperator k ρ W u) - s| := by
  apply border_abs_error_of_spectral_gap W hW k hρ ?_ a s u
  intro z hz
  have hzN := spectrum.norm_le_norm_of_mem hz
  rw [Matrix.cstar_norm_def, Real.norm_eq_abs] at hzN
  linarith [le_abs_self z]

end
end SlowEquilibration.BorderClippedSchurIdentity
