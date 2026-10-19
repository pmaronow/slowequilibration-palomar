-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEBorderedDeterminant
public import Mathlib.Analysis.Matrix.Spectrum

/-! # Exact one-border cofactor bound, including singular bulk matrices

Actual orthogonal diagonalization controls the full adjugate quadratic form
by the product of the clipped eigenvalue gaps. The resulting bordered bound
has the manuscript's exact constant C₁=1, with no invertibility or independence.
-/

@[expose] public section

namespace SlowEquilibration.OneBorderDeterminant

noncomputable section
open Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def clippedProduct (rho : ℝ) (lambda : ι → ℝ) : ℝ := ∏ i, max |lambda i| rho

omit [DecidableEq ι] in
lemma clippedProduct_nonneg {rho : ℝ} (hrho : 0 ≤ rho) (lambda : ι → ℝ) :
    0 ≤ clippedProduct rho lambda := Finset.prod_nonneg (fun _ _ => le_trans hrho (le_max_right _ _))

omit [DecidableEq ι] in
lemma absolute_product_le_clipped {rho : ℝ} (_hrho : 0 ≤ rho) (lambda : ι → ℝ) :
    |∏ i, lambda i| ≤ clippedProduct rho lambda := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi => le_max_left _ _)

/-- Every literal adjugate eigenvalue is bounded by the clipped full product,
including when any original eigenvalue vanishes. -/
lemma cofactor_product_bound {rho : ℝ} (hrho : 0 < rho) (lambda : ι → ℝ) (i : ι) :
    |∏ j ∈ Finset.univ.erase i, lambda j| ≤ clippedProduct rho lambda / rho := by
  apply (le_div_iff₀ hrho).mpr
  rw [Finset.abs_prod]
  have hprod : (∏ j ∈ Finset.univ.erase i, |lambda j|) ≤
      ∏ j ∈ Finset.univ.erase i, max |lambda j| rho :=
    Finset.prod_le_prod₀ (fun j hj => abs_nonneg _) (fun j hj => le_max_left _ _)
  calc
    _ ≤ (∏ j ∈ Finset.univ.erase i, max |lambda j| rho) * rho :=
      mul_le_mul_of_nonneg_right hprod hrho.le
    _ ≤ (∏ j ∈ Finset.univ.erase i, max |lambda j| rho) * max |lambda i| rho :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (Finset.prod_nonneg
        (fun j hj => le_trans hrho.le (le_max_right _ _)))
    _ = clippedProduct rho lambda := by
      exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

/-- Unconditional conjugation identity for the actual adjugate. -/
lemma adjugate_unitary_conjugate (U : Matrix.unitaryGroup ι ℝ) (D : Matrix ι ι ℝ) :
    (U * D * star (U : Matrix ι ι ℝ)).adjugate =
      U * D.adjugate * star (U : Matrix ι ι ℝ) := by
  have hUU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U
  have hUU' : star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_star_mul_self U
  have hU : (U : Matrix ι ι ℝ).adjugate = (U : Matrix ι ι ℝ).det • star (U : Matrix ι ι ℝ) := by
    calc
      _ = ((U : Matrix ι ι ℝ).adjugate * U) * star (U : Matrix ι ι ℝ) := by
        rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
      _ = ((U : Matrix ι ι ℝ).det • (1 : Matrix ι ι ℝ)) * star (U : Matrix ι ι ℝ) := by
        rw [Matrix.adjugate_mul]
      _ = _ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hstar : (star (U : Matrix ι ι ℝ)).adjugate =
      (star (U : Matrix ι ι ℝ)).det • (U : Matrix ι ι ℝ) := by
    calc
      _ = ((star (U : Matrix ι ι ℝ)).adjugate * star (U : Matrix ι ι ℝ)) * U := by
        rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
      _ = ((star (U : Matrix ι ι ℝ)).det • (1 : Matrix ι ι ℝ)) * U := by
        rw [Matrix.adjugate_mul]
      _ = _ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hdet : (star (U : Matrix ι ι ℝ)).det * (U : Matrix ι ι ℝ).det = 1 := by
    rw [← Matrix.det_mul, hUU', Matrix.det_one]
  have hdet' : (U : Matrix ι ι ℝ).det * (star (U : Matrix ι ι ℝ)).det = 1 := by
    rw [mul_comm]
    exact hdet
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hU, hstar]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hdet', one_smul, Matrix.mul_assoc]

/-- True adjugate eigenvalue decomposition in the actual orthogonal eigenbasis. -/
lemma hermitian_adjugate_decomposition (T : Matrix ι ι ℝ) (hT : T.IsHermitian) :
    T.adjugate = hT.eigenvectorUnitary *
      Matrix.diagonal (fun i => ∏ j ∈ Finset.univ.erase i, hT.eigenvalues j) *
        star (hT.eigenvectorUnitary : Matrix ι ι ℝ) := by
  have hs : T = hT.eigenvectorUnitary * Matrix.diagonal hT.eigenvalues *
      star (hT.eigenvectorUnitary : Matrix ι ι ℝ) := by
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] using hT.spectral_theorem
  calc
    T.adjugate = (hT.eigenvectorUnitary * Matrix.diagonal hT.eigenvalues *
      star (hT.eigenvectorUnitary : Matrix ι ι ℝ)).adjugate := congrArg Matrix.adjugate hs
    _ = _ := by rw [adjugate_unitary_conjugate, Matrix.adjugate_diagonal]

/-- The orthogonal coordinate change preserves the literal squared row norm. -/
lemma unitary_coordinate_square_sum (U : Matrix.unitaryGroup ι ℝ) (u : ι → ℝ) :
    (∑ i, (star (U : Matrix ι ι ℝ) *ᵥ u) i ^ 2) = ∑ i, u i ^ 2 := by
  have hv : star (U : Matrix ι ι ℝ) *ᵥ u = u ᵥ* (U : Matrix ι ι ℝ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mulVec_transpose]
  simp only [pow_two]
  change (star (U : Matrix ι ι ℝ) *ᵥ u) ⬝ᵥ (star (U : Matrix ι ι ℝ) *ᵥ u) = u ⬝ᵥ u
  have hUU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U
  rw [hv, ← Matrix.dotProduct_mulVec, ← hv, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]

/-- The full adjugate bound in any actual orthogonal diagonalizing coordinates. -/
theorem adjugate_quadratic_unitary (U : Matrix.unitaryGroup ι ℝ) (lambda : ι → ℝ)
    {rho : ℝ} (hrho : 0 < rho) (u : ι → ℝ) :
    |u ⬝ᵥ ((U * Matrix.diagonal lambda * star (U : Matrix ι ι ℝ)).adjugate *ᵥ u)| ≤
      (clippedProduct rho lambda / rho) * (∑ i, u i ^ 2) := by
  let v := star (U : Matrix ι ι ℝ) *ᵥ u
  have hv : u ᵥ* (U : Matrix ι ι ℝ) = v := by
    dsimp only [v]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mulVec_transpose]
  have hquad : u ⬝ᵥ ((U * Matrix.diagonal lambda * star (U : Matrix ι ι ℝ)).adjugate *ᵥ u) =
      ∑ i, v i ^ 2 * (∏ j ∈ Finset.univ.erase i, lambda j) := by
    rw [adjugate_unitary_conjugate, Matrix.adjugate_diagonal, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    change (u ᵥ* (U : Matrix ι ι ℝ)) ⬝ᵥ
      (Matrix.diagonal (fun i => ∏ j ∈ Finset.univ.erase i, lambda j) *ᵥ v) = _
    rw [hv]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hquad]
  calc
    _ ≤ ∑ i, |v i ^ 2 * (∏ j ∈ Finset.univ.erase i, lambda j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, v i ^ 2 * |∏ j ∈ Finset.univ.erase i, lambda j| := by
      simp only [abs_mul, abs_sq]
    _ ≤ ∑ i, v i ^ 2 * (clippedProduct rho lambda / rho) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (cofactor_product_bound hrho _ i) (sq_nonneg _)
    _ = (clippedProduct rho lambda / rho) * ∑ i, u i ^ 2 := by
      rw [← Finset.sum_mul, mul_comm, unitary_coordinate_square_sum]

/-- The actual adjugate quadratic form has the sharp clipped-product bound,
without a nonsingular-matrix hypothesis. -/
theorem adjugate_quadratic_bound (T : Matrix ι ι ℝ) (hT : T.IsHermitian)
    {rho : ℝ} (hrho : 0 < rho) (u : ι → ℝ) :
    |u ⬝ᵥ (T.adjugate *ᵥ u)| ≤
      (clippedProduct rho hT.eigenvalues / rho) * (∑ i, u i ^ 2) := by
  have hs : T = hT.eigenvectorUnitary * Matrix.diagonal hT.eigenvalues *
      star (hT.eigenvectorUnitary : Matrix ι ι ℝ) := by
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] using hT.spectral_theorem
  calc
    _ = |u ⬝ᵥ ((hT.eigenvectorUnitary * Matrix.diagonal hT.eigenvalues *
      star (hT.eigenvectorUnitary : Matrix ι ι ℝ)).adjugate *ᵥ u)| :=
        congrArg (fun A : Matrix ι ι ℝ => |u ⬝ᵥ (A.adjugate *ᵥ u)|) hs
    _ ≤ _ := adjugate_quadratic_unitary hT.eigenvectorUnitary hT.eigenvalues hrho u

/-- The manuscript's exact one-border bound C₁=1, for actual arbitrary
symmetric bulk and arbitrary border values, including all singular bulk cases. -/
theorem one_border_clipped_bound (T : Matrix ι ι ℝ) (hT : T.IsHermitian)
    {rho : ℝ} (hrho : 0 < rho) (a : ℝ) (u : ι → ℝ) :
    |(GOEBorderedDeterminant.border a u u T).det| ≤
      clippedProduct rho hT.eigenvalues * (|a| + (∑ i, u i ^ 2) / rho) := by
  rw [GOEBorderedDeterminant.border_det]
  have hdet : |T.det| ≤ clippedProduct rho hT.eigenvalues := by
    have he : T.det = ∏ i, hT.eigenvalues i := hT.det_eq_prod_eigenvalues
    rw [he]
    exact absolute_product_le_clipped hrho.le _
  have hquad := adjugate_quadratic_bound T hT hrho u
  calc
    _ ≤ |a * T.det| + |u ⬝ᵥ (T.adjugate *ᵥ u)| := abs_sub _ _
    _ ≤ |a| * clippedProduct rho hT.eigenvalues +
        (clippedProduct rho hT.eigenvalues / rho) * ∑ i, u i ^ 2 := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hdet (abs_nonneg _)) hquad
    _ = _ := by ring

lemma unitary_diagonal_det (U : Matrix.unitaryGroup ι ℝ) (lambda : ι → ℝ) :
    (U * Matrix.diagonal lambda * star (U : Matrix ι ι ℝ)).det = ∏ i, lambda i := by
  have hUU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U
  have hd : (U : Matrix ι ι ℝ).det * (star (U : Matrix ι ι ℝ)).det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  calc
    _ = ((U : Matrix ι ι ℝ).det * (star (U : Matrix ι ι ℝ)).det) * (∏ i, lambda i) := by ring
    _ = _ := by rw [hd, one_mul]

theorem one_border_unitary_clipped_bound (U : Matrix.unitaryGroup ι ℝ) (lambda : ι → ℝ)
    {rho : ℝ} (hrho : 0 < rho) (a : ℝ) (u : ι → ℝ) :
    |(GOEBorderedDeterminant.border a u u (U * Matrix.diagonal lambda * star (U : Matrix ι ι ℝ))).det| ≤
      clippedProduct rho lambda * (|a| + (∑ i, u i ^ 2) / rho) := by
  rw [GOEBorderedDeterminant.border_det]
  have hdet : |(U * Matrix.diagonal lambda * star (U : Matrix ι ι ℝ)).det| ≤ clippedProduct rho lambda := by
    rw [unitary_diagonal_det]
    exact absolute_product_le_clipped hrho.le _
  have hquad := adjugate_quadratic_unitary U lambda hrho u
  calc
    _ ≤ |a * (U * Matrix.diagonal lambda * star (U : Matrix ι ι ℝ)).det| +
        |u ⬝ᵥ ((U * Matrix.diagonal lambda * star (U : Matrix ι ι ℝ)).adjugate *ᵥ u)| := abs_sub _ _
    _ ≤ |a| * clippedProduct rho lambda + (clippedProduct rho lambda / rho) * ∑ i, u i ^ 2 := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hdet (abs_nonneg _)) hquad
    _ = _ := by ring

omit [DecidableEq ι] in
/-- The literal clipped logarithmic trace exponentiates to the actual clipped
product, including every original zero eigenvalue. -/
lemma clippedProduct_eq_exp_sum {rho : ℝ} (hrho : 0 < rho) (lambda : ι → ℝ) :
    clippedProduct rho lambda = Real.exp (∑ i, Real.log (max |lambda i| rho)) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (lt_of_lt_of_le hrho (le_max_right _ _))).symm

/-- The source literal shifted bulk has its actual diagonalization in the
same genuine orthogonal eigenbasis of W. -/
lemma shifted_unitary_diagonalization (W : Matrix ι ι ℝ) (hW : W.IsHermitian) (k : ℝ) :
    k • (1 : Matrix ι ι ℝ) - W = hW.eigenvectorUnitary *
      Matrix.diagonal (fun i => k - hW.eigenvalues i) * star (hW.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U := hW.eigenvectorUnitary
  have hWspec : W = U * Matrix.diagonal hW.eigenvalues * star (U : Matrix ι ι ℝ) := by
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] using hW.spectral_theorem
  have hUU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U
  have hd : k • (1 : Matrix ι ι ℝ) - Matrix.diagonal hW.eigenvalues =
      Matrix.diagonal (fun i => k - hW.eigenvalues i) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  calc
    _ = k • ((U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ)) -
        U * Matrix.diagonal hW.eigenvalues * star (U : Matrix ι ι ℝ) := by rw [hUU, ← hWspec]
    _ = U * (k • 1 - Matrix.diagonal hW.eigenvalues) * star (U : Matrix ι ι ℝ) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    _ = _ := by rw [hd]

/-- Exact one-border manuscript estimate with its literal Y_T and C₁=1.
No spectral-gap event, GOE law, invertibility, or border independence is needed. -/
theorem shifted_one_border_bound (W : Matrix ι ι ℝ) (hW : W.IsHermitian)
    (k : ℝ) {rho : ℝ} (hrho : 0 < rho) (a : ℝ) (u : ι → ℝ) :
    |(GOEBorderedDeterminant.border a u u (k • (1 : Matrix ι ι ℝ) - W)).det| ≤
      Real.exp (∑ i, Real.log (max |k - hW.eigenvalues i| rho)) *
        (|a| + (∑ i, u i ^ 2) / rho) := by
  have hs := shifted_unitary_diagonalization W hW k
  calc
    _ = |(GOEBorderedDeterminant.border a u u (hW.eigenvectorUnitary *
      Matrix.diagonal (fun i => k - hW.eigenvalues i) * star (hW.eigenvectorUnitary : Matrix ι ι ℝ))).det| :=
        congrArg (fun T : Matrix ι ι ℝ => |(GOEBorderedDeterminant.border a u u T).det|) hs
    _ ≤ _ := by
      simpa only [clippedProduct_eq_exp_sum hrho] using
        one_border_unitary_clipped_bound hW.eigenvectorUnitary (fun i => k - hW.eigenvalues i) hrho a u

end
end SlowEquilibration.OneBorderDeterminant
