-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEExtremalEdges
public import SlowEquilibration.SpectralCounting

@[expose] public section

/-!
# Actual finite-dimensional spectral trace Lipschitz bound

Squared overlaps between actual orthonormal eigenbases give a doubly stochastic
coupling. Its squared spectral displacement is the literal Frobenius matrix
norm. Weighted Cauchy--Schwarz then controls every scalar Lipschitz spectral
trace, without assuming Hoffman--Wielandt as a premise.
-/

namespace SlowEquilibration.SpectralTraceLipschitz

noncomputable section
set_option backward.isDefEq.respectTransparency false

open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace Topology NNReal

lemma gaussianMatrix_component_inner {k : ℕ} (A : GOEAsymptotics.GaussianMatrix k)
    (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    gaussianMatrixCLM A x i = inner ℝ (A i) x := by
  change (∑ j, A i j * x j) = _
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Frobenius norm is the Hilbert--Schmidt sum in any actual orthonormal basis. -/
lemma sum_norm_matrix_apply_sq {k : ℕ} (A : GOEAsymptotics.GaussianMatrix k)
    (b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) :
    (∑ j, ‖gaussianMatrixCLM A (b j)‖ ^ 2) = ‖A‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Real.norm_eq_abs, sq_abs, gaussianMatrix_component_inner]
  simpa only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using b.sum_sq_inner_left (A i)

lemma eigenbasis_coupling_row {k : ℕ}
    (a b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) (i : Fin k) :
    (∑ j, (inner ℝ (a i) (b j)) ^ 2) = 1 := by
  rw [b.sum_sq_inner_left, a.norm_eq_one, one_pow]

lemma eigenbasis_coupling_column {k : ℕ}
    (a b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) (j : Fin k) :
    (∑ i, (inner ℝ (a i) (b j)) ^ 2) = 1 := by
  rw [a.sum_sq_inner_right, b.norm_eq_one, one_pow]

/-- The actual eigenbasis coupling identity supplies the squared displacement
bound; neither spectral distance nor a matching permutation is assumed. -/
lemma eigenbasis_coupling_cost {k : ℕ} (A B : GOEAsymptotics.GaussianMatrix k)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) :
    let a := (gaussianMatrixCLM_symmetric A hA).eigenvectorBasis (by simp)
    let b := (gaussianMatrixCLM_symmetric B hB).eigenvectorBasis (by simp)
    (∑ i, ∑ j, (inner ℝ (a i) (b j)) ^ 2 *
      (matrixOrderedEigenvalues A i - matrixOrderedEigenvalues B j) ^ 2) = ‖A - B‖ ^ 2 := by
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
  let hSA := gaussianMatrixCLM_symmetric A hA
  let hSB := gaussianMatrixCLM_symmetric B hB
  let a := hSA.eigenvectorBasis hn
  let b := hSB.eigenvectorBasis hn
  change (∑ i, ∑ j, (inner ℝ (a i) (b j)) ^ 2 *
      (matrixOrderedEigenvalues A i - matrixOrderedEigenvalues B j) ^ 2) = _
  have heigA (i : Fin k) : gaussianMatrixCLM A (a i) = matrixOrderedEigenvalues A i • a i := by
    rw [matrixOrderedEigenvalues_eq A hA]
    exact hSA.apply_eigenvectorBasis hn i
  have heigB (j : Fin k) : gaussianMatrixCLM B (b j) = matrixOrderedEigenvalues B j • b j := by
    rw [matrixOrderedEigenvalues_eq B hB]
    exact hSB.apply_eigenvectorBasis hn j
  have hcoord (i j : Fin k) :
      inner ℝ (a i) (gaussianMatrixCLM (A - B) (b j)) =
        (matrixOrderedEigenvalues A i - matrixOrderedEigenvalues B j) * inner ℝ (a i) (b j) := by
    rw [show gaussianMatrixCLM (A - B) = gaussianMatrixCLM A - gaussianMatrixCLM B from
      (gaussianMatrixToCLM k).map_sub A B]
    have hswap : inner ℝ (a i) (gaussianMatrixCLM A (b j)) =
        inner ℝ (gaussianMatrixCLM A (a i)) (b j) := (hSA (a i) (b j)).symm
    rw [_root_.sub_apply, inner_sub_right, hswap, heigA, heigB,
      real_inner_smul_left, real_inner_smul_right]
    ring
  calc
    _ = ∑ j, ∑ i, (inner ℝ (a i) (gaussianMatrixCLM (A - B) (b j))) ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoord]
      ring
    _ = ∑ j, ‖gaussianMatrixCLM (A - B) (b j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact a.sum_sq_inner_right _
    _ = _ := sum_norm_matrix_apply_sq (A - B) b

/-- Every actual scalar Lipschitz spectral trace is Frobenius Lipschitz with
constant `sqrt(dimension) * L`. The coupling cost is proved above. -/
theorem spectral_trace_difference {k : ℕ} (A B : GOEAsymptotics.GaussianMatrix k)
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (f : ℝ → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    |(∑ i, f (matrixOrderedEigenvalues A i)) - (∑ j, f (matrixOrderedEigenvalues B j))| ≤
      Real.sqrt (k : ℝ) * (L : ℝ) * ‖A - B‖ := by
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
  let a := (gaussianMatrixCLM_symmetric A hA).eigenvectorBasis hn
  let b := (gaussianMatrixCLM_symmetric B hB).eigenvectorBasis hn
  let w : Fin k × Fin k → ℝ := fun ij => (inner ℝ (a ij.1) (b ij.2)) ^ 2
  let d : Fin k × Fin k → ℝ := fun ij => f (matrixOrderedEigenvalues A ij.1) - f (matrixOrderedEigenvalues B ij.2)
  have hw : ∀ ij ∈ (Finset.univ : Finset (Fin k × Fin k)), 0 ≤ w ij := fun ij _ => sq_nonneg _
  have hmass : (∑ ij, w ij) = (k : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp only [w, eigenbasis_coupling_row, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hid : (∑ ij, w ij * d ij) =
      (∑ i, f (matrixOrderedEigenvalues A i)) - (∑ j, f (matrixOrderedEigenvalues B j)) := by
    rw [Fintype.sum_prod_type]
    simp only [w, d, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, eigenbasis_coupling_row, one_mul]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, eigenbasis_coupling_column, one_mul]
  have hscalar (ij : Fin k × Fin k) : d ij ^ 2 ≤ (L : ℝ) ^ 2 *
      (matrixOrderedEigenvalues A ij.1 - matrixOrderedEigenvalues B ij.2) ^ 2 := by
    have h := hf.dist_le_mul (matrixOrderedEigenvalues A ij.1) (matrixOrderedEigenvalues B ij.2)
    simp only [Real.dist_eq] at h
    have hs := mul_self_le_mul_self (abs_nonneg _) h
    simpa only [d, ← sq, mul_pow, sq_abs] using hs
  have hcost : (∑ ij, w ij * d ij ^ 2) ≤ (L : ℝ) ^ 2 * ‖A - B‖ ^ 2 := by
    calc
      _ ≤ ∑ ij, w ij * ((L : ℝ) ^ 2 *
          (matrixOrderedEigenvalues A ij.1 - matrixOrderedEigenvalues B ij.2) ^ 2) :=
        Finset.sum_le_sum (fun ij _ => mul_le_mul_of_nonneg_left (hscalar ij) (sq_nonneg _))
      _ = (L : ℝ) ^ 2 * ∑ ij, w ij *
          (matrixOrderedEigenvalues A ij.1 - matrixOrderedEigenvalues B ij.2) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij _
        ring
      _ = _ := by rw [Fintype.sum_prod_type, eigenbasis_coupling_cost A B hA hB]
  have hcs := finite_weighted_cauchy Finset.univ w d hw
  rw [hid, hmass] at hcs
  have hs := hcs.trans (mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg k))
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [← sq, sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  simpa only [mul_assoc] using hs

lemma log_difference_le {rho x y : ℝ} (hrho : 0 < rho) (hx : rho ≤ x) (hy : rho ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / rho := by
  have hxpos := hrho.trans_le hx
  have hypos := hrho.trans_le hy
  have hupper (a b : ℝ) (ha : rho ≤ a) (hb : rho ≤ b) :
      Real.log a - Real.log b ≤ |a - b| / rho := by
    have hap := hrho.trans_le ha
    have hbp := hrho.trans_le hb
    calc
      _ = Real.log (a / b) := (Real.log_div hap.ne' hbp.ne').symm
      _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos hap hbp)
      _ = (a - b) / b := by field_simp
      _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hbp.le
      _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) hrho hb
  apply abs_le.mpr
  have hxy := hupper x y hx hy
  have hyx := hupper y x hy hx
  rw [abs_sub_comm y x] at hyx
  constructor <;> linarith

def clippedLog (k rho x : ℝ) : ℝ := Real.log (max |k - x| rho)

/-- The exact scalar clipped logarithm used in `prop:kr-determinant`. -/
theorem clippedLog_lipschitz (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    LipschitzWith ⟨1 / rho, by positivity⟩ (clippedLog k rho) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |clippedLog k rho x - clippedLog k rho y| ≤ (1 / rho) * |x - y|
  have hmax : |max |k - x| rho - max |k - y| rho| ≤ |x - y| := by
    have hl : LipschitzWith 1 (fun x : ℝ => k - x) := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rw [show k - a - (k - b) = -(a - b) by ring, abs_neg]
    have habs : LipschitzWith 1 (fun x : ℝ => |k - x|) := by
      simpa only [Function.comp_def, Real.norm_eq_abs, one_mul] using
        (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).comp hl
    have h := (habs.max_const rho).dist_le_mul x y
    simpa only [Real.dist_eq, Real.norm_eq_abs, NNReal.coe_one, one_mul] using h
  have hlog := log_difference_le hrho (le_max_right |k - x| rho) (le_max_right |k - y| rho)
  exact hlog.trans (by simpa only [div_eq_mul_inv, mul_comm, one_mul, mul_one] using
    div_le_div_of_nonneg_right hmax hrho.le)

end
end SlowEquilibration.SpectralTraceLipschitz
