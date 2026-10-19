-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.Matrix.Spectrum

/-! Exact Hermitian adjugate traces as eigenvalue erased products, including
singular matrices and every eigenvalue multiplicity. -/
@[expose] public section
namespace SlowEquilibration.HermitianAdjugateTrace
noncomputable section
open Matrix
open scoped BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma adjugate_trace_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℝ)) (D : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U D).adjugate.trace=D.adjugate.trace := by
  rw [Unitary.conjStarAlgAut_apply,adjugate_mul_distrib,adjugate_mul_distrib,
    trace_mul_comm,Matrix.mul_assoc,← adjugate_mul_distrib,
    Unitary.star_mul_self_of_mem U.prop,adjugate_one,Matrix.mul_one]

/-- Genuine adjugate trace diagonalization, valid also at singular matrices. -/
theorem adjugate_trace_eq_eigenvalue_products {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    A.adjugate.trace=∑ i,∏ j ∈ Finset.univ.erase i,hA.eigenvalues j := by
  conv_lhs=>rw [hA.spectral_theorem]
  rw [adjugate_trace_conjugate,adjugate_diagonal,trace_diagonal]
  simp only [Function.comp_apply,RCLike.ofReal_real_eq_id,id_eq]

/-- The literal shifted matrix has the same spectral adjugate formula,
without making any invertibility assumption. -/
theorem shifted_adjugate_trace_eq_products {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k : ℝ) :
    (k • (1 : Matrix ι ι ℝ)-A).adjugate.trace=
      ∑ i,∏ j ∈ Finset.univ.erase i,(k-hA.eigenvalues j) := by
  have hdiag : k • (1 : Matrix ι ι ℝ)-A=
      Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hA.eigenvectorUnitary
        (diagonal (fun j=>k-hA.eigenvalues j)) := by
    rw [show diagonal (fun j=>k-hA.eigenvalues j)=
      k • (1 : Matrix ι ι ℝ)-diagonal (RCLike.ofReal ∘ hA.eigenvalues) by
        ext i j;by_cases hij : i=j <;> simp [hij]]
    rw [map_sub,map_smul,map_one,← hA.spectral_theorem]
  rw [hdiag,adjugate_trace_conjugate,adjugate_diagonal,trace_diagonal]

end
end SlowEquilibration.HermitianAdjugateTrace
