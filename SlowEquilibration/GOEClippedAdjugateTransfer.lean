-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.HermitianAdjugateTrace
public import SlowEquilibration.GOEAdjugateJacobiMean
public import SlowEquilibration.GOEClippedResolventCenteredRate

/-! Actual GOE adjugate trace spectral formulas and pointwise clipping control.
The normalized adjugate trace is globally dominated by the same genuine
clipped determinant exponential and agrees with determinant times inverse
trace on the actual outside-edge event. -/
@[expose] public section
namespace SlowEquilibration.GOEAdjugateJacobiMean
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set Matrix Polynomial
open GOEAsymptotics OAI.CriticalSK GOESignedAbsoluteTransfer GOEClippedDeterminants
open GOEClippedResolvent GOEEdgeConcentration HermitianAdjugateTrace GOEExpectedDeterminant
open scoped NNReal ENNReal Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma shifted_adjugate_trace_eq_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (hW : W.IsHermitian) (k : ℝ) :
    (k • (1 : Matrix ι ι ℝ)-W).adjugate.trace=W.charpoly.derivative.eval k := by
  rw [shifted_adjugate_trace_eq_products W hW k,hW.charpoly_eq,derivative_prod_finset]
  simp only [eval_finsetSum,derivative_X_sub_C,eval_mul,eval_one,one_mul,mul_one,
    eval_prod,eval_sub,eval_X,eval_C,RCLike.ofReal_real_eq_id,id_eq]

lemma symmetric_gaussian_charpoly {m : ℕ} (A : GOEAsymptotics.GaussianMatrix m)
    (hA : ∀ i j,A i j=A j i) :
    (gaussianToMatrix A).charpoly=∏ i,(X-C (matrixOrderedEigenvalues A i)) := by
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin m))=m:=by simp
  have hS:=gaussianMatrixCLM_symmetric A hA
  have hchar : (gaussianMatrixCLM A).toLinearMap.charpoly=(gaussianToMatrix A).charpoly :=
    Matrix.charpoly_toLin (gaussianToMatrix A) (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  have h:=hS.charpoly_eq hn
  rw [hchar] at h
  simpa only [matrixOrderedEigenvalues_eq A hA,RCLike.ofReal_real_eq_id,id_eq] using h

lemma normalizedAdjugateTrace_eq_products (n : ℕ) (k : ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) :
    normalizedAdjugateTrace n k A=
      (∑ i : Fin (n+1),∏ j ∈ Finset.univ.erase i,(k-realizedEigenvalues n A j))/(n+1) := by
  let B:=symmetrizeGaussianMatrix (goeScale n) A
  have hB : (gaussianToMatrix B).IsHermitian := by
    ext i j
    exact symmetrize_symmetric (goeScale n) A j i
  change ((k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-gaussianToMatrix B).adjugate.trace)/(n+1)=_
  rw [shifted_adjugate_trace_eq_derivative _ hB,symmetric_gaussian_charpoly B
    (symmetrize_symmetric (goeScale n) A),derivative_prod_finset]
  simp only [eval_finsetSum,derivative_X_sub_C,eval_mul,eval_one,one_mul,mul_one,
    eval_prod,eval_sub,eval_X,eval_C]
  rfl

/-- Global genuine normalized-adjugate domination, including singular and
inside-edge matrices. The regularization appears only in the upper bound. -/
theorem normalizedAdjugateTrace_abs_le_clipped (n : ℕ) (k : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (A : GOEAsymptotics.GaussianMatrix (n+1)) :
    |normalizedAdjugateTrace n k A| ≤ Real.exp (clippedTrace n k ρ A)/ρ := by
  rw [normalizedAdjugateTrace_eq_products,abs_div,abs_of_pos (by positivity : 0 < (n+1:ℝ))]
  apply (div_le_iff₀ (by positivity : 0 < (n+1:ℝ))).mpr
  have he:=exp_clippedTrace n k hρ A
  have hp (i : Fin (n+1)) :
      |∏ j ∈ Finset.univ.erase i,(k-realizedEigenvalues n A j)| ≤ Real.exp (clippedTrace n k ρ A)/ρ := by
    rw [Finset.abs_prod]
    apply (le_div_iff₀ hρ).mpr
    calc
      _ ≤ (∏ j ∈ Finset.univ.erase i,max |k-realizedEigenvalues n A j| ρ)*
          max |k-realizedEigenvalues n A i| ρ := by
        exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _=>abs_nonneg _)
          (fun _ _=>le_max_left _ _)) (le_max_right _ _) hρ.le
          (Finset.prod_nonneg (fun _ _=>(abs_nonneg _).trans (le_max_left _ _)))
      _=Real.exp (clippedTrace n k ρ A) := by
        rw [he]
        exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _=>hp i)).trans_eq (by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    ring))

/-- On the actual common outside-edge event, the true adjugate equals the
ordinary signed determinant times the literal clipped inverse trace. -/
theorem normalizedAdjugateTrace_eq_det_mul_clipped_of_gap (n : ℕ)
    {g s ρ : ℝ} (hg : 0 < g) (hs : g ≤ s) (hρ : ρ ≤ g/2)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) (hA : A ∉ gapBad n g) :
    normalizedAdjugateTrace n (2+s) A=signedDet n (2+s) A*realizedClippedResolvent n s ρ A := by
  have hrad : realizedRadius n A≤2+g/2:=le_of_not_gt hA
  have hterm (i : Fin (n+1)) : 0 < 2+s-realizedEigenvalues n A i := by
    have hh:=(le_abs_self (realizedEigenvalues n A i)).trans
      ((abs_eigenvalue_le_realizedRadius n A i).trans hrad)
    linarith
  have hmax (i : Fin (n+1)) : max ρ (2+s-realizedEigenvalues n A i)=2+s-realizedEigenvalues n A i := by
    apply max_eq_right
    have hh:=(le_abs_self (realizedEigenvalues n A i)).trans
      ((abs_eigenvalue_le_realizedRadius n A i).trans hrad)
    linarith
  have heig : eigenvalues n (GOEDeterminantMoments.realization n A)=realizedEigenvalues n A := by
    unfold eigenvalues GOEDeterminantMoments.realization realizedEigenvalues
    rw [matrixToGaussian_gaussianToMatrix]
  rw [normalizedAdjugateTrace_eq_products,signedDet_eq_prod]
  unfold realizedClippedResolvent clippedResolvent
  rw [heig]
  simp only [hmax]
  rw [← mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),mul_assoc,mul_inv_cancel₀ (hterm i).ne',mul_one]

end
end SlowEquilibration.GOEAdjugateJacobiMean
