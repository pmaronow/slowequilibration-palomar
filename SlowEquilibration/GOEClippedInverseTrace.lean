-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedInverseOperator
public import SlowEquilibration.OneBorderMoments

/-! Actual operator trace of the continuous clipped inverse is exactly
the literal eigenvalue sum used in the proved physical GOE trace limit. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open GOEAsymptotics OAI.CriticalSK OneBorderMoments GaussianQuadraticVariance
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

lemma euclideanCLM_trace {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin m))
      ((Matrix.toEuclideanCLM (n:=Fin m) (𝕜:=ℝ)) A).toLinearMap=A.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis]
  change (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (Matrix.toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis A)).trace=A.trace
  rw [LinearMap.toMatrix_toLin]

lemma hermitian_cfc_trace {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace=∑ i,f (hA.eigenvalues i) := by
  rw [hA.cfc_eq,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply,Matrix.trace_mul_comm,
    ← Matrix.mul_assoc,Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.prop,
    Matrix.one_mul,Matrix.trace_diagonal]
  rfl

lemma symmetricEntries_eq_gaussian {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) :
    symmetricEntries W=gaussianToMatrix (symmetrizeGaussianMatrix (1/2:ℝ) (matrixToGaussian W)) := by
  ext i j
  rfl

/-- Exact operator trace under the actual symmetric-matrix extension,
retaining all eigenvalue multiplicities and the actual GOE normalization. -/
theorem clippedInverseOperator_trace (n : ℕ) (k ρ : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
      (clippedInverseOperator k ρ W).toLinearMap=(n+1:ℝ)*physicalClippedTrace n k ρ W := by
  let A:=symmetrizeGaussianMatrix (1/2:ℝ) (matrixToGaussian W)
  have hA : ∀ i j,A i j=A j i:=symmetrize_half_symmetric (matrixToGaussian W)
  have hM : (gaussianToMatrix A).IsHermitian := by ext i j;exact hA j i
  change LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
    ((Matrix.toEuclideanCLM (n:=Fin (n+1)) (𝕜:=ℝ))
      (cfc (clippedInverseFunction k ρ) (symmetricEntries W))).toLinearMap=_
  rw [euclideanCLM_trace,symmetricEntries_eq_gaussian,hermitian_cfc_trace _ hM,
    eigenvalue_trace_eq A hA hM (clippedInverseFunction k ρ)]
  have hEig : matrixOrderedEigenvalues A=eigenvalues n W := by
    rw [matrixOrderedEigenvalues_eq A hA]
    rfl
  rw [hEig]
  unfold physicalClippedTrace clippedInverseFunction
  have hn : (n+1:ℝ)≠0:=by positivity
  field_simp

end
end SlowEquilibration.GOEClippedResolvent

