-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SymmetricSpectralScale
public import SlowEquilibration.GOEScaling

/-! Literal spectral-sum scaling for the manuscript's actual GOE matrix
coordinates and eigenvalues, including every matrix realization. -/
@[expose] public section
namespace SlowEquilibration.SymmetricSpectralScale
noncomputable section
lemma spectral_sum_smul_indexed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E=n)
    (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (a : ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin n,f ((symmetric_smul T hT a).eigenvalues hn i))=
      ∑ i : Fin n,f (a*hT.eigenvalues hn i) := by
  subst n
  exact spectral_sum_smul T hT a f
end
end SlowEquilibration.SymmetricSpectralScale

namespace SlowEquilibration.GOEAsymptotics
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.CriticalSK SymmetricSpectralScale GOEScaling
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

lemma symmetrize_half_smul {m : ℕ} (a : ℝ) (W : GaussianMatrix m) :
    symmetrizeGaussianMatrix (1/2:ℝ) (a • W)=a • symmetrizeGaussianMatrix (1/2:ℝ) W := by
  ext i j
  change (1/2:ℝ)*(a*W i j+a*W j i)=a*((1/2:ℝ)*(W i j+W j i))
  ring

/-- True spectral functional sums scale exactly with the actual matrix;
the proof retains multiplicities through the characteristic polynomial. -/
theorem eigenvalues_spectral_sum_scale (n : ℕ) (a : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (f : ℝ → ℝ) :
    (∑ i,f (eigenvalues n (a • W) i))=∑ i,f (a*eigenvalues n W i) := by
  let M:=symmetrizeGaussianMatrix (1/2:ℝ) (matrixToGaussian W)
  let M':=symmetrizeGaussianMatrix (1/2:ℝ) (matrixToGaussian (a • W))
  let T:=gaussianMatrixCLM M
  have hT:=gaussianMatrixCLM_symmetric M (symmetrize_half_symmetric (matrixToGaussian W))
  have hT':=gaussianMatrixCLM_symmetric M' (symmetrize_half_symmetric (matrixToGaussian (a • W)))
  have hOp : gaussianMatrixCLM M'=a • T := by
    change gaussianMatrixCLM (symmetrizeGaussianMatrix (1/2:ℝ) (matrixToGaussian (a • W)))=a • gaussianMatrixCLM M
    rw [matrixToGaussian_scalar,symmetrize_half_smul]
    exact (gaussianMatrixToCLM (n+1)).map_smul a M
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1 := by simp
  have hEig : hT'.eigenvalues hn=(symmetric_smul T hT a).eigenvalues hn := by
    apply (hT'.eigenvalues_eq_eigenvalues_iff hn (symmetric_smul T hT a) hn).mpr
    exact congrArg (fun A : EuclideanSpace ℝ (Fin (n+1))→L[ℝ]EuclideanSpace ℝ (Fin (n+1))=>A.toLinearMap.charpoly) hOp
  change (∑ i,f (hT'.eigenvalues hn i))=∑ i,f (a*hT.eigenvalues hn i)
  rw [hEig]
  exact spectral_sum_smul_indexed hn T hT a f

end
end SlowEquilibration.GOEAsymptotics
