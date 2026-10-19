-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPairDensity
public import SlowEquilibration.PositiveSchurLogDeterminant

/-! Sharp actual pair Gaussian zero-density ratio by the true cross-block
Hilbert–Schmidt norm, without multiplying its rank-one term by dimension. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem isotropic_pair_density_ratio_bound_sharp {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ F) (A B : E →L[ℝ] F)
    (hA : Surjective A) (hB : Surjective B) (hPair : Surjective (pairHilbert A B))
    {a : ℝ} (ha : 0 < a)
    (hGA : gram A=a • ContinuousLinearMap.id ℝ F)
    (hGB : gram B=a • ContinuousLinearMap.id ℝ F)
    (hcross : ‖A.comp B.adjoint‖ ≤ a/2) :
    |Real.log (realObservationDensity (pairHilbert A B) 0 /
      (realObservationDensity A 0*realObservationDensity B 0))| ≤
        (1/a^2)*(∑ i,‖(A.comp B.adjoint) (b i)‖^2) := by
  let T:=A.comp B.adjoint
  let C:=(a⁻¹^2) • T.adjoint.comp T
  have hAdj : B.comp A.adjoint=T.adjoint := by
    dsimp only [T]
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hSchur:=NearIdentityLogDeterminant.positive_schur_det_and_log_bound b T ha hcross
  have hdet : (gram (pairHilbert A B)).det=
      a^(2*Module.finrank ℝ F)*(ContinuousLinearMap.id ℝ F-C).det := by
    rw [isotropic_pair_gram_det A B ha.ne' hGA hGB,hAdj]
  have heq : Real.log (gram (pairHilbert A B)).det-2*(Module.finrank ℝ F:ℝ)*Real.log a=
      Real.log (ContinuousLinearMap.id ℝ F-C).det := by
    rw [hdet,Real.log_mul (pow_pos ha _).ne' hSchur.1.ne',Real.log_pow]
    push_cast
    ring
  rw [log_isotropic_pair_density_ratio A B hA hB hPair ha hGA hGB,heq]
  simp only [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]
  have h:=hSchur.2
  change |Real.log (ContinuousLinearMap.id ℝ F-C).det| ≤ (2/a^2)*(∑ i,‖T (b i)‖^2) at h
  change |Real.log (ContinuousLinearMap.id ℝ F-C).det|/2 ≤ (1/a^2)*(∑ i,‖T (b i)‖^2)
  calc
    _ ≤ ((2/a^2)*(∑ i,‖T (b i)‖^2))/2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by ring

end
end SlowEquilibration.GaussianRegression
