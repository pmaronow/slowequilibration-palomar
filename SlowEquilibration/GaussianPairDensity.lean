-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensityEnergy
public import SlowEquilibration.PairGradientGramLog

/-! Ordinary densities of true pair Gaussian observations, compared with the
product of the two actual isotropic marginal densities at literal zero. -/
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

lemma normalizer_pair :
    GaussianDensity.normalizer (WithLp 2 (F×F))=(GaussianDensity.normalizer F)^2 := by
  unfold GaussianDensity.normalizer
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq,Module.finrank_prod,Nat.cast_add,add_div,
    Real.rpow_add (by positivity),mul_inv_rev]
  ring

lemma log_normalizer_pair :
    Real.log (GaussianDensity.normalizer (WithLp 2 (F×F)))=
      2*Real.log (GaussianDensity.normalizer F) := by
  rw [normalizer_pair,Real.log_pow]
  norm_num

/-- Exact zero-density ratio before bounding the true pair covariance. -/
theorem log_isotropic_pair_density_ratio (A B : E →L[ℝ] F)
    (hA : Surjective A) (hB : Surjective B) (hPair : Surjective (pairHilbert A B))
    {a : ℝ} (_ha : 0 < a)
    (hGA : gram A=a • ContinuousLinearMap.id ℝ F)
    (hGB : gram B=a • ContinuousLinearMap.id ℝ F) :
    Real.log (realObservationDensity (pairHilbert A B) 0 /
      (realObservationDensity A 0*realObservationDensity B 0))=
      -(Real.log (gram (pairHilbert A B)).det-2*(Module.finrank ℝ F:ℝ)*Real.log a)/2 := by
  rw [Real.log_div (realObservationDensity_pos _ hPair _).ne'
    (mul_pos (realObservationDensity_pos A hA _) (realObservationDensity_pos B hB _)).ne',
    Real.log_mul (realObservationDensity_pos A hA _).ne' (realObservationDensity_pos B hB _).ne',
    log_realObservationDensity _ hPair,log_realObservationDensity A hA,log_realObservationDensity B hB,
    log_normalizer_pair,hGA,hGB]
  simp only [map_zero,inner_zero_left,zero_div,sub_zero,ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id,LinearMap.det_smul,LinearMap.det_id,mul_one,Real.log_pow]
  ring

/-- The actual pair pdf at zero has a quadratic cross-block log error. -/
theorem isotropic_pair_density_ratio_bound (A B : E →L[ℝ] F)
    (hA : Surjective A) (hB : Surjective B) (hPair : Surjective (pairHilbert A B))
    {a : ℝ} (ha : 0 < a)
    (hGA : gram A=a • ContinuousLinearMap.id ℝ F)
    (hGB : gram B=a • ContinuousLinearMap.id ℝ F)
    (hcross : ‖A.comp B.adjoint‖ ≤ a/2) :
    |Real.log (realObservationDensity (pairHilbert A B) 0 /
      (realObservationDensity A 0*realObservationDensity B 0))| ≤
        (Module.finrank ℝ F:ℝ)*(‖A.comp B.adjoint‖/a)^2 := by
  rw [log_isotropic_pair_density_ratio A B hA hB hPair ha hGA hGB]
  simp only [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]
  have h:= (isotropic_pair_gram_logdet A B ha hGA hGB hcross).2
  linarith

end
end SlowEquilibration.GaussianRegression
