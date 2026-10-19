-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedPhysicalPairRatio
public import SlowEquilibration.SourcePurePhysicalPairRatio

/-! Genuine nonnegativity of all actual factors in the physical pair
ratio, including singular density conventions and zero normalizers. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations GaussianRegression
open SphericalSequentialRegression
open GOEPhysicalPotential
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma realObservationDensity_nonnegative {E F:Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A:E→L[ℝ] F) (w:F) : 0 ≤ realObservationDensity A w:=by
  have hNorm:0<GaussianDensity.normalizer F:=GaussianDensity.normalizer_pos
  unfold realObservationDensity
  positivity

lemma physicalMean_nonnegative (n N:ℕ) (b k:ℝ) : 0 ≤ physicalMean n N b k:=by
  exact integral_nonneg (fun _=>abs_nonneg _)

lemma normalized_intrinsic_product_nonnegative {n:ℕ} (μ:FiniteMixture) (Q:ℝ)
    (x y:Vector (n+3)) (k1 k2:ℝ) (P:Measure (Disorder (n+3) μ.maxDegree)) :
    0 ≤ ∫ J,(ConditionedDeterminantMoments.intrinsicDet μ Q x J/physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k1)*
      (ConditionedDeterminantMoments.intrinsicDet μ Q y J/physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k2) ∂P:=by
  apply integral_nonneg
  intro J
  exact mul_nonneg (div_nonneg (abs_nonneg _) (physicalMean_nonnegative _ _ _ _))
    (div_nonneg (abs_nonneg _) (physicalMean_nonnegative _ _ _ _))

lemma sourceMixedPhysicalPairRatio_nonnegative {n:ℕ} (μ:FiniteMixture) (Q:ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 k1 h2 k2:ℝ) :
    0 ≤ sourceMixedPhysicalPairRatio μ Q x y hx hy h1 k1 h2 k2:=by
  unfold sourceMixedPhysicalPairRatio
  dsimp (config := { failIfUnchanged := false }) only
  refine mul_nonneg (mul_nonneg ?_ ?_) (normalized_intrinsic_product_nonnegative μ Q x y k1 k2 _)
  · exact div_nonneg (realObservationDensity_nonnegative _ _)
      (mul_nonneg (realObservationDensity_nonnegative _ _) (realObservationDensity_nonnegative _ _))
  · unfold physicalPairScoreDensity
    exact div_nonneg (mul_nonneg (sq_nonneg _) (realObservationDensity_nonnegative _ _))
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

lemma sourcePurePhysicalPairRatio_nonnegative {n:ℕ} (p:ℕ) (hp:2 ≤ p) (alpha:ℝ) (halpha:0<alpha) (Q:ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 h2:ℝ) :
    0 ≤ sourcePurePhysicalPairRatio p hp alpha halpha Q x y hx hy h1 h2:=by
  unfold sourcePurePhysicalPairRatio
  dsimp (config := { failIfUnchanged := false }) only
  refine mul_nonneg (mul_nonneg ?_ ?_) (normalized_intrinsic_product_nonnegative _ Q x y ((p:ℝ)*h1) ((p:ℝ)*h2) _)
  · exact div_nonneg (realObservationDensity_nonnegative _ _)
      (mul_nonneg (realObservationDensity_nonnegative _ _) (realObservationDensity_nonnegative _ _))
  · unfold physicalPairValueDensity
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (realObservationDensity_nonnegative _ _))
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

end
end SlowEquilibration.PairConditionalDeterminantMoments
