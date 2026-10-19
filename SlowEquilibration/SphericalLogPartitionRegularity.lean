-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianInterpolation
public import SlowEquilibration.GaussianSpinLogConvex

/-! The actual spherical coefficient log partition is globally Lipschitz
and convex at every real inverse temperature.  These analytic facts are
independent of the lower-band and slab arguments. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LiteratureSubagLemma22

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem feature_logPartition_eq {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (g : EuclideanDisorder N P) :
    GaussianSpinInterpolation.logPartition (sphereLaw N)
      (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β) g =
        logPartitionEuclidean c β g := by
  unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
    GaussianSpinInterpolation.weight GaussianSpinInterpolation.scaledLinear
    logPartitionEuclidean partition
  simp only [one_mul, _root_.smul_apply, smul_eq_mul, sphereLinear_apply]

private theorem feature_logPartition_lipschitz {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V)
    [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    LipschitzWith K.toNNReal (GaussianSpinInterpolation.logPartition ν L) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).differentiable
      (by norm_num))
  intro w
  rw [(GaussianSpinInterpolation.logPartition_hasFDerivAt ν L hL hK hb w).fderiv]
  apply (NNReal.coe_le_coe).mp
  change ‖GaussianSpinInterpolation.score ν L w‖ ≤ (K.toNNReal : ℝ)
  rw [Real.coe_toNNReal K hK]
  exact GaussianSpinInterpolation.norm_score_le ν L hL hK hb w

/-- The actual log partition has its sharp coefficient Lipschitz constant
at every real temperature. -/
theorem logPartitionEuclidean_lipschitz_all_real {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    LipschitzWith (|β| * Real.sqrt ((N : ℝ) * covariancePolynomial c 1)).toNNReal
      (logPartitionEuclidean (N := N) c β) := by
  have h := feature_logPartition_lipschitz (sphereLaw N)
    (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β)
    (GaussianSpinInterpolation.scaledLinear_measurable _ (sphereLinear_measurable c) β)
    (mul_nonneg (abs_nonneg β) (Real.sqrt_nonneg _))
    (GaussianSpinInterpolation.scaledLinear_bound _ _ (sphereLinear_bound hN c hc) β)
  have heq : GaussianSpinInterpolation.logPartition (sphereLaw N)
      (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β) =
        logPartitionEuclidean (N := N) c β := funext (feature_logPartition_eq c β)
  rwa [heq] at h

/-- The coefficient convexity used in Subag's invocation of the convex
Gaussian small-deviation inequality, for the actual spherical partition. -/
theorem logPartitionEuclidean_convex {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    ConvexOn ℝ univ (logPartitionEuclidean (N := N) c β) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro w _ v _ a b ha hb hab
  have h := (GaussianSpinInterpolation.logPartition_line_convex (sphereLaw N)
    (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β)
    (GaussianSpinInterpolation.scaledLinear_measurable _ (sphereLinear_measurable c) β)
    (mul_nonneg (abs_nonneg β) (Real.sqrt_nonneg _))
    (GaussianSpinInterpolation.scaledLinear_bound _ _ (sphereLinear_bound hN c hc) β)
    w (v - w)).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul,
    add_zero, one_smul, add_sub_cancel, feature_logPartition_eq] at h
  have heq : w + b • (v - w) = a • w + b • v := by
    have he : b = 1 - a := by linarith
    rw [he]
    module
  rwa [heq] at h

end SlowEquilibration.LiteratureSubagLemma22
