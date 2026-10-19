-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinVarianceLowerTail
public import SlowEquilibration.SphericalGaussianInterpolation

/-! The smooth Ehrhard regularity adapter for the actual finite-mixture
spherical log partition, including real inverse temperatures of either sign. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory Set
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem featureLogPartition_eq {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (g : EuclideanDisorder N P) :
    GaussianSpinInterpolation.logPartition (sphereLaw N)
      (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β) g =
        logPartitionEuclidean c β g := by
  unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
    GaussianSpinInterpolation.weight GaussianSpinInterpolation.scaledLinear
    logPartitionEuclidean partition
  simp only [one_mul, _root_.smul_apply, smul_eq_mul, sphereLinear_apply]

/-- Twice continuous differentiability follows from the physical bounded
spin features; no smoothness premise about the partition is required. -/
theorem logPartitionEuclidean_contDiff_two {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    ContDiff ℝ 2 (logPartitionEuclidean (N := N) c β) := by
  have h := GaussianSpinInterpolation.logPartition_contDiff_two (sphereLaw N)
    (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β)
    (GaussianSpinInterpolation.scaledLinear_measurable _ (sphereLinear_measurable c) β)
    (mul_nonneg (abs_nonneg β) (Real.sqrt_nonneg _))
    (GaussianSpinInterpolation.scaledLinear_bound _ _ (sphereLinear_bound hN c hc) β)
  have heq : GaussianSpinInterpolation.logPartition (sphereLaw N)
      (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β) =
        logPartitionEuclidean (N := N) c β := funext (featureLogPartition_eq c β)
  rwa [heq] at h

/-- Smooth Ehrhard concavity for any linear enlargement of actual tensor
disorder. This includes the epigraph transform with one additional coordinate. -/
theorem qheat_logPartitionEuclidean_concave {N P : ℕ} {ι : Type*} [Fintype ι]
    (hN : 1 ≤ N) (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanDisorder N P)
    (b : EuclideanSpace ℝ ι →L[ℝ] ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    ConcaveOn ℝ univ (OAI.GaussianPropeller.EhrhardSmooth.qheat
      (fun x => a * (b x - logPartitionEuclidean c β (A x))) T) := by
  classical
  have h := GaussianSpinInterpolation.qheat_linear_affineLogPartition_concave (sphereLaw N)
    (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β)
    (GaussianSpinInterpolation.scaledLinear_measurable _ (sphereLinear_measurable c) β)
    (mul_nonneg (abs_nonneg β) (Real.sqrt_nonneg _))
    (GaussianSpinInterpolation.scaledLinear_bound _ _ (sphereLinear_bound hN c hc) β)
    A b ha hT
  simpa only [featureLogPartition_eq] using h

/-- The variance-sensitive smooth lower tail for the actual coefficient log
partition, at every real inverse temperature and in every positive dimension. -/
theorem logPartitionEuclidean_gaussian_lower_tail {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) {u : ℝ}
    (hu : 8*Real.sqrt (ProbabilityTheory.variance (logPartitionEuclidean (N := N) c β)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P))+1) ≤ u) :
    (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)).real
      {x | logPartitionEuclidean c β x ≤
        (∫ y, logPartitionEuclidean c β y
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N P))-u} ≤
      Real.exp (-u^2/(64*(ProbabilityTheory.variance (logPartitionEuclidean (N := N) c β)
        (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P))+1))) := by
  classical
  rw [SYK.standardGaussianMeasureOnEuclidean, ProbabilityTheory.map_pi_eq_stdGaussian] at hu ⊢
  have heq : GaussianSpinInterpolation.logPartition (sphereLaw N)
      (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β) =
        logPartitionEuclidean (N := N) c β := funext (featureLogPartition_eq c β)
  have h := GaussianSpinInterpolation.logPartition_gaussian_lower_tail (u := u) (sphereLaw N)
    (GaussianSpinInterpolation.scaledLinear (sphereLinear c) β)
    (GaussianSpinInterpolation.scaledLinear_measurable _ (sphereLinear_measurable c) β)
    (mul_nonneg (abs_nonneg β) (Real.sqrt_nonneg _))
    (GaussianSpinInterpolation.scaledLinear_bound _ _ (sphereLinear_bound hN c hc) β)
  rw [heq] at h
  exact h hu

end SlowEquilibration.SphericalModel
