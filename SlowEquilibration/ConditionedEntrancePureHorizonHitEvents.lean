-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPosteriorHorizonHitEvents
public import SlowEquilibration.SphericalPosteriorGradientPathGrid
public import SlowEquilibration.SphericalPosteriorGradientFixedTimeTail

/-! Measurability of actual posterior radial and source-gradient hit events
on a finite physical horizon. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
open MeasureTheory SphericalModel SphericalForm SphericalGaussianJet
open SphericalPosteriorMaps SphericalRotationCovariance SphericalOverlapExponential
open SphericalHorizonHitMeasurable
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 600000

def valuePosteriorOverlapScore (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (mark : ℝ)
    (β : ℝ) (S : ℝ≥0) (t : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × SphericalAging.VectorBrownian.Space (n+1))) : ℝ :=
  overlapValue u (valuePosteriorContinuousPath n μ Q u mark β S q
    (clippedPathTime S t))

theorem valuePosteriorOverlapScore_continuous (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (mark : ℝ)
    (β : ℝ) (S : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × SphericalAging.VectorBrownian.Space (n+1))) :
    Continuous (fun t => valuePosteriorOverlapScore n μ Q u mark β S t q) := by
  exact (overlapLinear u).continuous.comp
    ((valuePosteriorContinuousPath n μ Q u mark β S q).continuous.comp
      (clippedPathTime_continuous S))

theorem valuePosteriorOverlapScore_measurable (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (mark : ℝ)
    (β : ℝ) (S : ℝ≥0) (t : ℝ≥0) :
    Measurable (valuePosteriorOverlapScore n μ Q u mark β S t) := by
  unfold valuePosteriorOverlapScore
  have hp : Measurable (fun q =>
      (valuePosteriorContinuousPath n μ Q u mark β S q) (clippedPathTime S t)) := by
    simpa only [Function.comp_def] using
      (ContinuousMap.measurable_eval (clippedPathTime S t)).comp
        (valuePosteriorContinuousPath_measurable n μ Q u mark β S)
  exact (overlapLinear u).continuous.measurable.comp hp

theorem valuePosteriorOriginalGradientScore_continuous
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (S : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × SphericalAging.VectorBrownian.Space (n+1))) :
    Continuous (fun t => valuePosteriorOriginalGradientScore
      n μ Q u mark β S t q) := by
  unfold valuePosteriorOriginalGradientScore clippedGradientScore gradientScore
  exact ((continuous_const.inner
    ((valuePosteriorContinuousPath n μ Q u mark β S q).continuous.comp
      (clippedPathTime_continuous S))).div_const _)

theorem valuePosteriorOriginalGradientScore_measurable
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (S : ℝ≥0)
    (t : ℝ≥0) :
    Measurable (valuePosteriorOriginalGradientScore
      n μ Q u mark β S t) := by
  unfold valuePosteriorOriginalGradientScore clippedGradientScore gradientScore
  have hp : Measurable (fun q =>
      (valuePosteriorContinuousPath n μ Q u mark β S q) (clippedPathTime S t)) := by
    simpa only [Function.comp_def] using
      (ContinuousMap.measurable_eval (clippedPathTime S t)).comp
        (valuePosteriorContinuousPath_measurable n μ Q u mark β S)
  exact (((original_gradient_measurable n μ Q u).comp measurable_fst).inner hp).div_const _

theorem valuePosterior_overlap_horizon_hit_measurable
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (S H : ℝ≥0) (a : ℝ) :
    MeasurableSet {q | ∃ t : ℝ≥0, t ≤ H ∧ a ≤
      |valuePosteriorOverlapScore n μ Q u mark β S t q|} :=
  measurableSet_horizon_hit _
    (valuePosteriorOverlapScore_continuous n μ Q u mark β S)
    (valuePosteriorOverlapScore_measurable n μ Q u mark β S) H a

theorem valuePosterior_gradient_horizon_hit_measurable
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (S H : ℝ≥0) (a : ℝ) :
    MeasurableSet {q | ∃ t : ℝ≥0, t ≤ H ∧ a ≤
      |valuePosteriorOriginalGradientScore n μ Q u mark β S t q|} :=
  measurableSet_horizon_hit _
    (valuePosteriorOriginalGradientScore_continuous n μ Q u mark β S)
    (valuePosteriorOriginalGradientScore_measurable n μ Q u mark β S) H a

end SlowEquilibration.SphericalPosteriorGradientIndependence
