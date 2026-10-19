-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalHorizonHitMeasurable
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

def clippedPathTime (S : ℝ≥0) (t : ℝ≥0) : PathTime S :=
  ⟨min t S,⟨zero_le,min_le_right _ _⟩⟩

theorem clippedPathTime_continuous (S : ℝ≥0) :
    Continuous (clippedPathTime S) :=
  Continuous.subtype_mk (continuous_id.min continuous_const) _

def mixedPosteriorOverlapScore (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2))
    (β : ℝ) (S : ℝ≥0) (t : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × SphericalAging.VectorBrownian.Space (n+1))) : ℝ :=
  overlapValue u (mixedPosteriorContinuousPath n μ Q u marks β S q
    (clippedPathTime S t))

theorem mixedPosteriorOverlapScore_continuous (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2))
    (β : ℝ) (S : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × SphericalAging.VectorBrownian.Space (n+1))) :
    Continuous (fun t => mixedPosteriorOverlapScore n μ Q u marks β S t q) := by
  exact (overlapLinear u).continuous.comp
    ((mixedPosteriorContinuousPath n μ Q u marks β S q).continuous.comp
      (clippedPathTime_continuous S))

theorem mixedPosteriorOverlapScore_measurable (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2))
    (β : ℝ) (S : ℝ≥0) (t : ℝ≥0) :
    Measurable (mixedPosteriorOverlapScore n μ Q u marks β S t) := by
  unfold mixedPosteriorOverlapScore
  have hp : Measurable (fun q =>
      (mixedPosteriorContinuousPath n μ Q u marks β S q) (clippedPathTime S t)) := by
    simpa only [Function.comp_def] using
      (ContinuousMap.measurable_eval (clippedPathTime S t)).comp
        (mixedPosteriorContinuousPath_measurable n μ Q u marks β S)
  exact (overlapLinear u).continuous.measurable.comp hp

theorem mixedPosteriorOriginalGradientScore_continuous
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (S : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × SphericalAging.VectorBrownian.Space (n+1))) :
    Continuous (fun t => mixedPosteriorOriginalGradientScore
      n μ Q u marks β S t q) := by
  unfold mixedPosteriorOriginalGradientScore clippedGradientScore gradientScore
  exact ((continuous_const.inner
    ((mixedPosteriorContinuousPath n μ Q u marks β S q).continuous.comp
      (clippedPathTime_continuous S))).div_const _)

theorem mixedPosteriorOriginalGradientScore_measurable
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (S : ℝ≥0)
    (t : ℝ≥0) :
    Measurable (mixedPosteriorOriginalGradientScore
      n μ Q u marks β S t) := by
  unfold mixedPosteriorOriginalGradientScore clippedGradientScore gradientScore
  have hp : Measurable (fun q =>
      (mixedPosteriorContinuousPath n μ Q u marks β S q) (clippedPathTime S t)) := by
    simpa only [Function.comp_def] using
      (ContinuousMap.measurable_eval (clippedPathTime S t)).comp
        (mixedPosteriorContinuousPath_measurable n μ Q u marks β S)
  exact (((original_gradient_measurable n μ Q u).comp measurable_fst).inner hp).div_const _

theorem mixedPosterior_overlap_horizon_hit_measurable
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (S H : ℝ≥0) (a : ℝ) :
    MeasurableSet {q | ∃ t : ℝ≥0, t ≤ H ∧ a ≤
      |mixedPosteriorOverlapScore n μ Q u marks β S t q|} :=
  measurableSet_horizon_hit _
    (mixedPosteriorOverlapScore_continuous n μ Q u marks β S)
    (mixedPosteriorOverlapScore_measurable n μ Q u marks β S) H a

theorem mixedPosterior_gradient_horizon_hit_measurable
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (S H : ℝ≥0) (a : ℝ) :
    MeasurableSet {q | ∃ t : ℝ≥0, t ≤ H ∧ a ≤
      |mixedPosteriorOriginalGradientScore n μ Q u marks β S t q|} :=
  measurableSet_horizon_hit _
    (mixedPosteriorOriginalGradientScore_continuous n μ Q u marks β S)
    (mixedPosteriorOriginalGradientScore_measurable n μ Q u marks β S) H a

end SlowEquilibration.SphericalPosteriorGradientIndependence
