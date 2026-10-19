-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureHorizonHitEvents

/-! The measurable posterior-path hit events agree almost surely, on each
original-disorder and start fibre, with the literal mixed SDE events. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
open MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalGaussianJet SphericalPosteriorMaps SphericalDynamics
open SphericalRotationCovariance SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem valuePosteriorOverlapScore_ae_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (S : ℝ≥0)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t : ℝ≥0, t ≤ S →
      valuePosteriorOverlapScore n μ Q u mark β S t (g,(x,ω)) =
        overlapValue u (mixedProcess μ
          (unpackDisorder (valuePosterior n μ Q u mark g)) β x t ω) := by
  filter_upwards [valuePosteriorContinuousPath_ae_actual n μ Q u mark β S g x]
    with ω hω
  intro t ht
  unfold valuePosteriorOverlapScore
  have he : clippedPathTime S t = ⟨t,⟨zero_le,ht⟩⟩ := by
    apply Subtype.ext
    exact min_eq_left ht
  rw [he]
  exact congrArg (overlapValue u) (hω ⟨t,⟨zero_le,ht⟩⟩)

theorem valuePosteriorOriginalGradientScore_ae_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (S : ℝ≥0)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t : ℝ≥0, t ≤ S →
      valuePosteriorOriginalGradientScore n μ Q u mark β S t (g,(x,ω)) =
        gradientScore
          (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
            (unpackDisorder g)) u)
          (mixedProcess μ
            (unpackDisorder (valuePosterior n μ Q u mark g)) β x t ω) := by
  filter_upwards [valuePosteriorContinuousPath_ae_actual n μ Q u mark β S g x]
    with ω hω
  intro t ht
  unfold valuePosteriorOriginalGradientScore
  rw [clippedGradientScore_of_le _ _ _ ht]
  exact congrArg (gradientScore
    (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder g)) u)) (hω ⟨t,⟨zero_le,ht⟩⟩)

theorem valuePosterior_overlap_horizon_fiber_eq_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (S H : ℝ≥0)
    (hHS : H ≤ S) (a : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n μ Q u mark β S t (g,(x,ω))|} =
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |overlapValue u (mixedProcess μ
        (unpackDisorder (valuePosterior n μ Q u mark g)) β x t ω)|} := by
  apply measureReal_congr
  filter_upwards [valuePosteriorOverlapScore_ae_actual n μ Q u mark β S g x]
    with ω hω
  apply propext
  constructor <;> rintro ⟨t,ht,ha⟩ <;> refine ⟨t,ht,?_⟩
  · rwa [hω t (ht.trans hHS)] at ha
  · rwa [hω t (ht.trans hHS)]

theorem valuePosterior_gradient_horizon_fiber_eq_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ) (S H : ℝ≥0)
    (hHS : H ≤ S) (a : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOriginalGradientScore n μ Q u mark β S t (g,(x,ω))|} =
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |gradientScore
        (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
          (unpackDisorder g)) u)
        (mixedProcess μ
          (unpackDisorder (valuePosterior n μ Q u mark g)) β x t ω)|} := by
  apply measureReal_congr
  filter_upwards [valuePosteriorOriginalGradientScore_ae_actual
    n μ Q u mark β S g x] with ω hω
  apply propext
  constructor <;> rintro ⟨t,ht,ha⟩ <;> refine ⟨t,ht,?_⟩
  · rwa [hω t (ht.trans hHS)] at ha
  · rwa [hω t (ht.trans hHS)]

end SlowEquilibration.SphericalPosteriorGradientIndependence
