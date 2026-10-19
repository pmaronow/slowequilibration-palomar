-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPosteriorHorizonHitEvents

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

theorem mixedPosteriorOverlapScore_ae_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (S : ℝ≥0)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t : ℝ≥0, t ≤ S →
      mixedPosteriorOverlapScore n μ Q u marks β S t (g,(x,ω)) =
        overlapValue u (mixedProcess μ
          (unpackDisorder (mixedPosterior n μ Q u marks g)) β x t ω) := by
  filter_upwards [mixedPosteriorContinuousPath_ae_actual n μ Q u marks β S g x]
    with ω hω
  intro t ht
  unfold mixedPosteriorOverlapScore
  have he : clippedPathTime S t = ⟨t,⟨zero_le,ht⟩⟩ := by
    apply Subtype.ext
    exact min_eq_left ht
  rw [he]
  exact congrArg (overlapValue u) (hω ⟨t,⟨zero_le,ht⟩⟩)

theorem mixedPosteriorOriginalGradientScore_ae_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (S : ℝ≥0)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    ∀ᵐ ω ∂VectorBrownian.law (n+1), ∀ t : ℝ≥0, t ≤ S →
      mixedPosteriorOriginalGradientScore n μ Q u marks β S t (g,(x,ω)) =
        gradientScore
          (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
            (unpackDisorder g)) u)
          (mixedProcess μ
            (unpackDisorder (mixedPosterior n μ Q u marks g)) β x t ω) := by
  filter_upwards [mixedPosteriorContinuousPath_ae_actual n μ Q u marks β S g x]
    with ω hω
  intro t ht
  unfold mixedPosteriorOriginalGradientScore
  rw [clippedGradientScore_of_le _ _ _ ht]
  exact congrArg (gradientScore
    (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder g)) u)) (hω ⟨t,⟨zero_le,ht⟩⟩)

theorem mixedPosterior_overlap_horizon_fiber_eq_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (S H : ℝ≥0)
    (hHS : H ≤ S) (a : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOverlapScore n μ Q u marks β S t (g,(x,ω))|} =
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |overlapValue u (mixedProcess μ
        (unpackDisorder (mixedPosterior n μ Q u marks g)) β x t ω)|} := by
  apply measureReal_congr
  filter_upwards [mixedPosteriorOverlapScore_ae_actual n μ Q u marks β S g x]
    with ω hω
  apply propext
  constructor <;> rintro ⟨t,ht,ha⟩ <;> refine ⟨t,ht,?_⟩
  · rwa [hω t (ht.trans hHS)] at ha
  · rwa [hω t (ht.trans hHS)]

theorem mixedPosterior_gradient_horizon_fiber_eq_actual
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (S H : ℝ≥0)
    (hHS : H ≤ S) (a : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) (x : Vector (n+1)) :
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOriginalGradientScore n μ Q u marks β S t (g,(x,ω))|} =
    (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |gradientScore
        (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
          (unpackDisorder g)) u)
        (mixedProcess μ
          (unpackDisorder (mixedPosterior n μ Q u marks g)) β x t ω)|} := by
  apply measureReal_congr
  filter_upwards [mixedPosteriorOriginalGradientScore_ae_actual
    n μ Q u marks β S g x] with ω hω
  apply propext
  constructor <;> rintro ⟨t,ht,ha⟩ <;> refine ⟨t,ht,?_⟩
  · rwa [hω t (ht.trans hHS)] at ha
  · rwa [hω t (ht.trans hHS)]

end SlowEquilibration.SphericalPosteriorGradientIndependence
