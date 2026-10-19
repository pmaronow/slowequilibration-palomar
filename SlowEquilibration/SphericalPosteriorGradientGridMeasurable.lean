-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientPathGrid

/-! Borel regularity of the actual short-cell error. The quantification over
uncountably many times is an open projection in continuous-path space. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalRotationCovariance SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

theorem clippedGradientScore_continuous_pair {N : ℕ} {S : ℝ≥0} (t : ℝ≥0) :
    Continuous (fun q : Vector N×ContinuousPath N S =>
      clippedGradientScore q.1 q.2 t) := by
  unfold clippedGradientScore gradientScore
  fun_prop

theorem badGrid_clippedGradientScore_isOpen {N : ℕ} {S : ℝ≥0}
    (H T : ℝ≥0) (δ : ℝ) :
    IsOpen {q : Vector N×ContinuousPath N S |
      q ∈ badGrid (fun t q=>clippedGradientScore q.1 q.2 t) H T δ} := by
  have he : {q : Vector N×ContinuousPath N S |
      q ∈ badGrid (fun t q=>clippedGradientScore q.1 q.2 t) H T δ} =
      ⋃ j : Fin (gridSize H T), ⋃ v : Iic T,
        {q | δ < abs (clippedGradientScore q.1 q.2 (gridStart T j.val+v.1)-
          clippedGradientScore q.1 q.2 (gridStart T j.val))} := by
    ext q
    simp only [badGrid,mem_ofPred_eq,mem_iUnion]
    constructor
    · rintro ⟨j,v,hv,hq⟩
      exact ⟨j,⟨v,hv⟩,hq⟩
    · rintro ⟨j,v,hq⟩
      exact ⟨j,v.1,v.2,hq⟩
  rw [he]
  apply isOpen_iUnion
  intro j
  apply isOpen_iUnion
  intro v
  exact isOpen_lt continuous_const
    ((continuous_abs).comp
      ((clippedGradientScore_continuous_pair _).sub
        (clippedGradientScore_continuous_pair _)))

theorem mixedPosterior_badGrid_measurable (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2))
    (β : ℝ) (S H T : ℝ≥0) (δ : ℝ) :
    MeasurableSet (badGrid
      (mixedPosteriorOriginalGradientScore n μ Q u marks β S) H T δ) := by
  let F := fun q : EuclideanDisorder (n+1) μ.maxDegree×
      (Vector (n+1)×VectorBrownian.Space (n+1)) =>
    (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder q.1)) u,
      mixedPosteriorContinuousPath n μ Q u marks β S q)
  have hF : Measurable F :=
    ((original_gradient_measurable n μ Q u).comp measurable_fst).prodMk
      (mixedPosteriorContinuousPath_measurable n μ Q u marks β S)
  have he : badGrid
      (mixedPosteriorOriginalGradientScore n μ Q u marks β S) H T δ =
      F ⁻¹' {q : Vector (n+1)×ContinuousPath (n+1) S |
        q ∈ badGrid (fun t q=>clippedGradientScore q.1 q.2 t) H T δ} := by
    rfl
  rw [he]
  exact (badGrid_clippedGradientScore_isOpen H T δ).measurableSet.preimage hF

theorem valuePosterior_badGrid_measurable (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (mark : ℝ)
    (β : ℝ) (S H T : ℝ≥0) (δ : ℝ) :
    MeasurableSet (badGrid
      (valuePosteriorOriginalGradientScore n μ Q u mark β S) H T δ) := by
  let F := fun q : EuclideanDisorder (n+1) μ.maxDegree×
      (Vector (n+1)×VectorBrownian.Space (n+1)) =>
    (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder q.1)) u,
      valuePosteriorContinuousPath n μ Q u mark β S q)
  have hF : Measurable F :=
    ((original_gradient_measurable n μ Q u).comp measurable_fst).prodMk
      (valuePosteriorContinuousPath_measurable n μ Q u mark β S)
  have he : badGrid
      (valuePosteriorOriginalGradientScore n μ Q u mark β S) H T δ =
      F ⁻¹' {q : Vector (n+1)×ContinuousPath (n+1) S |
        q ∈ badGrid (fun t q=>clippedGradientScore q.1 q.2 t) H T δ} := by
    rfl
  rw [he]
  exact (badGrid_clippedGradientScore_isOpen H T δ).measurableSet.preimage hF

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
