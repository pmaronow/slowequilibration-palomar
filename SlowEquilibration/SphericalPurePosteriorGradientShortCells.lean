-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientShortCellTransfer
public import SlowEquilibration.SphericalTAPPosteriorBallRegularity

/-! Brownian short-cell control for the literal value/zero-gradient posterior.
The drift is bounded on the posterior tensor regularity event, and the
original center gradient on the original tensor regularity event. This works
in particular for a proper pure model, where the mixed two-score inverse is
singular. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalDynamics SphericalC1Dynamics SphericalMarkedWindows ConditionedEntrance.PhysicalHitting
open SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalTAPPosteriorBallRegularity
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem actual_valuePosterior_gradient_posteriorRegular_bound
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1)) (e : ℝ)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (K : ℝ)
    (hz : unpackDisorder (valuePosterior n μ Q u e z) ∈
      sourcePosteriorOrderedRegularity K)
    (y : Vector (n+1)) (hy : OnSphere y) :
    ‖mixedGradient μ (unpackDisorder (valuePosterior n μ Q u e z)) y‖ ≤
      posteriorDerivativeConstant (mixtureCoefficients μ) K * Real.sqrt ((n+1:ℕ):ℝ) := by
  have hnorm : ‖y‖ = Real.sqrt ((n+1:ℕ):ℝ) :=
    LandscapeDerivatives.sphere_norm y ((onSphere_iff_norm_sq y).mp hy)
  exact (field_posteriorOrderedRegularity_ball_bounds (by omega)
    (mixtureCoefficients μ) _ hz y hnorm.le).2.1

theorem actual_valuePosterior_original_gradient_regular_bound
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (z : EuclideanDisorder (n+1) μ.maxDegree)
    (hz : unpackDisorder z ∈ regularDisorder) :
    ‖surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder z)) u‖ ≤
      centerConstant μ Q * Real.sqrt ((n+1:ℕ):ℝ) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hnorm : ‖u‖ = Real.sqrt ((n+1:ℕ):ℝ) :=
    LandscapeDerivatives.sphere_norm u hu
  have hg := (field_regularDisorder_ball_bounds (by omega : 1 ≤ n+1)
    c (unpackDisorder z) hz u hnorm.le).2.1
  have hproj := projection_norm_le_onSphere (show n+1 ≠ 0 by omega)
    u (gradient (field c (unpackDisorder z)) u)
    ((onSphere_iff_norm_sq u).mpr hu)
  simpa only [surfaceGradient,tangentProjection_apply,centerConstant] using hproj.trans hg

theorem actual_valuePosterior_gradient_shortCells
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e : ℝ)
    (z : EuclideanDisorder (n+1) μ.maxDegree)
    (hz : unpackDisorder z ∈ regularDisorder) (K : ℝ) (hK : 0 ≤ K)
    (hpost : unpackDisorder (valuePosterior n μ Q u e z) ∈
      sourcePosteriorOrderedRegularity K)
    {β : ℝ} (hβ : 0 ≤ β) (x : Vector (n+1)) (hx : OnSphere x)
    {α : ℝ} (hα : 0 < α) (H T : ℝ≥0) (hT : 0 < T)
    (hshort : 4*(1+β*posteriorDerivativeConstant (mixtureCoefficients μ) K)*(T:ℝ) ≤
      α/(2*centerConstant μ Q)) :
    let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder z)) u
    let J := unpackDisorder (valuePosterior n μ Q u e z)
    (VectorBrownian.law (n+1)).real
      (badGrid (fun t ω => gradientScore G (mixedProcess μ J β x t ω)) H T (α/2)) ≤
      (gridSize H T:ℝ)*2*Real.exp (-((n+1:ℕ):ℝ)*
        (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) := by
  dsimp only
  let J := unpackDisorder (valuePosterior n μ Q u e z)
  have he : badGrid (fun t ω => gradientScore
      (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
        (unpackDisorder z)) u) (mixedProcess μ J β x t ω)) H T (α/2) =ᵐ[VectorBrownian.law (n+1)]
      badGrid (fun t ω => gradientScore
        (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
          (unpackDisorder z)) u)
        (process β (mixedGradient μ J) ((mixedGradient_contDiff μ J).of_le (by simp)) x t ω)) H T (α/2) := by
    filter_upwards [mixedProcess_ae_C1Process (by omega) μ J β x hx] with ω hω
    simp only [badGrid,mem_ofPred_eq,hω]
  rw [measureReal_congr he]
  exact gradientScore_badGrid_probability (by omega) hβ
    (posteriorDerivativeConstant_pos (mixtureCoefficients μ) hK).le
    (centerConstant_pos μ Q) _ _
    (actual_valuePosterior_gradient_posteriorRegular_bound n μ Q u e z K hpost)
    _ x (actual_valuePosterior_original_gradient_regular_bound n μ Q u hu z hz)
    hx hα H T hT hshort

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
