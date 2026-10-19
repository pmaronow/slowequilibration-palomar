-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPurePosteriorGradientRegularHorizon
public import SlowEquilibration.SphericalOverlapExponentialGridRates

/-! Exponential-horizon version of the actual value-posterior gradient
estimate on the two tensor regularity events. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalOverlapExponential SphericalMarkedWindows
open ConditionedEntrance.PhysicalHitting
open SphericalAging HardSphereDynamics
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalTAPPosteriorBallRegularity
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem valuePosterior_regular_gradient_exponential_horizon_tail
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e β : ℝ) (hβ : 0 ≤ β)
    (K : ℝ) (hK : 0 ≤ K) {α : ℝ} (hα : 0 < α)
    (T : ℝ≥0) (hT : 0 < T)
    (hshort : 4*(1+β*posteriorDerivativeConstant (mixtureCoefficients μ) K)*(T:ℝ) ≤
      α/(2*centerConstant μ Q))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (_hγ₁ : γ < α^2/(8*(Q*μ.xi1 Q)))
    (_hγ₂ : γ < (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) :
    let H := exponentialGridHorizon γ (n+1)
    (posteriorTrajectoryLaw n μ).real
      {q | unpackDisorder q.1 ∈ regularDisorder ∧
        unpackDisorder (valuePosterior n μ Q u e q.1) ∈ sourcePosteriorOrderedRegularity K ∧
        ∃ t : ℝ≥0, t ≤ H ∧ α ≤
          |valuePosteriorOriginalGradientScore n μ Q u e β (H+2*T) t q|} ≤
      (2/(T:ℝ)+4) *
        (Real.exp (-((n+1:ℕ):ℝ)*(α^2/(8*(Q*μ.xi1 Q))-γ)) +
         Real.exp (-((n+1:ℕ):ℝ)*
           ((α/(2*centerConstant μ Q))^2/(16*(T:ℝ))-γ))) := by
  dsimp only
  let H := exponentialGridHorizon γ (n+1)
  let c₁ := α^2/(8*(Q*μ.xi1 Q))
  let c₂ := (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))
  have hreg := valuePosterior_regular_gradient_horizon_tail
    n μ Q hQ u hu e β hβ K hK hα (H+2*T) H T hT le_rfl hshort
  have h₁ : (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) ≤
      (2/(T:ℝ)+4)*Real.exp (-((n+1:ℕ):ℝ)*(c₁-γ)) := by
    have he := exponentialGridError_bound T hT γ c₁ hγ (n+1)
    convert he using 1
    · dsimp only [exponentialGridError,H,c₁]
      congr 1
      ring_nf
  have h₂ : (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*(α/(2*centerConstant μ Q))^2/
          (16*(T:ℝ))) ≤
      (2/(T:ℝ)+4)*Real.exp (-((n+1:ℕ):ℝ)*(c₂-γ)) := by
    have he := exponentialGridError_bound T hT γ c₂ hγ (n+1)
    convert he using 1
    · dsimp only [exponentialGridError,H,c₂]
      congr 1
      ring_nf
  have h := hreg.trans (add_le_add h₁ h₂)
  simpa only [H,c₁,c₂,mul_add] using h

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
