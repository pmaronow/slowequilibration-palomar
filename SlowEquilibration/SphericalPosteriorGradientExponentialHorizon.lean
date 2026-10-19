-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPosteriorGradientRegularHorizonBound
public import SlowEquilibration.SphericalOverlapExponentialGridRates

/-! A fixed physical mesh and time exponent turn the complete regular
posterior-gradient grid estimate into an explicit exponential-horizon
bound. The mesh condition is exactly the source Brownian short-cell
condition, and each exponent is derived from a physical variance. -/
@[expose] public section
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.SphericalPosteriorMaps
open SlowEquilibration.SphericalOverlapExponential
open SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SphericalAging SphericalAging.HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- The actual mixed posterior center-gradient cutoff error on the original
regular tensor event is exponentially small on a physical exponential
horizon. The two displayed rates are precisely the fixed-time Gaussian
variance and Brownian short-cell rates. -/
theorem mixedPosterior_regular_gradient_exponential_horizon_tail
    (n : ℕ) (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (u : Vector (n+1)) (hu : ‖u‖ ^ 2 = (n+1 : ℕ))
    (e k β : ℝ) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0 < α) (T : ℝ≥0) (hT : 0 < T)
    (hshort : 4*(1+β*mixedDeletedGradientConstant μ Q e k)*(T:ℝ) ≤
      α/(2*centerConstant μ Q))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (_hγ₁ : γ < α^2/(8*(Q*μ.xi1 Q)))
    (_hγ₂ : γ < (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) :
    let H := exponentialGridHorizon γ (n+1)
    (posteriorTrajectoryLaw n μ).real
      {q | unpackDisorder q.1 ∈ regularDisorder ∧
        ∃ t : ℝ≥0, t ≤ H ∧ α ≤
          |mixedPosteriorOriginalGradientScore n μ Q u
            (scorePairEquiv (e,k)) β (H+2*T) t q|} ≤
      (2/(T:ℝ)+4) *
        (Real.exp (-((n+1 : ℕ) : ℝ)*
          (α^2/(8*(Q*μ.xi1 Q))-γ)) +
         Real.exp (-((n+1 : ℕ) : ℝ)*
          ((α/(2*centerConstant μ Q))^2/(16*(T:ℝ))-γ))) := by
  dsimp only
  let H := exponentialGridHorizon γ (n+1)
  let c₁ := α^2/(8*(Q*μ.xi1 Q))
  let c₂ := (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))
  have hreg := mixedPosterior_regular_gradient_horizon_tail
    n μ hnp Q hQ hQ1 u hu e k β hβ hα (H+2*T) H T hT le_rfl hshort
  have h₁ : (gridSize H T : ℝ)*2*
        Real.exp (-((n+1 : ℕ) : ℝ)*α^2/(8*(Q*μ.xi1 Q))) ≤
      (2/(T:ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*(c₁-γ)) := by
    have he := exponentialGridError_bound T hT γ c₁ hγ (n+1)
    convert he using 1
    · dsimp only [exponentialGridError,H,c₁]
      congr 1
      ring_nf
  have h₂ : (gridSize H T : ℝ)*2*
        Real.exp (-((n+1 : ℕ) : ℝ)*(α/(2*centerConstant μ Q))^2/
          (16*(T:ℝ))) ≤
      (2/(T:ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*(c₂-γ)) := by
    have he := exponentialGridError_bound T hT γ c₂ hγ (n+1)
    convert he using 1
    · dsimp only [exponentialGridError,H,c₂]
      congr 1
      ring_nf
  have h := hreg.trans (add_le_add h₁ h₂)
  simpa only [H,c₁,c₂,mul_add] using h

end SlowEquilibration.SphericalPosteriorGradientIndependence
