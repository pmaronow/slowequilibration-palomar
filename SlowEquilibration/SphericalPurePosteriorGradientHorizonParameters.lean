-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPurePosteriorGradientUnconditionalHorizon

/-! A dimension-independent positive mesh and time exponent for the actual
value-posterior center-gradient path, including every proper pure model. -/
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

theorem valuePosterior_gradient_exponential_horizon_parameters
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (K β : ℝ) (hK : 0 ≤ K) (hβ : 0 ≤ β) {α : ℝ} (hα : 0 < α) :
    ∃ (T : ℝ≥0) (_hT : 0 < T) (γ : ℝ), 0 < γ ∧
      4*(1+β*posteriorDerivativeConstant (mixtureCoefficients μ) K)*(T:ℝ) ≤
        α/(2*centerConstant μ Q) ∧
      γ < α^2/(8*(Q*μ.xi1 Q)) ∧
      γ < (α/(2*centerConstant μ Q))^2/(16*(T:ℝ)) := by
  let L := centerConstant μ Q
  let C := posteriorDerivativeConstant (mixtureCoefficients μ) K
  have hL : 0 < L := centerConstant_pos μ Q
  have hC : 0 ≤ C := (posteriorDerivativeConstant_pos _ hK).le
  have hb : 0 < 1+β*C := by positivity
  let t : ℝ := α/(16*L*(1+β*C))
  have ht : 0 < t := by dsimp [t]; positivity
  let T : ℝ≥0 := ⟨t,ht.le⟩
  have hT : 0 < T := ht
  have hshort : 4*(1+β*C)*(T:ℝ) ≤ α/(2*L) := by
    change 4*(1+β*C)*t ≤ α/(2*L)
    dsimp only [t]
    have he : 4*(1+β*C)*(α/(16*L*(1+β*C))) = α/(4*L) := by
      field_simp [hL.ne',hb.ne']
      ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity : 0 < 4*L)
      (by positivity : 0 < 2*L)).mpr
    nlinarith [mul_pos hα hL]
  let c₁ := α^2/(8*(Q*μ.xi1 Q))
  let c₂ := (α/(2*L))^2/(16*(T:ℝ))
  have hc₁ : 0 < c₁ := by
    dsimp [c₁]
    have hξ := μ.xi1_pos hQ
    positivity
  have hc₂ : 0 < c₂ := by dsimp [c₂]; positivity
  let γ := min c₁ c₂ / 2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨T,hT,γ,hγ,?_,?_,?_⟩
  · simpa only [L,C] using hshort
  · dsimp only [γ,c₁,c₂]
    have hm : min c₁ c₂ ≤ c₁ := min_le_left _ _
    have hp : 0 < min c₁ c₂ := lt_min hc₁ hc₂
    dsimp only [c₁,c₂] at *
    linarith
  · dsimp only [γ,c₁,c₂]
    have hm : min c₁ c₂ ≤ c₂ := min_le_right _ _
    have hp : 0 < min c₁ c₂ := lt_min hc₁ hc₂
    dsimp only [c₁,c₂] at *
    linarith

/-- One posterior tensor threshold, physical mesh, and positive exponential
horizon rate work for every dimension, center, and bounded value mark. -/
theorem source_valuePosterior_gradient_exponential_horizon_single_witness
    (μ : FiniteMixture) {Q M : ℝ} (hQ : 0 < Q) (hM : 0 ≤ M)
    (β : ℝ) (hβ : 0 ≤ β) {α : ℝ} (hα : 0 < α) :
    ∃ (K : ℝ) (_hK : 0 < K) (T : ℝ≥0) (_hT : 0 < T)
      (γ : ℝ), 0 < γ ∧
      4*(1+β*posteriorDerivativeConstant (mixtureCoefficients μ) K)*(T:ℝ) ≤
        α/(2*centerConstant μ Q) ∧
      γ < α^2/(8*(Q*μ.xi1 Q)) ∧
      γ < (α/(2*centerConstant μ Q))^2/(16*(T:ℝ)) ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (u : Vector (n+1)), ‖u‖^2=(n+1:ℕ) →
      ∀ (e : ℝ), |e| ≤ M →
        let H := exponentialGridHorizon γ (n+1)
        (posteriorTrajectoryLaw n μ).real
          {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤
            |valuePosteriorOriginalGradientScore n μ Q u e β (H+2*T) t q|} ≤
          (2/(T:ℝ)+4) *
            (Real.exp (-((n+1:ℕ):ℝ)*(α^2/(8*(Q*μ.xi1 Q))-γ)) +
             Real.exp (-((n+1:ℕ):ℝ)*
               ((α/(2*centerConstant μ Q))^2/(16*(T:ℝ))-γ))) +
          Real.exp (-((n+1:ℕ):ℝ)) +
          (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2) := by
  obtain ⟨K,hK,hKernel⟩ :=
    source_value_physical_posterior_orderedRegularity μ hQ hM
  obtain ⟨T,hT,γ,hγ,hshort,hγ₁,hγ₂⟩ :=
    valuePosterior_gradient_exponential_horizon_parameters μ hQ K β hK.le hβ hα
  refine ⟨K,hK,T,hT,γ,hγ,hshort,hγ₁,hγ₂,?_⟩
  intro n hn u hu e he
  dsimp only
  exact valuePosterior_gradient_exponential_horizon_tail n hn μ Q hQ u hu e β hβ
    K hK.le (hKernel n u hu e he) hα T hT hshort hγ.le hγ₁ hγ₂

/-- Explicit proper-pure specialization. The conditioned path uses only the
physical value mark and its forced zero tangent-gradient observation. -/
theorem source_pure_valuePosterior_gradient_exponential_horizon_single_witness
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q M : ℝ} (hQ : 0 < Q) (hM : 0 ≤ M)
    (β : ℝ) (hβ : 0 ≤ β) {α : ℝ} (hα : 0 < α) :
    ∃ (K : ℝ) (_hK : 0 < K) (T : ℝ≥0) (_hT : 0 < T)
      (γ : ℝ), 0 < γ ∧
      4*(1+β*posteriorDerivativeConstant
        (mixtureCoefficients (FiniteMixture.pure p hp c hc)) K)*(T:ℝ) ≤
        α/(2*centerConstant (FiniteMixture.pure p hp c hc) Q) ∧
      γ < α^2/(8*(Q*(FiniteMixture.pure p hp c hc).xi1 Q)) ∧
      γ < (α/(2*centerConstant (FiniteMixture.pure p hp c hc) Q))^2/(16*(T:ℝ)) ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (u : Vector (n+1)), ‖u‖^2=(n+1:ℕ) →
      ∀ (e : ℝ), |e| ≤ M →
        let H := exponentialGridHorizon γ (n+1)
        (posteriorTrajectoryLaw n (FiniteMixture.pure p hp c hc)).real
          {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤
            |valuePosteriorOriginalGradientScore n (FiniteMixture.pure p hp c hc)
              Q u e β (H+2*T) t q|} ≤
          (2/(T:ℝ)+4) *
            (Real.exp (-((n+1:ℕ):ℝ)*
              (α^2/(8*(Q*(FiniteMixture.pure p hp c hc).xi1 Q))-γ)) +
             Real.exp (-((n+1:ℕ):ℝ)*
               ((α/(2*centerConstant (FiniteMixture.pure p hp c hc) Q))^2/
                 (16*(T:ℝ))-γ))) +
          Real.exp (-((n+1:ℕ):ℝ)) +
          (Fintype.card (Degree (FiniteMixture.pure p hp c hc).maxDegree):ℝ)*
            Real.exp (-((n+1:ℕ):ℝ)/2) := by
  exact source_valuePosterior_gradient_exponential_horizon_single_witness
    (FiniteMixture.pure p hp c hc) hQ hM β hβ hα

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
