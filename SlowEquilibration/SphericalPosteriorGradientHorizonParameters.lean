-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPosteriorGradientUnconditionalHorizon

/-! Positive physical mesh and exponential-horizon rate exist for every
fixed cutoff threshold and bounded source marks. -/
@[expose] public section
noncomputable section
open SlowEquilibration.SphericalModel
open SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem mixedPosterior_gradient_exponential_horizon_parameters
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e k β : ℝ) (hβ : 0 ≤ β) {α : ℝ} (hα : 0 < α) :
    ∃ (T : ℝ≥0) (_hT : 0 < T) (γ : ℝ), 0 < γ ∧
      4*(1+β*mixedDeletedGradientConstant μ Q e k)*(T:ℝ) ≤
        α/(2*centerConstant μ Q) ∧
      γ < α^2/(8*(Q*μ.xi1 Q)) ∧
      γ < (α/(2*centerConstant μ Q))^2/(16*(T:ℝ)) := by
  let K := centerConstant μ Q
  let C := mixedDeletedGradientConstant μ Q e k
  have hK : 0 < K := centerConstant_pos μ Q
  have hC : 0 ≤ C := mixedDeletedGradientConstant_nonneg μ Q e k
  have hb : 0 < 1+β*C := by positivity
  let t : ℝ := α/(16*K*(1+β*C))
  have ht : 0 < t := by dsimp [t]; positivity
  let T : ℝ≥0 := ⟨t,ht.le⟩
  have hT : 0 < T := ht
  have hshort : 4*(1+β*C)*(T:ℝ) ≤ α/(2*K) := by
    change 4*(1+β*C)*t ≤ α/(2*K)
    dsimp only [t]
    have he : 4*(1+β*C)*(α/(16*K*(1+β*C))) = α/(4*K) := by
      field_simp [hK.ne',hb.ne']
      ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity : 0 < 4*K)
      (by positivity : 0 < 2*K)).mpr
    nlinarith [mul_pos hα hK]
  let c₁ := α^2/(8*(Q*μ.xi1 Q))
  let c₂ := (α/(2*K))^2/(16*(T:ℝ))
  have hc₁ : 0 < c₁ := by
    dsimp [c₁]
    have hξ := μ.xi1_pos hQ
    positivity
  have hc₂ : 0 < c₂ := by dsimp [c₂]; positivity
  let γ := min c₁ c₂ / 2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨T,hT,γ,hγ,?_,?_,?_⟩
  · simpa only [K,C] using hshort
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

end SlowEquilibration.SphericalPosteriorGradientIndependence
