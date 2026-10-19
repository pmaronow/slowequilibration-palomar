-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPurePosteriorGradientHorizonParameters
public import SlowEquilibration.ConditionedEntranceSourceRateNumeric

/-! One exponential-horizon center-gradient cutoff estimate for all bounded
proper-pure source marks and all prescribed physical axes. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence

open Function MeasureTheory ProbabilityTheory Set Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SlowEquilibration.ConditionedEntrance
open SphericalAging HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_valuePosterior_uniform_gradient_cutoff_rate
    (μ : FiniteMixture)
    {Q B β α : ℝ} (hQ : 0 < Q)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hα : 0 < α) :
    ∃ (T : ℝ≥0) (_hT : 0 < T) (γ c : ℝ),
      0 < γ ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1 : ℕ) : ℝ) →
      ∀ (e : ℝ), |e| ≤ B →
      let H := exponentialGridHorizon γ (n+1)
      (posteriorTrajectoryLaw n μ).real
        {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤
          |valuePosteriorOriginalGradientScore n μ Q u
            e β (H+2*T) t q|} ≤
        Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨Kreg,hKreg,T,hT,γ,hγ,hshort,hγ₁,hγ₂,hTail⟩ :=
    source_valuePosterior_gradient_exponential_horizon_single_witness
      μ hQ hB β hβ hα
  let c₁ := α^2/(8*(Q*μ.xi1 Q))-γ
  let c₂ := (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))-γ
  let a := min (1/2 : ℝ) (min c₁ c₂)
  let c := a/2
  let K := 2*(2/(T:ℝ)+4)+1+(Fintype.card (Degree μ.maxDegree) : ℝ)
  have ha : 0 < a := lt_min (by norm_num) (lt_min (sub_pos.mpr hγ₁) (sub_pos.mpr hγ₂))
  have hc : 0 < c := half_pos ha
  have hcoef : 0 ≤ 2/(T:ℝ)+4 := by
    have hTr : 0 < (T:ℝ) := by exact_mod_cast hT
    positivity
  refine ⟨T,hT,γ,c,hγ,hc,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    weighted_exponential_eventually_le ha K] with n hn hnK
  intro u hu e he
  dsimp only
  have hTail := hTail n hn u hu e he
  let x : ℝ := ((n+1 : ℕ) : ℝ)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hE₁ : Real.exp (-x*c₁) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right
      ((min_le_right (1/2:ℝ) (min c₁ c₂)).trans (min_le_left c₁ c₂)) hx
    nlinarith
  have hE₂ : Real.exp (-x*c₂) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right
      ((min_le_right (1/2:ℝ) (min c₁ c₂)).trans (min_le_right c₁ c₂)) hx
    nlinarith
  have hE₃ : Real.exp (-x) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left (1/2:ℝ) (min c₁ c₂)) hx
    nlinarith
  have hE₄ : Real.exp (-x/2) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left (1/2:ℝ) (min c₁ c₂)) hx
    nlinarith
  have hBound :
      (2/(T:ℝ)+4)*(Real.exp (-x*c₁)+Real.exp (-x*c₂))+
        Real.exp (-x)+(Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-x/2) ≤
        K*Real.exp (-a*x) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hE₁ hE₂) hcoef
    have hcard := mul_le_mul_of_nonneg_left hE₄
      (Nat.cast_nonneg (Fintype.card (Degree μ.maxDegree)) : (0:ℝ) ≤ _)
    dsimp only [K]
    nlinarith [hh,hE₃,hcard]
  change (posteriorTrajectoryLaw n μ).real
      {q | ∃ t : ℝ≥0, t ≤ exponentialGridHorizon γ (n+1) ∧ α ≤
        |valuePosteriorOriginalGradientScore n μ Q u e β
          (exponentialGridHorizon γ (n+1)+2*T) t q|} ≤
      (2/(T:ℝ)+4)*(Real.exp (-x*c₁)+Real.exp (-x*c₂))+
        Real.exp (-x)+(Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-x/2) at hTail
  exact hTail.trans (hBound.trans hnK)

end SlowEquilibration.SphericalPosteriorGradientIndependence
