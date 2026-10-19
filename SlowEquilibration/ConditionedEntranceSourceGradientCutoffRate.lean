-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientHorizonParameters
public import SlowEquilibration.ConditionedEntranceSourceRateNumeric

/-! One exponential-horizon center-gradient cutoff estimate for all bounded
mixed-source marks and all prescribed physical axes. -/

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

theorem mixedDeletedGradientConstant_le_mark_bound
    (μ : FiniteMixture) (Q B : ℝ) (hB : 0 ≤ B)
    (e k : ℝ) (he : |e| ≤ B) (hk : |k| ≤ B) :
    mixedDeletedGradientConstant μ Q e k ≤
      mixedDeletedGradientConstant μ Q B B := by
  exact sourceGradientConstant_le_mark_bound μ Q B 1 hB (by norm_num)
    (fun _ => 1) contDiff_const e k he hk

theorem source_mixedPosterior_uniform_gradient_cutoff_rate
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    {Q B β α : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hα : 0 < α) :
    ∃ (T : ℝ≥0) (_hT : 0 < T) (γ c : ℝ),
      0 < γ ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1 : ℕ) : ℝ) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
      let H := exponentialGridHorizon γ (n+1)
      (posteriorTrajectoryLaw n μ).real
        {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤
          |mixedPosteriorOriginalGradientScore n μ Q u
            (SphericalMarkedWindows.scorePairEquiv (e,k)) β (H+2*T) t q|} ≤
        Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,hγ,hshort,hγ₁,hγ₂⟩ :=
    mixedPosterior_gradient_exponential_horizon_parameters
      μ hQ B B β hβ hα
  let c₁ := α^2/(8*(Q*μ.xi1 Q))-γ
  let c₂ := (α/(2*centerConstant μ Q))^2/(16*(T:ℝ))-γ
  let a := min 1 (min c₁ c₂)
  let c := a/2
  let K := 2*(2/(T:ℝ)+4)+1
  have ha : 0 < a := lt_min (by norm_num) (lt_min (sub_pos.mpr hγ₁) (sub_pos.mpr hγ₂))
  have hc : 0 < c := half_pos ha
  have hcoef : 0 ≤ 2/(T:ℝ)+4 := by
    have hTr : 0 < (T:ℝ) := by exact_mod_cast hT
    positivity
  refine ⟨T,hT,γ,c,hγ,hc,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    weighted_exponential_eventually_le ha K] with n hn hnK
  intro u hu e k he hk
  dsimp only
  have hmark : mixedDeletedGradientConstant μ Q e k ≤
      mixedDeletedGradientConstant μ Q B B :=
    mixedDeletedGradientConstant_le_mark_bound μ Q B hB e k he hk
  have hshort' : 4*(1+β*mixedDeletedGradientConstant μ Q e k)*(T:ℝ) ≤
      α/(2*centerConstant μ Q) := by
    have hTr : 0 ≤ (T:ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmark hβ
    have hsum : 1+β*mixedDeletedGradientConstant μ Q e k ≤
        1+β*mixedDeletedGradientConstant μ Q B B := by linarith
    have hs := mul_le_mul_of_nonneg_right hsum hTr
    nlinarith [hshort]
  have hTail := mixedPosterior_gradient_exponential_horizon_tail n hn μ hnp
    Q hQ hQ1 u hu e k β hβ hα T hT hshort' hγ.le hγ₁ hγ₂
  let x : ℝ := ((n+1 : ℕ) : ℝ)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hE₁ : Real.exp (-x*c₁) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right
      ((min_le_right (1:ℝ) (min c₁ c₂)).trans (min_le_left c₁ c₂)) hx
    nlinarith
  have hE₂ : Real.exp (-x*c₂) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right
      ((min_le_right (1:ℝ) (min c₁ c₂)).trans (min_le_right c₁ c₂)) hx
    nlinarith
  have hE₃ : Real.exp (-x) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (min c₁ c₂)) hx
    nlinarith
  have hBound :
      (2/(T:ℝ)+4)*(Real.exp (-x*c₁)+Real.exp (-x*c₂))+
        Real.exp (-x) ≤ K*Real.exp (-a*x) := by
    have hh := add_le_add hE₁ hE₂
    have hhh := mul_le_mul_of_nonneg_left hh hcoef
    dsimp only [K]
    nlinarith [hhh,hE₃]
  change (posteriorTrajectoryLaw n μ).real
      {q | ∃ t : ℝ≥0, t ≤ exponentialGridHorizon γ (n+1) ∧ α ≤
        |mixedPosteriorOriginalGradientScore n μ Q u
          (SphericalMarkedWindows.scorePairEquiv (e,k)) β
          (exponentialGridHorizon γ (n+1)+2*T) t q|} ≤
      (2/(T:ℝ)+4)*(Real.exp (-x*c₁)+Real.exp (-x*c₂))+
        Real.exp (-x) at hTail
  exact hTail.trans (hBound.trans hnK)

end SlowEquilibration.SphericalPosteriorGradientIndependence
