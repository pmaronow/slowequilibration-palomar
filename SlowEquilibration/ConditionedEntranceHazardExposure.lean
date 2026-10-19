-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceDiscountedHazard

/-! A true finite post-hit exposure interval gives a quantitative killing
mass. No infinite-killing limit is used, so the source hazard stays bounded. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open MeasureTheory Set Filter
set_option maxHeartbeats 500000

theorem integratedHazard_ge_exposure {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t,0≤g t) {τ δ T : ℝ} (hτ : 0≤τ) (hδ : 0≤δ)
    (hEnd : τ+δ≤T) (hExposure : ∀ t∈Icc τ (τ+δ),1≤g t) :
    δ ≤ integratedHazard g T := by
  have hi : δ≤∫ t in τ..(τ+δ),g t := by
    have hb := intervalIntegral.integral_mono_on (show τ≤τ+δ by linarith)
      (continuous_const.intervalIntegrable (μ := volume) τ (τ+δ))
      (hg.intervalIntegrable (μ := volume) τ (τ+δ)) hExposure
    simpa only [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,mul_one] using hb
  have ho : (∫ t in τ..(τ+δ),g t) ≤ ∫ t in (0:ℝ)..T,g t :=
    intervalIntegral.integral_mono_interval hτ (show τ≤τ+δ by linarith)
      hEnd (Filter.Eventually.of_forall hg0) (hg.intervalIntegrable 0 T)
  exact hi.trans ho

theorem hazardSurvival_le_of_exposure {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t,0≤g t) {τ δ T : ℝ} (hτ : 0≤τ) (hδ : 0≤δ)
    (hEnd : τ+δ≤T) (hExposure : ∀ t∈Icc τ (τ+δ),1≤g t) :
    hazardSurvival g T≤Real.exp (-δ) :=
  Real.exp_le_exp.mpr (neg_le_neg (integratedHazard_ge_exposure hg hg0 hτ hδ hEnd hExposure))

theorem discounted_hazard_ge_exposure {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t,0≤g t) {θ τ δ T : ℝ} (hθ : 0≤θ) (hτ : 0≤τ) (hδ : 0≤δ)
    (hEnd : τ+δ≤T) (hExposure : ∀ t∈Icc τ (τ+δ),1≤g t) :
    Real.exp (-θ*T)*(1-Real.exp (-δ))≤
      ∫ t in (0:ℝ)..T,Real.exp (-θ*t)*g t*hazardSurvival g t := by
  have hT : 0≤T := (by linarith : 0≤τ+δ).trans hEnd
  have hs := hazardSurvival_le_of_exposure hg hg0 hτ hδ hEnd hExposure
  have hb := (discounted_hazard_bounds hg hg0 hθ hT).1
  exact (mul_le_mul_of_nonneg_left (by linarith : 1-Real.exp (-δ)≤1-hazardSurvival g T)
    (Real.exp_pos _).le).trans hb

end SlowEquilibration.ConditionedEntrance.FeynmanKac
