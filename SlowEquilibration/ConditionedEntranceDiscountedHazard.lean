-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceHazardCalculus

/-! Discounted pathwise killing mass controls finite-horizon killing.
The bounds follow from the literal hazard derivative, not a killing-time
or resolvent identification premise. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open MeasureTheory Set
set_option maxHeartbeats 500000

theorem discounted_hazard_bounds {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t,0≤g t) {θ T : ℝ} (hθ : 0≤θ) (hT : 0≤T) :
    Real.exp (-θ*T)*(1-hazardSurvival g T)≤
      (∫ t in (0:ℝ)..T,Real.exp (-θ*t)*g t*hazardSurvival g t) ∧
    (∫ t in (0:ℝ)..T,Real.exp (-θ*t)*g t*hazardSurvival g t)≤1 := by
  let F : ℝ → ℝ := fun t => g t*hazardSurvival g t
  let E : ℝ → ℝ := fun t => Real.exp (-θ*t)
  have hF : Continuous F := hg.mul (hazardSurvival_continuous hg)
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hF0 (t : ℝ) : 0≤F t := mul_nonneg (hg0 t) (hazardSurvival_nonneg g t)
  have hl : (∫ t in (0:ℝ)..T,Real.exp (-θ*T)*F t)≤
      ∫ t in (0:ℝ)..T,E t*F t := by
    apply intervalIntegral.integral_mono_on hT
      ((continuous_const.mul hF).intervalIntegrable 0 T)
      ((hE.mul hF).intervalIntegrable 0 T)
    intro t ht
    apply mul_le_mul_of_nonneg_right _ (hF0 t)
    exact Real.exp_le_exp.mpr (by nlinarith [ht.2])
  have hu : (∫ t in (0:ℝ)..T,E t*F t)≤∫ t in (0:ℝ)..T,F t := by
    apply intervalIntegral.integral_mono_on hT
      ((hE.mul hF).intervalIntegrable 0 T) (hF.intervalIntegrable 0 T)
    intro t ht
    apply mul_le_of_le_one_left (hF0 t)
    apply Real.exp_le_one_iff.mpr
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hθ ht.1)
  rw [intervalIntegral.integral_const_mul,integral_hazard_survival hg] at hl
  rw [integral_hazard_survival hg] at hu
  constructor
  · simpa only [E,F,mul_assoc] using hl
  · have hb : 1-hazardSurvival g T≤1 := by linarith [hazardSurvival_nonneg g T]
    simpa only [E,F,mul_assoc] using hu.trans hb

end SlowEquilibration.ConditionedEntrance.FeynmanKac
