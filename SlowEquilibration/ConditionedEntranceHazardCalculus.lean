-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceFeynmanKacWeight
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Literal finite-horizon killing integrals, derived by the fundamental
theorem of calculus. These hold pathwise and require no stochastic or
resolvent assumption. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open MeasureTheory Set Filter Topology
set_option maxHeartbeats 500000

def integratedHazard (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t,g s

def hazardSurvival (g : ℝ → ℝ) (t : ℝ) : ℝ := Real.exp (-integratedHazard g t)

lemma hazardSurvival_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (hazardSurvival g) :=
  Real.continuous_exp.comp
    (intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0).neg

lemma hazardSurvival_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (hazardSurvival g) (-g t*hazardSurvival g t) t := by
  unfold hazardSurvival integratedHazard
  have hd := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    (hg.stronglyMeasurableAtFilter volume (𝓝 t)) hg.continuousAt
  simpa only [Pi.neg_apply,mul_comm] using hd.neg.exp

theorem integral_hazard_survival {g : ℝ → ℝ} (hg : Continuous g) (T : ℝ) :
    (∫ t in (0:ℝ)..T,g t*hazardSurvival g t)=1-hazardSurvival g T := by
  have hd (t : ℝ) : HasDerivAt (fun s => 1-hazardSurvival g s)
      (g t*hazardSurvival g t) t := by
    simpa only [neg_mul,neg_neg] using (hazardSurvival_hasDerivAt hg t).const_sub 1
  have hi := hg.mul (hazardSurvival_continuous hg)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hi.intervalIntegrable 0 T)
  simpa only [hazardSurvival,integratedHazard,intervalIntegral.integral_same,
    neg_zero,Real.exp_zero,sub_self,sub_zero] using h

lemma hazardSurvival_nonneg (g : ℝ → ℝ) (T : ℝ) : 0≤hazardSurvival g T :=
  (Real.exp_pos _).le

lemma hazardSurvival_le_one {g : ℝ → ℝ} (hg0 : ∀ t,0≤g t) {T : ℝ} (hT : 0≤T) :
    hazardSurvival g T≤1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hT (fun t _ => hg0 t))

end SlowEquilibration.ConditionedEntrance.FeynmanKac
