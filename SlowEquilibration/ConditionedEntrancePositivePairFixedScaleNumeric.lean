-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePositivePairHorizonNumeric

/-! The source cap hazard remains exponentially small when the reference
rate is at least the reciprocal exponential time horizon. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem positive_pair_cap_rate_absorb
    {N α γ C θ R : ℝ} (hN : 0≤N) (hC : 0≤C)
    (hγ : γ≤α^2/256) (hθ : 0<θ)
    (hrate : Real.exp (-γ*N)≤θ)
    (hR : R≤4*C*Real.exp (-N*α^2/128)/θ) :
    R≤4*C*Real.exp (-N*α^2/256) := by
  have hexp : Real.exp (-N*α^2/128)≤
      Real.exp (-N*α^2/256)*Real.exp (-γ*N) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hN (sub_nonneg.mpr hγ)]
  have hC0 : 0≤4*C := by positivity
  have htarget : 0≤4*C*Real.exp (-N*α^2/256) := by positivity
  have hnum : 4*C*Real.exp (-N*α^2/128)≤
      (4*C*Real.exp (-N*α^2/256))*θ := by
    calc
      _ ≤ 4*C*(Real.exp (-N*α^2/256)*Real.exp (-γ*N)) :=
        mul_le_mul_of_nonneg_left hexp hC0
      _ = (4*C*Real.exp (-N*α^2/256))*Real.exp (-γ*N) := by ring
      _ ≤ (4*C*Real.exp (-N*α^2/256))*θ :=
        mul_le_mul_of_nonneg_left hrate htarget
  have hRm := (le_div_iff₀ hθ).mp hR
  nlinarith

theorem positive_pair_cap_horizon_bound
    {L η ε H R N α γ C θ : ℝ}
    (hN : 0≤N) (hC : 0≤C) (hγ : γ≤α^2/256)
    (hθ : 0<θ) (hrate : Real.exp (-γ*N)≤θ)
    (hε : 0≤ε) (hH : 0≤H) (hR0 : 0≤R)
    (hL : L≤R+10*Real.sqrt ε+
      2*Real.sqrt (ε*H*(R+ε*(1+H)))+4*η)
    (hR : R≤4*C*Real.exp (-N*α^2/128)/θ) :
    L≤4*η+10*Real.sqrt ε+3*ε*(1+H)+
      8*C*Real.exp (-N*α^2/256) := by
  have hs := positive_pair_uniform_transform_simple hε hH hR0 hL
  have hc := positive_pair_cap_rate_absorb hN hC hγ hθ hrate hR
  linarith

end SlowEquilibration.ConditionedEntrance
