-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKillingHorizon

/-! Scalar horizon absorption for the positive-pair source transform's
actual ten-square-root forcing constant. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem positive_pair_uniform_transform_simple
    {L η ε H R : ℝ} (hε : 0≤ε) (hH : 0≤H) (hR : 0≤R)
    (hL : L≤R+10*Real.sqrt ε+
      2*Real.sqrt (ε*H*(R+ε*(1+H)))+4*η) :
    L≤4*η+10*Real.sqrt ε+2*R+3*ε*(1+H) := by
  have hs := resolvent_root_error_simplification hε hH hR
  linarith

theorem positive_pair_uniform_transform_exp_horizon
    {L η ε H R : ℝ} (hη : 0≤η) (hε : 0≤ε)
    (hH : 0≤H) (hR : 0≤R)
    (hL : L≤R+10*Real.sqrt ε+
      2*Real.sqrt (ε*H*(R+ε*(1+H)))+4*η) :
    Real.exp 1*L≤28*(η+Real.sqrt ε+ε*(1+H)+R) := by
  have hs := positive_pair_uniform_transform_simple hε hH hR hL
  have he : Real.exp 1≤(14/5 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hse := mul_le_mul_of_nonneg_left hs (Real.exp_pos 1).le
  have htot : 0≤4*η+10*Real.sqrt ε+2*R+3*ε*(1+H) := by positivity
  have hce := mul_le_mul_of_nonneg_right he htot
  have hroot := Real.sqrt_nonneg ε
  have htail : 0≤ε*(1+H) := by positivity
  nlinarith

theorem positive_pair_exposure_horizon
    {P E L c η ε H R : ℝ} (hc : 0<c)
    (hε : 0≤ε) (hH : 0≤H) (hR : 0≤R)
    (hexposure : c*(P-E)≤L)
    (hL : L≤R+10*Real.sqrt ε+
      2*Real.sqrt (ε*H*(R+ε*(1+H)))+4*η) :
    P≤E+(4*η+10*Real.sqrt ε+2*R+3*ε*(1+H))/c := by
  have hs := positive_pair_uniform_transform_simple hε hH hR hL
  have hpc : c*(P-E)≤4*η+10*Real.sqrt ε+2*R+3*ε*(1+H) :=
    hexposure.trans hs
  have hd : P-E≤(4*η+10*Real.sqrt ε+2*R+3*ε*(1+H))/c :=
    (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hpc)
  linarith

end SlowEquilibration.ConditionedEntrance
