-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceResolventEnergy
public import Mathlib.Tactic

/-! The gradient-cross square root after the same-witness absorbed
energy and Fisher projection; no energy inequality is imported as an
unproved numerical premise. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem positive_pair_cross_error_of_absorbed_energy
    {lam B J ε H R : ℝ}
    (hlam : 0<lam) (hB : 0≤B) (hJ : 0≤J)
    (hε : 0≤ε) (hH : 0≤H) (hR : 0≤R)
    (hFisher : J≤2*ε*lam*H)
    (hEnergy : B/lam≤2*R+ε+2*ε*H) :
    Real.sqrt (J*B)/lam ≤
      2*Real.sqrt (ε*H*(R+ε*(1+H))) := by
  have hB' : B≤2*lam*(R+ε*(1+H)) := by
    have hh := (div_le_iff₀ hlam).mp hEnergy
    nlinarith
  have h1 : J*B≤(2*ε*lam*H)*B :=
    mul_le_mul_of_nonneg_right hFisher hB
  have h2 : (2*ε*lam*H)*B≤
      (2*ε*lam*H)*(2*lam*(R+ε*(1+H))) :=
    mul_le_mul_of_nonneg_left hB' (by positivity)
  have hlarge : J*B≤4*lam^2*(ε*H*(R+ε*(1+H))) := by
    nlinarith
  have hs1 := Real.sq_sqrt (show 0≤J*B by positivity)
  have hs2 := Real.sq_sqrt
    (show 0≤ε*H*(R+ε*(1+H)) by positivity)
  have hs1n := Real.sqrt_nonneg (J*B)
  have hs2n := Real.sqrt_nonneg (ε*H*(R+ε*(1+H)))
  apply (div_le_iff₀ hlam).2
  have hsq : (Real.sqrt (J*B))^2 ≤
      (2*Real.sqrt (ε*H*(R+ε*(1+H)))*lam)^2 := by
    rw [hs1,mul_pow,mul_pow,hs2]
    nlinarith only [hlarge]
  exact (sq_le_sq₀ hs1n (by positivity)).1 hsq

end SlowEquilibration.ConditionedEntrance
