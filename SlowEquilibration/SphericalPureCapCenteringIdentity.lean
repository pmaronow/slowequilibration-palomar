-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapDepth

@[expose] public section

/-! The exact source pure cap centering exponent used in §9.19. -/

namespace SlowEquilibration.SphericalPureCapCenteringIdentity
noncomputable section
open SphericalTAPCertificate TwoAtomStationarity
open PureStationarity PureScalarStatic
open SphericalPureCapSourceScalars
set_option autoImplicit false

theorem pureEnergyConstant_pos (p : ℕ) (hp : 3 ≤ p) :
    0 < pureEnergyConstant p hp := by
  have hz : 0 < zParameter p hp := (zParameter_spec p hp).1
  have hpR : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  unfold pureEnergyConstant
  exact div_pos (by linarith) (Real.sqrt_pos.mpr (mul_pos hpR (by linarith)))

theorem pureIntensityConstant_pos (p : ℕ) (hp : 3 ≤ p) :
    0 < pureIntensityConstant p hp := by
  have hz : 0 < zParameter p hp := (zParameter_spec p hp).1
  have hpR : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  unfold pureIntensityConstant
  exact div_pos hz (Real.sqrt_pos.mpr (mul_pos hpR (by linarith)))

/-- Printed identity `β Q^(p/2)/(2c_p)=1/(2x)`, with the actual source
one-step weight and the literal scalar `c_p`. -/
theorem sourcePure_cap_centering_power
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    β*(Real.sqrt Q)^p/(2*pureIntensityConstant p (by omega)) = 1/(2*x) := by
  have hsc := (sourcePure_certificate_scalar_coordinates p hp h).2
  have hq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr h.overlap_range.1
  have hx : 0 < x := h.weight_range.1
  rw [←hsc]
  field_simp [h.beta_pos.ne',hx.ne',pow_ne_zero p hq.ne']

end
end SlowEquilibration.SphericalPureCapCenteringIdentity
