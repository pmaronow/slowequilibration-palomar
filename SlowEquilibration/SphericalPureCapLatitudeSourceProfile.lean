-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapResidualMargin

@[expose] public section

/-! Identification of the profile used in the global cap saddle with the
printed §9.13 normalized pure latitude exponent. -/

namespace SlowEquilibration.SphericalPureCapLatitudeSourceProfile
noncomputable section
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
open PureStationarity
set_option autoImplicit false

/-- The conditional Palm exponent from §12 is precisely the global pure
latitude exponent of §9, with `e_p=E₀/Q^(p/2)` and the literal residual
coefficient `C_β`. This identity holds at every real latitude. -/
theorem sourcePureLatitudeExponent_eq_cap_profile
    (p : ℕ) (hp : 4 ≤ p) {Q : ℝ} (hQ : 0 < Q)
    (β E a : ℝ) :
    sourcePureLatitudeExponent p 1 Q β E a =
      β*(E/(Real.sqrt Q)^p)*a^p+
        Real.log (1-a^2)/2+
        pureResidualCoefficient p β a/2 := by
  have hq : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hcoef := pureResidualCoefficient_eq p (by omega : 2 ≤ p) β a
  unfold sourcePureLatitudeExponent sourcePureLatitudeVariance
  rw [hcoef,div_pow]
  field_simp [pow_ne_zero p hq]

end
end SlowEquilibration.SphericalPureCapLatitudeSourceProfile
