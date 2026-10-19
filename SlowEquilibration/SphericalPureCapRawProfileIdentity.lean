-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapCenteringIdentity

@[expose] public section

/-! The raw pure conditional-mean latitude density is exactly the printed
profile density after the source energy change of variables. -/

namespace SlowEquilibration.SphericalPureCapRawProfileIdentity
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalPureCapLatitudeSourceProfile
open SphericalPureLaplaceRegularity
open SphericalPureCapSourceScalars
open PureStationarity
set_option autoImplicit false

/-- The actual certificate's conditional Palm exponent is precisely the
source scalar `Λ(t)=β e_p t^p+log(1−t²)/2+Cβ(t)/2`. -/
theorem sourcePure_cap_printed_profile
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (t : ℝ) :
    sourcePureLatitudeExponent p 1 Q β
      (markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) t =
      β*pureEnergyConstant p (by omega)*t^p+
        Real.log (1-t^2)/2+pureResidualCoefficient p β t/2 := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  have hsc := (sourcePure_certificate_scalar_coordinates p hp h).1
  have hq : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hprofile := sourcePureLatitudeExponent_eq_cap_profile p hp
    h.overlap_range.1 β (markE μ β x Q) t
  rw [hsc] at hprofile
  have hratio : pureEnergyConstant p (by omega)*q^p/q^p =
      pureEnergyConstant p (by omega) := by
    field_simp [pow_ne_zero p hq.ne']
  rw [hratio] at hprofile
  rw [hsc]
  simpa only [mul_assoc] using hprofile

/-- Exact change from the source raw entropy-power integrand to the
Jacobian/profile integrand, pointwise at every physical latitude. -/
theorem sourcePure_cap_raw_profile_identity
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (N : ℕ) (u t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    (1-t^2)^(((N:ℝ)-3)/2) *
      Real.exp (β*((N:ℝ)*pureEnergyConstant p (by omega)+u)*t^p+
        (N:ℝ)*pureResidualCoefficient p β t/2) =
      sourcePureLatitudeJacobian t *
        Real.exp ((N:ℝ)*sourcePureLatitudeExponent p 1 Q β
          (markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) t+
          β*u*t^p) := by
  have hs : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
  have hprofile := sourcePure_cap_printed_profile p hp h t
  unfold sourcePureLatitudeJacobian
  rw [Real.rpow_def_of_pos hs,Real.rpow_def_of_pos hs]
  rw [←Real.exp_add,←Real.exp_add]
  congr 1
  rw [hprofile]
  ring

end
end SlowEquilibration.SphericalPureCapRawProfileIdentity
