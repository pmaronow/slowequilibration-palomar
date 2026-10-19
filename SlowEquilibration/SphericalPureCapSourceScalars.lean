-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapLatitudeSourceProfile
public import SlowEquilibration.PureVariationalMarks

@[expose] public section

/-! Literal source coordinates for the pure cap saddle of §9.13. -/

namespace SlowEquilibration.SphericalPureCapSourceScalars
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open PureStationarity PureScalarStatic
open SphericalTAPCriticalPureLatitudeProfile
open SphericalPureCapResidualMargin
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The printed pure critical-point intensity slope `c_p`. -/
def pureIntensityConstant (p : ℕ) (hp : 3 ≤ p) : ℝ :=
  zParameter p hp / Real.sqrt ((p : ℝ)*(1+zParameter p hp))

/-- The physical certificate agrees with the explicit source pure ground-energy
and intensity-slope coordinates. -/
theorem sourcePure_certificate_scalar_coordinates
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    markE μ β x Q = pureEnergyConstant p (by omega) * q^p ∧
      β*x*q^p = pureIntensityConstant p (by omega) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let z := zParameter p (by omega : 3 ≤ p)
  let q := Real.sqrt Q
  let k := Real.sqrt ((p:ℝ)*(1+z))
  have hxi : μ.xi = fun r : ℝ => r^p := by
    funext r
    simp only [μ,FiniteMixture.pure_xi,one_mul]
  have hβ := h.superstatic
  rw [hxi] at hβ
  obtain ⟨x',hx',Q',hQ',hlaw',hxformula,hroot,_,_⟩ :=
    canonical_pure_parameters p (by omega : 3 ≤ p) hβ
  have hQ0' : Q' ∈ Ioo (0:ℝ) 1 :=
    ⟨(staticOverlap_mem_Ioo (zParameter_spec p (by omega)).1).1.trans hQ'.1,
      hQ'.2⟩
  have hmine := CSStability.parameters_of_twoAtom μ β h.weight_range
    h.overlap_range h.canonical_law
  have hother := CSStability.parameters_of_twoAtom μ β hx' hQ0' hlaw'
  have hQeq : Q=Q' := hmine.1.symm.trans hother.1
  have hxeq : x=x' := hmine.2.1.symm.trans hother.2.1
  rw [←hQeq, ←hxeq] at hxformula
  rw [←hQeq] at hroot
  obtain ⟨x'',hx'',Q'',hQ'',hlaw'',hE,_,_⟩ :=
    canonical_pure_mark_values p (by omega : 3 ≤ p) hβ
  have hQ0'' : Q'' ∈ Ioo (0:ℝ) 1 :=
    ⟨(staticOverlap_mem_Ioo (zParameter_spec p (by omega)).1).1.trans hQ''.1,
      hQ''.2⟩
  have hother' := CSStability.parameters_of_twoAtom μ β hx'' hQ0'' hlaw''
  have hQeq' : Q=Q'' := hmine.1.symm.trans hother'.1
  have hxeq' : x=x'' := hmine.2.1.symm.trans hother'.2.1
  rw [←hQeq', ←hxeq'] at hE
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq2 : q^2=Q := Real.sq_sqrt h.overlap_range.1.le
  have hrpow : Real.rpow Q ((p:ℝ)/2) = q^p := by
    rw [show q=Q^(1/2:ℝ) by exact Real.sqrt_eq_rpow Q]
    rw [←Real.rpow_natCast, ←Real.rpow_mul h.overlap_range.1.le]
    congr 1
    ring
  have hEnergy : markE μ β x Q = pureEnergyConstant p (by omega) * q^p := by
    simpa only [hrpow] using hE
  have hz : 0 < z := (zParameter_spec p (by omega)).1
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hk0 : 0 < k := Real.sqrt_pos.mpr (mul_pos hp0 (by linarith))
  have hk2 : k^2=(p:ℝ)*(1+z) := Real.sq_sqrt (mul_pos hp0 (by linarith)).le
  have hs : 0 < 1-Q := sub_pos.mpr h.overlap_range.2
  have hβ0 : 0 < β := h.beta_pos
  have hqpow : q^p = q^(p-2)*Q := by
    rw [←hq2,←pow_add]
    congr 1
    omega
  have hqroot : q^(2*(p-2))=Q^(p-2) := by
    rw [pow_mul,hq2]
  let t := β*(1-Q)*q^(p-2)*k
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht2 : t^2=1 := by
    calc
      t^2 = β^2*(1-Q)^2*q^(2*(p-2))*k^2 := by dsimp [t]; ring
      _ = β^2*(p:ℝ)*(1+z)*Q^(p-2)*(1-Q)^2 := by rw [hqroot,hk2]; ring
      _ = 1 := hroot
  have ht : t=1 := by nlinarith
  have hIntensity : β*x*q^p = pureIntensityConstant p (by omega) := by
    unfold pureIntensityConstant
    dsimp [z,k] at *
    rw [hxformula,hqpow]
    field_simp [h.overlap_range.1.ne',hk0.ne']
    nlinarith [ht]
  exact ⟨hEnergy,hIntensity⟩

end
end SlowEquilibration.SphericalPureCapSourceScalars
