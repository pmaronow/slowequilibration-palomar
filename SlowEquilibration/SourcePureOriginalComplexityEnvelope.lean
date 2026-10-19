-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureOnePointContactEnvelope
public import SlowEquilibration.SphericalPureCapSourceScalars

/-! Transport the pure center-field complexity contact to the original
amplitude-one field at Q=1. This recovers the exact `e_p,c_p` tangent used
for source `pc-envelope`, independently of the Gibbs cap calculations. -/

@[expose] public section
namespace SlowEquilibration.SourcePureOriginalComplexityEnvelope
noncomputable section
open Set SphericalMarkedWindows SphericalTAPCertificate
open TwoAtomStationarity PureStationarity
open SphericalPureCapSourceScalars
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_complexity_scale_identity (p : ℕ) (hp : 4 ≤ p)
    {Q : ℝ} (hQ : 0 < Q) (e : ℝ) :
    pureMarkedComplexity p (by omega) 1 (by positivity) Q
      (e*(Real.sqrt Q)^p) =
      pureMarkedComplexity p (by omega) 1 (by positivity) 1 e := by
  let q := Real.sqrt Q
  have hq : 0 < q := Real.sqrt_pos.mpr hQ
  have hq2 : q^2 = Q := Real.sq_sqrt hQ.le
  have hqp : 0 < q^p := pow_pos hq _
  have hqpow : (q^p)^2 = Q^p := by
    calc
      _ = q^(p*2) := (pow_mul q p 2).symm
      _ = q^(2*p) := by congr 1; omega
      _ = (q^2)^p := (pow_mul q 2 p)
      _ = Q^p := by rw [hq2]
  have hpower₂ : Q^2*Q^(p-2) = Q^p := by
    rw [←pow_add]
    congr 1
    omega
  have hpower₁ : Q*Q^(p-1) = Q^p := by
    conv_lhs => lhs; rw [←pow_one Q]
    rw [←pow_add]
    congr 1
    omega
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hp1 : 0 < (p : ℝ)-1 := by
    have h : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    linarith
  have hQp : Q^p ≠ 0 := pow_ne_zero _ hQ.ne'
  have hden : 0 ≤ (p : ℝ)*((p : ℝ)-1) :=
    mul_nonneg (by positivity) hp1.le
  have hden0 : 0 < (p : ℝ)*((p : ℝ)-1) :=
    mul_pos (by positivity) hp1
  have hcov : Q^2*((p : ℝ)*((p : ℝ)-1)*Q^(p-2)) =
      (p : ℝ)*((p : ℝ)-1)*Q^p := by rw [←hpower₂]; ring
  have hfirst : Q*((p : ℝ)*Q^(p-1)) = (p : ℝ)*Q^p := by
    rw [←hpower₁]
    ring
  have hratio :
      (Q^2*((p : ℝ)*((p : ℝ)-1)*Q^(p-2)))/
        (Q*((p : ℝ)*Q^(p-1))) = (p : ℝ)-1 := by
    rw [show Q^2*((p : ℝ)*((p : ℝ)-1)*Q^(p-2)) =
      (p : ℝ)*((p : ℝ)-1)*Q^p by rw [←hpower₂]; ring,
      show Q*((p : ℝ)*Q^(p-1)) = (p : ℝ)*Q^p by rw [←hpower₁]; ring]
    field_simp [hpne,hQp]
  have hsqrt :
      Real.sqrt ((p : ℝ)*((p : ℝ)-1)*Q^p) =
        Real.sqrt ((p : ℝ)*((p : ℝ)-1))*q^p := by
    rw [Real.sqrt_mul hden,←hqpow,Real.sqrt_sq_eq_abs,abs_of_pos hqp]
  unfold pureMarkedComplexity
  simp only [FiniteMixture.pure_xi,one_mul,
    PureStationarity.pure_xi1, PureStationarity.pure_xi2,
    one_pow,mul_one,hcov,hfirst]
  rw [show ((p : ℝ)*((p : ℝ)-1)*Q^p)/((p : ℝ)*Q^p) =
      (p : ℝ)-1 by field_simp [hpne,hQp],hsqrt]
  have hs0 : Real.sqrt ((p : ℝ)*((p : ℝ)-1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hden0).ne'
  have harg : (p : ℝ)*e*q^p /
      (Real.sqrt ((p : ℝ)*((p : ℝ)-1))*q^p) =
      (p : ℝ)*e/Real.sqrt ((p : ℝ)*((p : ℝ)-1)) := by
    field_simp [hs0,hqp.ne']
  have harg' : (p : ℝ)*(e*q^p) /
      (Real.sqrt ((p : ℝ)*((p : ℝ)-1))*q^p) =
      (p : ℝ)*e/Real.sqrt ((p : ℝ)*((p : ℝ)-1)) := by
    convert harg using 1; ring
  have hratio₁ : ((p : ℝ)*((p : ℝ)-1))/(p : ℝ) =
      (p : ℝ)-1 := by field_simp [hpne]
  rw [harg',hratio₁]
  change 1/2+Real.log ((p:ℝ)-1)/2-(e*q^p)^2/(2*Q^p)+
      SemicirclePotential.potential ((p:ℝ)*e/Real.sqrt ((p:ℝ)*((p:ℝ)-1))) =
    1/2+Real.log ((p:ℝ)-1)/2-e^2/2+
      SemicirclePotential.potential ((p:ℝ)*e/Real.sqrt ((p:ℝ)*((p:ℝ)-1)))
  rw [mul_pow,hqpow]
  have hqpn : q^p ≠ 0 := hqp.ne'
  field_simp [hQp,hqpn]

/-- The original pure scalar complexity is globally below its exact
ground-state tangent, including scores inside the GOE bulk. -/
theorem pure_original_complexity_global_linear_loss
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (e : ℝ) :
    pureMarkedComplexity p (by omega) 1 (by positivity) 1 e ≤
      -(pureIntensityConstant p (by omega))*(e-pureEnergyConstant p (by omega)) := by
  let q := Real.sqrt Q
  have hq : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hqp : 0 < q^p := pow_pos hq _
  have hcoords := sourcePure_certificate_scalar_coordinates p hp h
  dsimp only at hcoords
  have hmain := sourcePureMarkedComplexity_global_linear_loss p (by omega)
    1 (by positivity) h (e*q^p)
  rw [hcoords.1] at hmain
  calc
    _ = pureMarkedComplexity p (by omega) 1 (by positivity) Q
        (e*q^p) := (pure_complexity_scale_identity p hp h.overlap_range.1 e).symm
    _ ≤ -(β*x)*(e*q^p-pureEnergyConstant p (by omega)*q^p) := hmain
    _ = _ := by rw [←hcoords.2]; ring

end
end SlowEquilibration.SourcePureOriginalComplexityEnvelope
