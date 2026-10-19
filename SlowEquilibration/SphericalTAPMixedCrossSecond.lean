-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedLatitudeSmooth

@[expose] public section

/-! Literal first and second latitude derivatives of the mixed two-score
cross vector `b(a)`. These are the inputs to the contact Haa computation. -/

namespace SlowEquilibration.SphericalTAPMixedCrossSecond
noncomputable section
open SphericalTAPMixedBandExponent
set_option autoImplicit false

theorem cross_value_first (μ : FiniteMixture) (Q a : ℝ) :
    deriv (fun t => μ.xi (Real.sqrt Q*t)) a =
      Real.sqrt Q*μ.xi1 (Real.sqrt Q*a) := by
  have h := (μ.hasDerivAt_xi (Real.sqrt Q*a)).comp a
    ((hasDerivAt_id a).const_mul (Real.sqrt Q))
  change HasDerivAt (fun t => μ.xi (Real.sqrt Q*t)) _ a at h
  rw [h.deriv]
  ring

theorem cross_value_second (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (a : ℝ) :
    deriv (deriv (fun t => μ.xi (Real.sqrt Q*t))) a =
      Q*μ.xi2 (Real.sqrt Q*a) := by
  rw [show deriv (fun t => μ.xi (Real.sqrt Q*t)) =
    (fun t => Real.sqrt Q*μ.xi1 (Real.sqrt Q*t)) from
    funext (cross_value_first μ Q)]
  have h := ((μ.hasDerivAt_xi1 (Real.sqrt Q*a)).comp a
    ((hasDerivAt_id a).const_mul (Real.sqrt Q))).const_mul (Real.sqrt Q)
  change HasDerivAt (fun t => Real.sqrt Q*μ.xi1 (Real.sqrt Q*t)) _ a at h
  rw [h.deriv]
  simp only [mul_one]
  ring_nf
  rw [Real.sq_sqrt hQ]
  ring

theorem cross_radial_first (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (a : ℝ) :
    deriv (fun t => Real.sqrt Q*t*μ.xi1 (Real.sqrt Q*t)) a =
      Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)+Q*a*μ.xi2 (Real.sqrt Q*a) := by
  have h := ((hasDerivAt_id a).const_mul (Real.sqrt Q)).mul
    ((μ.hasDerivAt_xi1 (Real.sqrt Q*a)).comp a
      ((hasDerivAt_id a).const_mul (Real.sqrt Q)))
  change HasDerivAt (fun t => Real.sqrt Q*t*μ.xi1 (Real.sqrt Q*t)) _ a at h
  rw [h.deriv]
  simp only [id_eq,Function.comp_apply,mul_one]
  ring_nf
  rw [Real.sq_sqrt hQ]
  ring

theorem cross_radial_second (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q)
    (a : ℝ) :
    deriv (deriv (fun t => Real.sqrt Q*t*μ.xi1 (Real.sqrt Q*t))) a =
      2*Q*μ.xi2 (Real.sqrt Q*a)+
        Q*Real.sqrt Q*a*μ.v1 (Real.sqrt Q*a) := by
  rw [show deriv (fun t => Real.sqrt Q*t*μ.xi1 (Real.sqrt Q*t)) =
    (fun t => Real.sqrt Q*μ.xi1 (Real.sqrt Q*t)+
      Q*t*μ.xi2 (Real.sqrt Q*t)) from
    funext (cross_radial_first μ hQ)]
  have h1 := ((μ.hasDerivAt_xi1 (Real.sqrt Q*a)).comp a
    ((hasDerivAt_id a).const_mul (Real.sqrt Q))).const_mul (Real.sqrt Q)
  have h2 := ((hasDerivAt_id a).const_mul Q).mul
    ((μ.hasDerivAt_xi2 (Real.sqrt Q*a)).comp a
      ((hasDerivAt_id a).const_mul (Real.sqrt Q)))
  have h := h1.add h2
  change HasDerivAt (fun t => Real.sqrt Q*μ.xi1 (Real.sqrt Q*t)+
    Q*t*μ.xi2 (Real.sqrt Q*t)) _ a at h
  rw [h.deriv]
  simp only [id_eq,Function.comp_apply,mul_one]
  ring_nf
  rw [Real.sq_sqrt hQ]
  ring

theorem cross_second_contact (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    deriv (deriv (fun t => μ.xi (Real.sqrt Q*t))) (Real.sqrt Q)=
      Q*μ.xi2 Q ∧
    deriv (deriv (fun t => Real.sqrt Q*t*μ.xi1 (Real.sqrt Q*t)))
      (Real.sqrt Q)=2*Q*μ.xi2 Q+Q^2*μ.v1 Q := by
  constructor
  · rw [cross_value_second μ hQ.le,Real.mul_self_sqrt hQ.le]
  · rw [cross_radial_second μ hQ.le,Real.mul_self_sqrt hQ.le]
    ring_nf
    rw [Real.sq_sqrt hQ.le]
    ring

end
end SlowEquilibration.SphericalTAPMixedCrossSecond
