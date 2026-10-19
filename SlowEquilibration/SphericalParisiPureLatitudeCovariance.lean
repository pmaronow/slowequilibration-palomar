-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiConditionedLatitudeCovariance

@[expose] public section

/-! The literal value-and-gradient conditional covariance in source 10.12
for a proper pure model. The singular two-score covariance is never inverted.
Its constant and linear coefficients vanish, and its remaining covariance is
the actual second-order finite-mixture Taylor residual. -/

namespace SlowEquilibration.SphericalParisiPureLatitudeCovariance

noncomputable section
open Set SphericalParisiConditionedLatitudeCovariance
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual scalar kernel of the value-and-zero-gradient posterior. -/
def sourceValueTau (μ : FiniteMixture) (Q r t : ℝ) : ℝ :=
  centerCovariance μ Q (r^2+(1-r^2)*t)-(centerCovariance μ Q r)^2/μ.xi Q-
    (1-r^2)*(centerFirst μ Q r)^2/gradientVariance μ Q*t

theorem pure_xi1 (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (r : ℝ) :
    (FiniteMixture.pure p hp c hc).xi1 r = c*(p : ℝ)*r^(p-1) := by
  simp [FiniteMixture.xi1,FiniteMixture.pure,Finsupp.support_single p hc.ne']

theorem pure_centerCovariance (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q r : ℝ) :
    centerCovariance (FiniteMixture.pure p hp c hc) Q r = c*Q^p*r^p := by
  rw [centerCovariance,FiniteMixture.pure_xi,mul_pow]
  ring

theorem pure_centerFirst (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q r : ℝ) :
    centerFirst (FiniteMixture.pure p hp c hc) Q r = c*Q^p*(p : ℝ)*r^(p-1) := by
  rw [centerFirst,pure_xi1,mul_pow]
  have he : Q*Q^(p-1)=Q^p := by
    rw [← pow_succ',Nat.sub_add_cancel (show 1 ≤ p by omega)]
  calc
    _ = c*(Q*Q^(p-1))*(p : ℝ)*r^(p-1) := by ring
    _ = _ := by rw [he]

/-- Equality in the genuine pure value regression Cauchy--Schwarz identity. -/
theorem pure_value_correction (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (r : ℝ) :
    (centerCovariance (FiniteMixture.pure p hp c hc) Q r)^2/
      (FiniteMixture.pure p hp c hc).xi Q =
      centerCovariance (FiniteMixture.pure p hp c hc) Q (r^2) := by
  rw [pure_centerCovariance,FiniteMixture.pure_xi,pure_centerCovariance]
  have hC : c*Q^p ≠ 0 := (mul_pos hc (pow_pos hQ _)).ne'
  calc
    _ = c*Q^p*(r^p)^2 := by apply (div_eq_iff hC).mpr; ring
    _ = _ := by rw [← pow_mul,← pow_mul,Nat.mul_comm p 2]

/-- Equality in the genuine pure gradient regression Cauchy--Schwarz identity. -/
theorem pure_gradient_correction (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (r : ℝ) :
    (centerFirst (FiniteMixture.pure p hp c hc) Q r)^2/
      gradientVariance (FiniteMixture.pure p hp c hc) Q =
      centerFirst (FiniteMixture.pure p hp c hc) Q (r^2) := by
  rw [gradientVariance,pure_centerFirst,pure_centerFirst,pure_centerFirst]
  simp only [one_pow,mul_one]
  have hA : c*Q^p*(p : ℝ) ≠ 0 :=
    (mul_pos (mul_pos hc (pow_pos hQ _)) (by exact_mod_cast (show 0 < p by omega))).ne'
  calc
    _ = c*Q^p*(p : ℝ)*(r^(p-1))^2 := by apply (div_eq_iff hA).mpr; ring
    _ = _ := by rw [← pow_mul,← pow_mul,Nat.mul_comm (p-1) 2]

/-- The proper-pure source kernel has precisely the true Taylor residual
covariance; no constant or linear Gaussian field remains. -/
theorem pure_valueTau_eq_residual_xi (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q r : ℝ} (hQ : 0 < Q) (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    sourceValueTau (FiniteMixture.pure p hp c hc) Q r t =
      ((FiniteMixture.pure p hp c hc).taylorResidual
        (mul_pos hQ (sq_pos_of_pos hr.1))
        (mul_pos hQ (show 0 < 1-r^2 by nlinarith [hr.1,hr.2]))).xi t := by
  rw [FiniteMixture.taylorResidual_xi]
  unfold sourceValueTau
  rw [pure_value_correction p hp c hc hQ,mul_div_assoc,
    pure_gradient_correction p hp c hc hQ]
  unfold centerCovariance centerFirst
  rw [show Q*(r^2+(1-r^2)*t)=Q*r^2+Q*(1-r^2)*t by ring]
  ring

theorem pure_sourceLinearCoefficient_zero (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (r : ℝ) :
    sourceLinearCoefficient (FiniteMixture.pure p hp c hc) Q r = 0 := by
  unfold sourceLinearCoefficient
  rw [pure_gradient_correction p hp c hc hQ,sub_self,mul_zero]

/-- The exact pure formula displayed in source 10.12, valid for either
parity and obtained from the actual value-and-gradient regression kernel. -/
theorem pure_valueTau_eq_monomial (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (r t : ℝ) :
    sourceValueTau (FiniteMixture.pure p hp c hc) Q r t =
      c*Q^p*((r^2+(1-r^2)*t)^p-r^(2*p)-
        (p : ℝ)*r^(2*p-2)*(1-r^2)*t) := by
  unfold sourceValueTau
  rw [pure_value_correction p hp c hc hQ,mul_div_assoc,
    pure_gradient_correction p hp c hc hQ,pure_centerCovariance,
    pure_centerCovariance,pure_centerFirst]
  rw [← pow_mul,← pow_mul,show 2*(p-1)=2*p-2 by omega]
  ring

theorem pure_valueTau_zero (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q) (r : ℝ) :
    sourceValueTau (FiniteMixture.pure p hp c hc) Q r 0 = 0 := by
  unfold sourceValueTau
  rw [pure_value_correction p hp c hc hQ]
  simp

end
end SlowEquilibration.SphericalParisiPureLatitudeCovariance
