-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiPureLatitudeCovariance
public import SlowEquilibration.SphericalPureConditionalPointVariance
public import SlowEquilibration.MixtureSubcriticalQuadratic

/-! The exact quadratic covariance majorant used in source (9.33).
It applies to the genuine value-and-zero-gradient posterior, for odd as
well as even pure degrees. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorCovarianceMajor
noncomputable section
open Set SphericalModel
open SphericalParisiPureLatitudeCovariance
open SphericalTAPCriticalPureLatitudeVariance
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A finite covariance with no constant or linear term has a quadratic
majorant on the full signed overlap interval. -/
theorem finiteMixture_abs_xi_le_xi_one_mul_sq
    (μ : FiniteMixture)
    (hzero : μ.coeff 0 = 0) (hone : μ.coeff 1 = 0)
    {t : ℝ} (ht : |t| ≤ 1) :
    |μ.xi t| ≤ μ.xi 1 * t^2 := by
  unfold FiniteMixture.xi
  calc
    |∑ k ∈ μ.coeff.support, μ.coeff k*t^k| ≤
        ∑ k ∈ μ.coeff.support, |μ.coeff k*t^k| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ μ.coeff.support, μ.coeff k*t^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hk2 : 2 ≤ k := by
        by_contra hn
        interval_cases k <;> simp_all [Finsupp.mem_support_iff]
      rw [abs_mul, abs_of_nonneg (μ.nonneg k), abs_pow]
      exact mul_le_mul_of_nonneg_left
        (by
          have hh := pow_le_pow_of_le_one (abs_nonneg t) ht hk2
          simpa only [sq_abs] using hh)
        (μ.nonneg k)
    _ = (∑ k ∈ μ.coeff.support, μ.coeff k*1^k)*t^2 := by
      simp only [one_pow, mul_one, Finset.sum_mul]

/-- The source's posterior residual is bounded by its own point variance
times the square of transverse overlap. -/
theorem pure_sourceValueTau_abs_le_self_mul_sq
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q q t : ℝ} (hQ : 0 < Q) (hq : q ∈ Ioo (0 : ℝ) 1)
    (ht : |t| ≤ 1) :
    |sourceValueTau (FiniteMixture.pure p hp alpha halpha) Q q t| ≤
      sourceValueTau (FiniteMixture.pure p hp alpha halpha) Q q 1*t^2 := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let ρ := μ.taylorResidual (mul_pos hQ (sq_pos_of_pos hq.1))
    (mul_pos hQ (by nlinarith [hq.1, hq.2] : 0 < 1-q^2))
  have hself := finiteMixture_abs_xi_le_xi_one_mul_sq ρ
    (ρ.zero_below_two 0 (by omega)) (ρ.zero_below_two 1 (by omega)) ht
  rw [pure_valueTau_eq_residual_xi p hp alpha halpha hQ hq t]
  rw [pure_valueTau_eq_residual_xi p hp alpha halpha hQ hq 1]
  exact hself

/-- Literal pure source (9.33), including inverse temperature and the
normalization by the conditional latitude variance. -/
theorem pure_source_covariance_major
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (β : ℝ) {Q q t : ℝ} (hQ : 0 < Q) (hq : q ∈ Ioo (0 : ℝ) 1)
    (ht : |t| ≤ 1) :
    |β^2*sourceValueTau (FiniteMixture.pure p hp alpha halpha) Q q t| ≤
      β^2*Q^p*sourcePureLatitudeVariance p alpha q*t^2 := by
  have hraw := pure_sourceValueTau_abs_le_self_mul_sq p hp alpha halpha hQ hq ht
  have hself : sourceValueTau (FiniteMixture.pure p hp alpha halpha) Q q 1 =
      Q^p*sourcePureLatitudeVariance p alpha q := by
    have hpow1 : (q^2)^p = q^(2*p) := by rw [←pow_mul]
    have hpow2 : (q^2)^(p-1) = q^(2*p-2) := by
      rw [←pow_mul]
      congr 1
      omega
    unfold sourceValueTau sourcePureLatitudeVariance
    rw [show q^2+(1-q^2)*1=1 by ring]
    simp only [mul_one]
    rw [pure_value_correction p hp alpha halpha hQ,
      mul_div_assoc, pure_gradient_correction p hp alpha halpha hQ,
      pure_centerCovariance p hp alpha halpha,
      pure_centerCovariance p hp alpha halpha,
      pure_centerFirst p hp alpha halpha]
    rw [hpow1,hpow2]
    ring
  rw [abs_mul, abs_of_nonneg (sq_nonneg β)]
  convert mul_le_mul_of_nonneg_left hraw (sq_nonneg β) using 1
  rw [hself]
  ring

end
end SlowEquilibration.SourcePureCapPosteriorCovarianceMajor
