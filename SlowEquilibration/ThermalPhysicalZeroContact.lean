-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSParisiMeasure
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# The zero contact for every finite spherical covariance

This proves the full variational statement of manuscript Lemma 5.6, including
mixtures with a quadratic term. The measure used below is the actual, existing
unique minimizer of the ordinary Crisanti--Sommers integral functional. No
identification of its value with a physical thermodynamic limit is assumed.
-/

namespace SlowEquilibration.ThermalPhysicalZeroContact

open MeasureTheory Set Filter CrisantiSommers
open scoped Topology

/-- Every nonnegative covariance with degrees at least two obeys its Euler
inequality. Equality is allowed, which is essential for quadratic mixtures. -/
theorem covariance_euler_bound (μ : FiniteMixture) {a : ℝ} (ha : 0 ≤ a) :
    2 * μ.xi a ≤ a * μ.xi1 a := by
  unfold FiniteMixture.xi FiniteMixture.xi1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp2 := μ.degree_ge_two hp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpow : a ^ p = a ^ (p - 1) * a := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ p by omega)]
  rw [hpow]
  have hnonneg : 0 ≤ μ.coeff p * a ^ (p - 1) * a :=
    mul_nonneg (mul_nonneg (μ.nonneg p) (pow_nonneg ha _)) ha
  have hmul := mul_le_mul_of_nonneg_right hpR hnonneg
  nlinarith only [hmul]

private theorem firstVariation_continuousOn_cutoff (μ : FiniteMixture) (β : ℝ)
    (ζ : Admissible) :
    ContinuousOn (firstVariation β μ.xi ζ.law) (Icc 0 ζ.cutoff) := by
  intro r hr
  exact (firstVariation_hasDerivAt β μ.xi ζ.law ζ.hasCutoff
    (hr.2.trans_lt ζ.hasCutoff.2.1)
    (μ.hasDerivAt_xi r)).continuousAt.continuousWithinAt

private theorem integral_triangular_constant {a C : ℝ} :
    (∫ t in (0 : ℝ)..a, (a - t) / C ^ 2) = a ^ 2 / (2 * C ^ 2) := by
  have hs : (∫ t in (0 : ℝ)..a, a - t) =
      (∫ t in (0 : ℝ)..a, a) - (∫ t in (0 : ℝ)..a, t) :=
    intervalIntegral.integral_sub intervalIntegrable_const
      (continuous_id.intervalIntegrable 0 a)
  rw [intervalIntegral.integral_div, hs]
  simp only [intervalIntegral.integral_const, integral_id,
    sub_zero, smul_eq_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  ring

/-- The maximum of the actual first variation is zero for every finite
mixture, even when the first support point is positive. -/
theorem minimizer_firstVariation_maximum_zero (μ : FiniteMixture) (β : ℝ)
    (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi) :
    (∀ r ∈ Ico 0 1, firstVariation β μ.xi ζ.law r ≤ 0) ∧
    (∀ᵐ r ∂ζ.law, firstVariation β μ.xi ζ.law r = 0) ∧
    (∀ r ∈ ζ.law.support, firstVariation β μ.xi ζ.law r = 0) := by
  have hξcont : ContinuousOn μ.xi (Ico 0 1) :=
    fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt
  obtain ⟨m, hmax, hsupport⟩ :=
    (ζ.minimizer_iff_support_on_maximum β μ.xi hξcont).mp hmin
  obtain ⟨a, ha, harange, hfirst⟩ :=
    CSStructure.exists_first_support_point ζ.law ζ.hasCutoff
  have hfa : firstVariation β μ.xi ζ.law a = m :=
    CSStructure.eq_on_support_of_ae_eq ζ.law ζ.hasCutoff
      (firstVariation_continuousOn_cutoff μ β ζ) hsupport ha
  have hmnonneg : 0 ≤ m := by
    simpa only [firstVariation, μ.xi_zero, mul_zero,
      intervalIntegral.integral_same, sub_self] using
      hmax 0 (by norm_num : (0 : ℝ) ∈ Ico 0 1)
  have hmnonpos : m ≤ 0 := by
    by_cases ha0 : a = 0
    · simpa [ha0, firstVariation, μ.xi_zero] using hfa.symm.le
    have hapos : 0 < a := lt_of_le_of_ne harange.1 (Ne.symm ha0)
    have ha1 : a < 1 := harange.2.trans_lt ζ.hasCutoff.2.1
    have hlocal : IsLocalMax (firstVariation β μ.xi ζ.law) a := by
      filter_upwards [Ioo_mem_nhds hapos ha1] with r hr
      rw [hfa]
      exact hmax r ⟨hr.1.le, hr.2⟩
    have hstationary := hlocal.deriv_eq_zero
    rw [firstVariation_deriv β μ.xi ζ.law ζ.hasCutoff ha1
      (μ.hasDerivAt_xi a).differentiableAt,
      (μ.hasDerivAt_xi a).deriv] at hstationary
    have hint : (∫ t in (0 : ℝ)..a, 1 / (xHat ζ.law t) ^ 2) =
        a / (xHat ζ.law a) ^ 2 := by
      calc
        _ = ∫ t in (0 : ℝ)..a, 1 / (xHat ζ.law a) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hapos.le] at ht
          dsimp only
          rw [CSStructure.xHat_constant_below_first_support ζ.law hfirst ht.2]
        _ = _ := by simp; ring
    rw [hint] at hstationary
    have htri : (∫ t in (0 : ℝ)..a, (a - t) / (xHat ζ.law t) ^ 2) =
        a ^ 2 / (2 * (xHat ζ.law a) ^ 2) := by
      calc
        _ = ∫ t in (0 : ℝ)..a, (a - t) / (xHat ζ.law a) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hapos.le] at ht
          dsimp only
          rw [CSStructure.xHat_constant_below_first_support ζ.law hfirst ht.2]
        _ = _ := integral_triangular_constant
    have heuler := mul_le_mul_of_nonneg_left (covariance_euler_bound μ hapos.le)
      (sq_nonneg β)
    have hscaled := congrArg (fun u : ℝ => a * u) (sub_eq_zero.mp hstationary)
    have hden : a * (a / (xHat ζ.law a) ^ 2) =
        2 * (a ^ 2 / (2 * (xHat ζ.law a) ^ 2)) := by ring
    rw [← hfa]
    unfold firstVariation
    rw [htri]
    nlinarith
  have hm0 : m = 0 := le_antisymm hmnonpos hmnonneg
  rw [hm0] at hmax hsupport
  exact ⟨hmax, hsupport, fun r hr =>
    CSStructure.eq_on_support_of_ae_eq ζ.law ζ.hasCutoff
      (firstVariation_continuousOn_cutoff μ β ζ) hsupport hr⟩

/-- Manuscript Lemma 5.6 for the canonical existing minimizer, with no
mixture-degree, minimizer-existence or physical-pressure premise. -/
theorem canonical_zero_contact (μ : FiniteMixture) (β : ℝ) :
    let ζ := CSParisiMeasure.canonicalMinimizer μ β
    (CSStructure.potential μ β ζ.law 0 = 0) ∧
    (∀ r ∈ Ico 0 1, 0 ≤ CSStructure.potential μ β ζ.law r) ∧
    (∀ᵐ r ∂ζ.law, CSStructure.potential μ β ζ.law r = 0) ∧
    (∀ r ∈ ζ.law.support, CSStructure.potential μ β ζ.law r = 0) := by
  dsimp only
  obtain ⟨hmax, hae, hsupp⟩ := minimizer_firstVariation_maximum_zero μ β
    (CSParisiMeasure.canonicalMinimizer μ β)
    (CSParisiMeasure.canonicalMinimizer_isMinimizer μ β)
  refine ⟨by simp [CSStructure.potential, firstVariation, μ.xi_zero],
    fun r hr => neg_nonneg.mpr (hmax r hr), ?_, ?_⟩
  · exact hae.mono (fun _ hr => by simp [CSStructure.potential, hr])
  · intro r hr
    simp [CSStructure.potential, hsupp r hr]

/-- The origin is additionally in the actual support when the smallest
degree is at least three, as required by the last clause of Lemma 5.6. -/
theorem canonical_origin_mem_support (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree)
    {β : ℝ} (hβ : 0 < β) :
    (0 : ℝ) ∈ (CSParisiMeasure.canonicalMinimizer μ β).law.support :=
  CSStructure.origin_mem_support_of_minimizer μ hd hβ
    (CSParisiMeasure.canonicalMinimizer μ β)
    (CSParisiMeasure.canonicalMinimizer_isMinimizer μ β)

end SlowEquilibration.ThermalPhysicalZeroContact
