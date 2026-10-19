-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCaptureThreeEvenMomentGap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCaptureThreeEvenMomentLaw

open Set Filter MeasureTheory
open PureCaptureThreeEvenMomentGap

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Three distinct positive even moments of a measurable real observable
identify its three-point support and its exact nonzero mass. This is the
measure-theoretic equality case of the manuscript's weighted Jensen argument. -/
theorem support_and_mass_of_three_even_moments
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (x Q : ℝ) (hQ : 0 < Q)
    (a b c : ℕ) (ha0 : 0 < a) (hab : a < b) (hbc : b < c)
    (ha : Even a) (hb : Even b) (hc : Even c)
    (haI : Integrable (fun z => f z ^ a) ν)
    (hbI : Integrable (fun z => f z ^ b) ν)
    (hcI : Integrable (fun z => f z ^ c) ν)
    (hA : (∫ z, f z ^ a ∂ν) = (1 - x) * Q ^ a)
    (hB : (∫ z, f z ^ b ∂ν) = (1 - x) * Q ^ b)
    (hC : (∫ z, f z ^ c ∂ν) = (1 - x) * Q ^ c) :
    (∀ᵐ z ∂ν, f z ∈ ({-Q, 0, Q} : Set ℝ)) ∧
      ν.real {z | |f z| = Q} = 1 - x := by
  have hg (z : Ω) : powerGap a b c (|f z| / Q) =
      (1 - middleWeight a b c) * (f z ^ a / Q ^ a) +
        middleWeight a b c * (f z ^ c / Q ^ c) - f z ^ b / Q ^ b := by
    simp only [powerGap, div_pow, ha.pow_abs, hb.pow_abs, hc.pow_abs]
  have haN := haI.div_const (Q ^ a)
  have hbN := hbI.div_const (Q ^ b)
  have hcN := hcI.div_const (Q ^ c)
  have hsum : Integrable (fun z =>
      (1 - middleWeight a b c) * (f z ^ a / Q ^ a) +
        middleWeight a b c * (f z ^ c / Q ^ c)) ν :=
    (haN.const_mul _).add (hcN.const_mul _)
  have hint : Integrable (fun z => powerGap a b c (|f z| / Q)) ν := by
    simp_rw [hg]
    exact ((haN.const_mul _).add (hcN.const_mul _)).sub hbN
  have hgapIntegral : (∫ z, powerGap a b c (|f z| / Q) ∂ν) = 0 := by
    simp_rw [hg]
    rw [integral_sub hsum hbN,
      integral_add (haN.const_mul (1 - middleWeight a b c))
        (hcN.const_mul (middleWeight a b c)),
      integral_const_mul, integral_const_mul,
      integral_div, integral_div, integral_div, hA, hB, hC]
    simp only [mul_div_cancel_right₀ _ (pow_ne_zero a hQ.ne'),
      mul_div_cancel_right₀ _ (pow_ne_zero b hQ.ne'),
      mul_div_cancel_right₀ _ (pow_ne_zero c hQ.ne')]
    ring
  have hzero : ∀ᵐ z ∂ν, powerGap a b c (|f z| / Q) = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (.of_forall fun z => powerGap_nonneg ha0 hab hbc (div_nonneg (abs_nonneg _) hQ.le))
      hint).mp hgapIntegral
  have hsupport : ∀ᵐ z ∂ν, f z = 0 ∨ |f z| = Q := by
    filter_upwards [hzero] with z hz
    by_cases hz0 : f z = 0
    · exact Or.inl hz0
    right
    by_contra hne
    have ht : 0 < |f z| / Q := div_pos (abs_pos.mpr hz0) hQ
    have ht1 : |f z| / Q ≠ 1 := by
      intro heq
      exact hne ((div_eq_one_iff_eq hQ.ne').mp heq)
    exact (ne_of_gt (powerGap_pos hab hbc ht ht1)) hz
  constructor
  · filter_upwards [hsupport] with z hz
    rcases hz with hz | hz
    · simp [hz]
    · rcases (abs_eq hQ.le).mp hz with hz | hz <;> simp [hz]
  · let E : Set Ω := {z | |f z| = Q}
    have hE : MeasurableSet E := measurableSet_eq_fun (continuous_abs.measurable.comp hf) measurable_const
    have hfun : (fun z => f z ^ a) =ᵐ[ν] E.indicator (fun _ => Q ^ a) := by
      filter_upwards [hsupport] with z hz
      by_cases he : z ∈ E
      · rw [Set.indicator_of_mem he, ← ha.pow_abs]
        exact congrArg (fun r : ℝ => r ^ a) he
      · rw [Set.indicator_of_notMem he]
        rcases hz with hz | hz
        · simp [hz, ne_of_gt ha0]
        · exact False.elim (he hz)
    have hmass := integral_congr_ae hfun
    rw [integral_indicator_const (Q ^ a) hE, smul_eq_mul, hA] at hmass
    exact mul_right_cancel₀ (pow_ne_zero a hQ.ne') hmass.symm

end SlowEquilibration.PureCaptureThreeEvenMomentLaw
