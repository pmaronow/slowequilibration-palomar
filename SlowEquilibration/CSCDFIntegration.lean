-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CrisantiSommers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.CDF

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

private lemma interval_integral_upper_indicator {r s : ℝ}
    (hr : r ≤ 1) (hs : s ≤ 1) :
    (∫ t in r..1, if s ≤ t then (1:ℝ) else 0) = 1-max r s := by
  by_cases hsr : s ≤ r
  · rw [max_eq_left hsr]
    have heq : (∫ t in r..1, if s ≤ t then (1:ℝ) else 0) = ∫ t in r..1, (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hr] at ht
      simp [hsr.trans ht.1]
    rw [heq]
    simp
  · have hrs : r ≤ s := le_of_not_ge hsr
    have hint (a b : ℝ) (hab : a ≤ b) :
        IntervalIntegrable (fun t => if s ≤ t then (1:ℝ) else 0) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      apply (integrable_const (1:ℝ)).mono'
      · exact (Measurable.ite (measurableSet_le measurable_const measurable_id)
          measurable_const measurable_const).aestronglyMeasurable
      · apply Eventually.of_forall
        intro t
        split_ifs <;> norm_num
    have hleft : (∫ t in r..s, if s ≤ t then (1:ℝ) else 0) = 0 := by
      calc
        (∫ t in r..s, if s ≤ t then (1:ℝ) else 0) = ∫ t in r..s, (0:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hrs
          intro t ht
          simp [not_le.mpr ht.2]
        _ = 0 := by simp
    have hright : (∫ t in s..1, if s ≤ t then (1:ℝ) else 0) = 1-s := by
      calc
        (∫ t in s..1, if s ≤ t then (1:ℝ) else 0) = ∫ t in s..1, (1:ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hs] at ht
          simp [ht.1]
        _ = 1-s := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint r s hrs) (hint s 1 hs)
    rw [hleft, hright, zero_add] at hsplit
    rw [← hsplit, max_eq_right hrs]

/-- The kernel definition of xHat is exactly the integral of the ordinary
probability distribution function, proved by genuine Fubini. -/
theorem xHat_integrated_distribution (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q r : ℝ} (hq : HasCutoff ζ q) (hr : r ≤ 1) :
    xHat ζ r = ∫ t in r..1, ζ.real (Iic t) := by
  let F : ℝ → ℝ → ℝ := fun t s => if s ≤ t then 1 else 0
  have hFm : Measurable (Function.uncurry F) := by
    exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      measurable_const measurable_const
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ioc r 1)).prod ζ) := by
    apply (integrable_const (1:ℝ)).mono' hFm.aestronglyMeasurable
    apply Eventually.of_forall
    rintro ⟨t, s⟩
    dsimp only [Function.uncurry_def, F]
    split_ifs <;> norm_num
  rw [← uIoc_of_le hr] at hFi
  have hswap := intervalIntegral_integral_swap (f := F) (a := r) (b := 1) (μ := ζ) hFi
  have hinner : ∀ t, (∫ s, F t s ∂ζ) = ζ.real (Iic t) := by
    intro t
    change (∫ s, (Iic t).indicator (fun _ => (1:ℝ)) s ∂ζ) = _
    rw [integral_indicator measurableSet_Iic]
    simp
  simp only [hinner] at hswap
  have hright : (∫ s, (∫ t in r..1, F t s) ∂ζ) = xHat ζ r := by
    unfold xHat
    apply integral_congr_ae
    filter_upwards [hq.2.2] with s hs
    exact interval_integral_upper_indicator hr (hs.2.trans hq.2.1.le)
  rw [hright] at hswap
  exact hswap.symm

/-- The Mathlib CDF and the manuscript's integrated distribution agree
with the hatted function. -/
theorem xHat_integrated_cdf (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q r : ℝ} (hq : HasCutoff ζ q) (hr : r ≤ 1) :
    xHat ζ r = ∫ t in r..1, cdf ζ t := by
  simpa only [cdf_eq_real] using xHat_integrated_distribution ζ hq hr

/-- The exact manuscript convention, with the distribution function
ζ([0,t]), follows from nonnegative support of the actual law. -/
theorem xHat_integrated_distribution_Icc (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q r : ℝ} (hq : HasCutoff ζ q) (hr : r ≤ 1) :
    xHat ζ r = ∫ t in r..1, ζ.real (Icc 0 t) := by
  rw [xHat_integrated_distribution ζ hq hr]
  apply intervalIntegral.integral_congr
  intro t _
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hq.2.2] with s hs
  simp [hs.1]

end SlowEquilibration.CrisantiSommers
