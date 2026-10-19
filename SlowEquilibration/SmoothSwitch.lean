-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

/-! A literal smooth switch with the source's numerical derivative bound 2.
It is the normalized primitive of a genuine smooth bump with a half-length
plateau; no existence or differential identities are assumed. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SmoothSwitch

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def bump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
def normalizer : ℝ := ∫ t in (0 : ℝ)..1, bump t
def switch (x : ℝ) : ℝ := (∫ t in (0 : ℝ)..x, bump t) / normalizer

lemma bump_zero_left {x : ℝ} (hx : x ≤ 0) : bump x = 0 := by
  apply bump.zero_of_le_dist
  simp only [bump, Real.dist_eq]
  rw [abs_of_nonpos (by linarith : x - 1 / 2 ≤ 0)]
  linarith

lemma bump_zero_right {x : ℝ} (hx : 1 ≤ x) : bump x = 0 := by
  apply bump.zero_of_le_dist
  simp only [bump, Real.dist_eq]
  rw [abs_of_nonneg (by linarith : 0 ≤ x - 1 / 2)]
  linarith

lemma bump_plateau {x : ℝ} (hx : x ∈ Icc (1 / 4 : ℝ) (3 / 4)) : bump x = 1 := by
  apply bump.one_of_mem_closedBall
  simp only [bump, mem_closedBall, Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma normalizer_lower : (1 / 2 : ℝ) ≤ normalizer := by
  have hi (a b : ℝ) : IntervalIntegrable (fun t => bump t) volume a b :=
    bump.continuous.intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 / 4)) (hi (1 / 4) (3 / 4))
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals (hi 0 (3 / 4)) (hi (3 / 4) 1)
  have hmiddle : (∫ t in (1 / 4 : ℝ)..(3 / 4), bump t) = 1 / 2 := by
    calc
      _ = ∫ _ in (1 / 4 : ℝ)..(3 / 4), (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact bump_plateau (by simpa only [uIcc_of_le (show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num)] using hx)
      _ = _ := by simp; ring
  have hleft : 0 ≤ ∫ t in (0 : ℝ)..(1 / 4), bump t := intervalIntegral.integral_nonneg_of_forall
    (show (0 : ℝ) ≤ 1 / 4 by norm_num) bump.nonneg'
  have hright : 0 ≤ ∫ t in (3 / 4 : ℝ)..1, bump t := intervalIntegral.integral_nonneg_of_forall
    (show (3 / 4 : ℝ) ≤ 1 by norm_num) bump.nonneg'
  dsimp [normalizer]
  linarith

lemma normalizer_pos : 0 < normalizer := lt_of_lt_of_le (by norm_num) normalizer_lower

lemma hasDerivAt_switch (x : ℝ) : HasDerivAt switch (bump x / normalizer) x := by
  exact (intervalIntegral.integral_hasDerivAt_right (bump.continuous.intervalIntegrable 0 x)
    bump.continuous.stronglyMeasurable.stronglyMeasurableAtFilter bump.continuous.continuousAt).div_const _

lemma deriv_switch (x : ℝ) : deriv switch x = bump x / normalizer := (hasDerivAt_switch x).deriv

lemma contDiff_switch : ContDiff ℝ ∞ switch := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_switch x).differentiableAt, ?_⟩
  have heq : deriv switch = fun x => bump x / normalizer := funext deriv_switch
  rw [heq]
  exact bump.contDiff.div_const _

lemma zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : switch x = 0 := by
  have hz : (∫ t in (0 : ℝ)..x, bump t) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc x 0 := by simpa [uIcc_of_ge hx] using ht
        exact bump_zero_left ht'.2
      _ = 0 := by simp
  simp only [switch, hz, zero_div]

lemma one_of_one_le {x : ℝ} (hx : 1 ≤ x) : switch x = 1 := by
  have hz : (∫ t in (1 : ℝ)..x, bump t) = 0 := by
    calc
      _ = ∫ _ in (1 : ℝ)..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc 1 x := by simpa [uIcc_of_le hx] using ht
        exact bump_zero_right ht'.1
      _ = 0 := by simp
  have he := intervalIntegral.integral_add_adjacent_intervals
    (show IntervalIntegrable (fun t => bump t) volume 0 1 from bump.continuous.intervalIntegrable 0 1)
    (show IntervalIntegrable (fun t => bump t) volume 1 x from bump.continuous.intervalIntegrable 1 x)
  rw [hz, add_zero] at he
  rw [switch, ← he, ← normalizer, div_self normalizer_pos.ne']

lemma monotone_switch : Monotone switch :=
  monotone_of_deriv_nonneg (fun x => (hasDerivAt_switch x).differentiableAt)
    (fun x => by rw [deriv_switch]; exact div_nonneg bump.nonneg normalizer_pos.le)

lemma nonneg (x : ℝ) : 0 ≤ switch x := by
  by_cases hx : x ≤ 0
  · rw [zero_of_nonpos hx]
  · have h := monotone_switch (le_of_not_ge hx)
    simpa only [zero_of_nonpos (le_refl 0)] using h

lemma le_one (x : ℝ) : switch x ≤ 1 := by
  by_cases hx : 1 ≤ x
  · rw [one_of_one_le hx]
  · have h := monotone_switch (le_of_not_ge hx)
    simpa only [one_of_one_le (le_refl 1)] using h

lemma abs_deriv_le_two (x : ℝ) : |deriv switch x| ≤ 2 := by
  rw [deriv_switch, abs_of_nonneg (div_nonneg bump.nonneg normalizer_pos.le),
    div_le_iff₀ normalizer_pos]
  linarith [bump.le_one (x := x), normalizer_lower]

end SlowEquilibration.SmoothSwitch
