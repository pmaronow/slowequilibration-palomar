-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import SlowEquilibration.Certificate

/-!
# Analytic logarithm enclosure for the nonconvex example

This closes the analytic step of Appendix A, Lemma A.1. Mathlib's derivative
proof of the logarithm expansion gives a thirteen-term lower bound and a
twenty-term upper bound. Exact rational arithmetic proves that these bounds
lie inside the manuscript's stated rational enclosure. The upper bound uses
more terms than the manuscript's sharper thirteen-term tail estimate, with
the same conclusion and no numerical approximation.
-/

@[expose] public section

namespace SlowEquilibration.LogEnclosure

open Finset Certificate

set_option maxHeartbeats 800000

/-- Equation (A.1): an exact analytic enclosure of the actual real logarithm. -/
theorem log_six_enclosure :
    (4885985 / 2726952 : ℝ) < Real.log 6 ∧
      Real.log 6 < (1628605 / 908936 : ℝ) := by
  have harg : (1 + (5 / 7 : ℝ)) / (1 - (5 / 7 : ℝ)) = 6 := by norm_num
  have hlo := Real.sum_range_le_log_div (x := (5 / 7 : ℝ))
    (by norm_num) (by norm_num) 13
  have hhi := Real.log_div_le_sum_range_add (x := (5 / 7 : ℝ))
    (by norm_num) (by norm_num) 20
  rw [harg] at hlo hhi
  have hloRat : (4885985 / 2726952 : ℝ) <
      2 * (∑ i ∈ range 13, (5 / 7 : ℝ) ^ (2 * i + 1) / (2 * i + 1)) := by
    norm_num [sum_range_succ]
  have hhiRat :
      2 * ((∑ i ∈ range 20, (5 / 7 : ℝ) ^ (2 * i + 1) / (2 * i + 1)) +
        (5 / 7 : ℝ) ^ (2 * 20 + 1) / (1 - (5 / 7 : ℝ) ^ 2)) <
      (1628605 / 908936 : ℝ) := by
    norm_num [sum_range_succ]
  constructor <;> linarith

/-- The actual parameter of the degree-4/degree-12 example. -/
noncomputable def exampleParameter : ℝ :=
  (45 - 24 * Real.log 6) / (72 * Real.log 6 - 85)

/-- The denominator in the parameter transformation is strictly positive. -/
theorem exampleParameter_denominator_pos : 0 < 72 * Real.log 6 - 85 := by
  linarith [log_six_enclosure.1]

/-- The strict parameter enclosure of Appendix A, Lemma A.1. -/
theorem exampleParameter_enclosure :
    tMinus < exampleParameter ∧ exampleParameter < tPlus := by
  have hden := exampleParameter_denominator_pos
  unfold exampleParameter tMinus tPlus
  constructor
  · apply (lt_div_iff₀ hden).2
    nlinarith [log_six_enclosure.2]
  · apply (div_lt_iff₀ hden).2
    nlinarith [log_six_enclosure.1]

/-- Closed interval membership connecting the analytic and rational certificates. -/
theorem exampleParameter_mem : exampleParameter ∈ Set.Icc tMinus tPlus :=
  ⟨exampleParameter_enclosure.1.le, exampleParameter_enclosure.2.le⟩

/-- The four polynomial sign margins for the actual logarithmic parameter. -/
theorem actual_parameter_polynomial_sign_bounds :
    (∀ r ∈ Set.Icc (0 : ℝ) (357 / 1000) ∪ Set.Icc (892 / 1000 : ℝ) 1,
      (2 / 25 : ℝ) < P exampleParameter r) ∧
    (∀ r ∈ Set.Icc (359 / 1000 : ℝ) (890 / 1000),
      P exampleParameter r < -(1 / 25 : ℝ)) ∧
    (∀ r ∈ Set.Icc (357 / 1000 : ℝ) (359 / 1000),
      D exampleParameter r < -86) ∧
    (∀ r ∈ Set.Icc (890 / 1000 : ℝ) (892 / 1000),
      (73 : ℝ) < D exampleParameter r) :=
  polynomial_sign_bounds exampleParameter exampleParameter_mem

end SlowEquilibration.LogEnclosure
