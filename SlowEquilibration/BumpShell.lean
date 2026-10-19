-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Uniform inner-shell mass ratio

This file proves the scalar half-shell estimate used in manuscript Lemma
`lem:sp-bumps`, equation `eq:sp-bump-mass`, uniformly over every dimension
at least two.  Real Bernoulli's inequality gives the estimate directly:
with exponent `N/2` and increment `-1/N`, its affine lower bound is `1/2`.
The Euclidean ball-volume formula and parameter-measure construction are
separate geometric measure steps.
-/

namespace SlowEquilibration

/-- The bump's inner-shell volume ratio is at least one half in every real
dimension parameter `N ≥ 2`; no finite range of dimensions is substituted. -/
theorem bump_shell_rpow_lower_bound (N : ℝ) (hN : 2 ≤ N) :
    (1 / 2 : ℝ) ≤ Real.rpow (1 - 1 / N) (N / 2) := by
  have hNpos : 0 < N := by linarith
  have hincr : -1 ≤ -(1 / N) := by
    have hdiv : 1 / N ≤ 1 := (div_le_one₀ hNpos).2 (by linarith)
    linarith
  have hexponent : 1 ≤ N / 2 := by linarith
  have hbernoulli := one_add_mul_self_le_rpow_one_add hincr hexponent
  have hleft : 1 + (N / 2) * -(1 / N) = (1 / 2 : ℝ) := by
    field_simp [hNpos.ne']
    norm_num
  simpa only [hleft, ← sub_eq_add_neg, Real.rpow_eq_pow] using hbernoulli

/-- Natural-dimension form of the uniform half-shell ratio. -/
theorem bump_shell_nat_rpow_lower_bound (n : ℕ) (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.rpow (1 - 1 / (n : ℝ)) ((n : ℝ) / 2) :=
  bump_shell_rpow_lower_bound n (by exact_mod_cast hn)

/-- Equivalent radius-ratio form for the Euclidean ball volume comparison. -/
theorem bump_shell_sqrt_pow_lower_bound (n : ℕ) (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ (Real.sqrt (1 - 1 / (n : ℝ))) ^ n := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : 1 / (n : ℝ) ≤ 1 := (div_le_one₀ hnpos).2 (by linarith)
    linarith
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hbase]
  have hexponent : (1 / (2 : ℝ)) * (n : ℝ) = (n : ℝ) / 2 := by ring
  rw [hexponent]
  simpa only [Real.rpow_eq_pow] using bump_shell_nat_rpow_lower_bound n hn

end SlowEquilibration
