-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

/-! The numerical origin-removal argument of manuscript Theorem 6.3.
Any nonnegative common lower bound on the zero-star probabilities must
vanish, since the GG decrement pays that bound at every harmonic step. -/

@[expose] public section
namespace SlowEquilibration.DirectingPhysical
open Filter
open scoped Topology BigOperators

set_option maxHeartbeats 750000

/-- Finite telescoping consequence of the actual zero-star recurrence. -/
theorem zeroStar_harmonic_bound (T : ℕ → ℝ) {b c : ℝ}
    (hc : 0 < c) (hb : ∀ n, b ≤ T n) (hT : ∀ n, 0 ≤ T n)
    (hrec : ∀ n, T (n + 1) ≤ (1 - c / ((n : ℝ) + 1)) * T n) (n : ℕ) :
    c * b * (∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) ≤ T 0 := by
  have htelescope : ∀ n : ℕ,
      c * b * (∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) ≤ T 0 - T n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep := hrec n
      have hbound : c / ((n : ℝ) + 1) * b ≤ c / ((n : ℝ) + 1) * T n :=
        mul_le_mul_of_nonneg_left (hb n) (by positivity)
      rw [Finset.sum_range_succ]
      have heq : c * b * (1 / ((n : ℝ) + 1)) = c / ((n : ℝ) + 1) * b := by ring
      rw [mul_add, heq]
      nlinarith
  exact (htelescope n).trans (sub_le_self _ (hT n))

/-- A harmonic GG recurrence allows no positive mass common to all
zero-star events. This avoids any extra convergence hypothesis. -/
theorem zeroStar_common_lower_eq_zero (T : ℕ → ℝ) {b c : ℝ}
    (hc : 0 < c) (hb0 : 0 ≤ b) (hb : ∀ n, b ≤ T n) (hT : ∀ n, 0 ≤ T n)
    (hrec : ∀ n, T (n + 1) ≤ (1 - c / ((n : ℝ) + 1)) * T n) : b = 0 := by
  apply le_antisymm _ hb0
  by_contra h
  have hbpos : 0 < b := lt_of_not_ge h
  have hcb : 0 < c * b := mul_pos hc hbpos
  have hh : ∀ᶠ n : ℕ in atTop,
      T 0 / (c * b) < ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
      (eventually_gt_atTop (T 0 / (c * b)))
  obtain ⟨n, hn⟩ := hh.exists
  have hbound := zeroStar_harmonic_bound T hc hb hT hrec n
  have hlarge : T 0 < c * b * (∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) := by
    have := (div_lt_iff₀ hcb).mp hn
    nlinarith
  exact (not_lt_of_ge hbound) hlarge

end SlowEquilibration.DirectingPhysical
