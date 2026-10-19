-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixture

/-! The exact square-root coefficient bounds used for construction of the
infinite Gaussian field and its first two derivatives. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
variable (μ : InfiniteMixture)

theorem summable_weighted_sqrt {s : ℝ} (hs : s≤5/2) :
    Summable (fun p : ℕ => (p:ℝ)^s*Real.sqrt (μ.coeff p)) := by
  apply μ.weighted_summable.of_nonneg_of_le (fun p => by positivity)
  intro p
  by_cases hp : p<2
  · simp [μ.zero_below_two p hp]
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1≤p by omega)) hs) (Real.sqrt_nonneg _)

theorem summable_sqrt : Summable (fun p => Real.sqrt (μ.coeff p)) := by
  simpa using μ.summable_weighted_sqrt (s := 0) (by norm_num)

theorem summable_shifted_sqrt : Summable (fun p => Real.sqrt (μ.coeff (p+2))) :=
  (summable_nat_add_iff 2).2 μ.summable_sqrt

theorem summable_shifted_weighted_sqrt {s : ℝ} (hs : s≤5/2) :
    Summable (fun p : ℕ => (p+2:ℕ)^s*Real.sqrt (μ.coeff (p+2))) :=
  (summable_nat_add_iff 2).2 (μ.summable_weighted_sqrt hs)

end SlowEquilibration.InfiniteMixture
