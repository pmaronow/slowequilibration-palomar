-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.MeanInequalities

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCaptureThreeEvenMomentGap

set_option autoImplicit false
set_option maxHeartbeats 600000

/-- The interpolation weight locating the middle exponent between the two
outer exponents. -/
def middleWeight (a b c : ℕ) : ℝ := ((b : ℝ) - a) / ((c : ℝ) - a)

/-- The weighted arithmetic-geometric mean gap for three distinct powers.
This is the pointwise form of the manuscript's weighted Jensen argument. -/
def powerGap (a b c : ℕ) (t : ℝ) : ℝ :=
  (1 - middleWeight a b c) * t ^ a + middleWeight a b c * t ^ c - t ^ b

theorem middleWeight_mem_Ioo {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    middleWeight a b c ∈ Set.Ioo (0 : ℝ) 1 := by
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
  have hac : 0 < (c : ℝ) - a := by linarith
  constructor
  · exact div_pos (by linarith) hac
  · dsimp [middleWeight]
    exact (div_lt_one hac).mpr (by linarith)

private theorem geometric_interpolation {a b c : ℕ}
    (hab : a < b) (hbc : b < c) {t : ℝ} (ht : 0 < t) :
    (t ^ a : ℝ) ^ (1 - middleWeight a b c) *
      (t ^ c : ℝ) ^ middleWeight a b c = t ^ b := by
  have hac : (c : ℝ) - a ≠ 0 := by
    have hh : (a : ℝ) < c := by exact_mod_cast hab.trans hbc
    linarith
  have hexp : (a : ℝ) * (1 - middleWeight a b c) +
      (c : ℝ) * middleWeight a b c = b := by
    unfold middleWeight
    field_simp [hac]
    ring
  rw [← Real.rpow_natCast t a, ← Real.rpow_natCast t c,
    ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
    ← Real.rpow_add ht, hexp, Real.rpow_natCast]

theorem powerGap_nonneg {a b c : ℕ} (ha : 0 < a)
    (hab : a < b) (hbc : b < c) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ powerGap a b c t := by
  rcases eq_or_lt_of_le ht with hzero | ht
  · subst t
    simp [powerGap, ne_of_gt ha, ne_of_gt (ha.trans hab),
      ne_of_gt (ha.trans (hab.trans hbc))]
  have hw := middleWeight_mem_Ioo hab hbc
  have hg := Real.geom_mean_le_arith_mean2_weighted
    (by linarith [hw.2] : 0 ≤ 1 - middleWeight a b c) hw.1.le
    (pow_nonneg ht.le a) (pow_nonneg ht.le c) (by ring)
  rw [geometric_interpolation hab hbc ht] at hg
  exact sub_nonneg.mpr hg

theorem powerGap_pos {a b c : ℕ} (hab : a < b) (hbc : b < c)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    0 < powerGap a b c t := by
  have hw := middleWeight_mem_Ioo hab hbc
  have hne : t ^ a ≠ t ^ c := fun heq =>
    (Nat.ne_of_lt (hab.trans hbc)) ((pow_right_inj₀ ht ht1).mp heq)
  have hg := (Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos
    (by linarith [hw.2] : 0 < 1 - middleWeight a b c) hw.1
    (pow_nonneg ht.le a) (pow_nonneg ht.le c) (by ring)).mpr hne
  rw [geometric_interpolation hab hbc ht] at hg
  exact sub_pos.mpr hg

/-- A fixed positive gap survives on a neighborhood of any positive overlap
away from the prescribed overlap Q. -/
theorem exists_powerGap_neighborhood {a b c : ℕ}
    (hab : a < b) (hbc : b < c) {Q q : ℝ}
    (hQ : 0 < Q) (hq : 0 < q) (hne : q ≠ Q) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧
      ∀ r : ℝ, |r - q| < ρ → δ ≤ powerGap a b c (|r| / Q) := by
  let g : ℝ → ℝ := fun r => powerGap a b c (|r| / Q)
  have hg : Continuous g := by unfold g powerGap; fun_prop
  have hpos : 0 < g q := by
    dsimp [g]
    rw [abs_of_pos hq]
    exact powerGap_pos hab hbc (div_pos hq hQ)
      (by intro heq; exact hne ((div_eq_one_iff_eq hQ.ne').mp heq))
  have hmem : {r : ℝ | g q / 2 < g r} ∈ nhds q :=
    (isOpen_lt continuous_const hg).mem_nhds (by dsimp; linarith)
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ρ, g q / 2, hρ, by linarith, ?_⟩
  intro r hr
  exact le_of_lt (hsub (by simpa [Metric.mem_ball, Real.dist_eq] using hr))

end SlowEquilibration.PureCaptureThreeEvenMomentGap
