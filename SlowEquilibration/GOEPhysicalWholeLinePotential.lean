-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEWholeLinePotential
public import SlowEquilibration.GOEPhysicalPrefactors

/-! Whole-line compact-uniform ordinary determinant upper bounds under the
actual physical GOE variance b/N with arbitrary fixed codimension. The exact
finite-dimensional scale and the manuscript's finite-dimensional rate are
retained, including every real shift. -/

@[expose] public section
namespace SlowEquilibration.GOEPhysicalWholeLinePotential

noncomputable section
open Set Filter
open scoped Topology
open GOEScaling GOEPrefactors GOEPhysicalPotential GOEPhysicalPrefactors
open GOEWholeLinePotential SemicirclePotential
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma scaled_shift_mem (n j : ℕ) {b Z k : ℝ} (hb : 0<b) (hZ : 0≤Z) (hk : |k|≤Z) :
    k/scaleFactor n (n+1+j) b∈Icc
      (-Z/Real.sqrt (b/(j+1 : ℝ))) (Z/Real.sqrt (b/(j+1 : ℝ))) := by
  have ha := scaleFactor_pos n (by omega : 0<n+1+j) hb
  have hl : 0<Real.sqrt (b/(j+1 : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hlower := scaleFactor_lower n j hb.le
  have hbound : |k/scaleFactor n (n+1+j) b|≤Z/Real.sqrt (b/(j+1 : ℝ)) := by
    rw [abs_div,abs_of_pos ha]
    exact (div_le_div_of_nonneg_right hk ha.le).trans
      (div_le_div_of_nonneg_left hZ hl hlower)
  have h := abs_le.mp hbound
  change -Z/Real.sqrt (b/(j+1 : ℝ))≤k/scaleFactor n (n+1+j) b ∧
    k/scaleFactor n (n+1+j) b≤Z/Real.sqrt (b/(j+1 : ℝ))
  simpa only [neg_div] using h

/-- The ordinary physical GOE mean obeys the exact finite-dimensional rate,
uniformly over every bounded real shift interval, including inside the edge. -/
theorem physical_mean_upper_uniform (j : ℕ) {b Z eps : ℝ}
    (hb : 0<b) (hZ : 0≤Z) (heps : 0<eps) :
    ∀ᶠ n : ℕ in atTop,∀ k : ℝ,|k|≤Z →
      physicalMean n (n+1+j) b k≤Real.exp
        (physicalRate n j b k+(n+1 : ℝ)*eps) := by
  have hstd := GOEWholeLinePotential.mean_upper_uniform
    (S := Icc (-Z/Real.sqrt (b/(j+1 : ℝ))) (Z/Real.sqrt (b/(j+1 : ℝ))))
    isCompact_Icc heps
  filter_upwards [hstd] with n hn
  intro k hk
  let a := scaleFactor n (n+1+j) b
  have ha : 0<a := scaleFactor_pos n (by omega) hb
  have hbound := hn (k/a) (scaled_shift_mem n j hb hZ hk)
  rw [physicalMean_scaling n (by omega) hb]
  have hp : 0≤a^(n+1) := (pow_pos ha _).le
  have h := mul_le_mul_of_nonneg_left hbound hp
  have hex : a^(n+1)=Real.exp ((n+1 : ℝ)*Real.log a) := by
    rw [← show ((n+1:ℕ):ℝ)=(n+1 : ℝ) by simp,Real.exp_nat_mul,Real.exp_log ha]
  change a^(n+1)*meanAbsolute n (k/a)≤_
  apply h.trans_eq
  rw [hex,← Real.exp_add]
  congr 1
  unfold physicalRate
  dsimp only [a]
  ring

/-- Logarithmic version with the literal physical expectation normalization. -/
theorem physical_log_mean_upper_uniform (j : ℕ) {b Z eps : ℝ}
    (hb : 0<b) (hZ : 0≤Z) (heps : 0<eps) :
    ∀ᶠ n : ℕ in atTop,∀ k : ℝ,|k|≤Z →
      Real.log (physicalMean n (n+1+j) b k)≤
        physicalRate n j b k+(n+1 : ℝ)*eps := by
  filter_upwards [physical_mean_upper_uniform j hb hZ heps] with n hn
  intro k hk
  have hpos : 0<physicalMean n (n+1+j) b k := by
    rw [physicalMean_scaling n (by omega) hb]
    exact mul_pos (pow_pos (scaleFactor_pos n (by omega) hb) _) (meanAbsolute_all_shift_pos n _)
  exact (Real.log_le_iff_le_exp hpos).mpr (hn k hk)

end
end SlowEquilibration.GOEPhysicalWholeLinePotential
