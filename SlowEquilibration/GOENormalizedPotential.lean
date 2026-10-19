-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPrefactors

@[expose] public section

/-! # Actual determinant asymptotics at varying outside-edge shifts

Uniform genuine bounded prefactors yield the actual leading exponent for any
convergent outside-edge shift sequence. No convergence of an expected log
observable or semicircle integral is supplied as a premise.
-/

namespace SlowEquilibration.GOENormalizedPotential

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open GOEPrefactors
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def normalizedLogMean (n : ℕ) (k : ℝ) : ℝ := Real.log (meanAbsolute n k) / (n + 1 : ℝ)

lemma normalized_log_mean_bounds (n : ℕ) {d k : ℝ} (hd : 0 < d) (hk : 2 + d ≤ k)
    (hupper : meanAbsolute n k ≤ firstPrefactor d *
      Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential k)) :
    0 ≤ normalizedLogMean n k - SemicirclePotential.potential k ∧
      normalizedLogMean n k - SemicirclePotential.potential k ≤
        Real.log (firstPrefactor d) / (n + 1 : ℝ) := by
  have hk2 : 2 < k := by linarith
  have hm : 0 < (n + 1 : ℝ) := by positivity
  have hpos := meanAbsolute_pos n hk2
  have hC : 0 < firstPrefactor d := by unfold firstPrefactor; positivity
  have hloglower := Real.log_le_log (Real.exp_pos _) (meanAbsolute_lower n hk2)
  rw [Real.log_exp] at hloglower
  have hlogupper := Real.log_le_log hpos hupper
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hlogupper
  unfold normalizedLogMean
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hm).mpr
    nlinarith
  · apply (le_div_iff₀ hm).mpr
    rw [sub_mul, div_mul_cancel₀ _ hm.ne']
    nlinarith

/-- Uniform actual first prefactors locate the normalized ordinary determinant
expectation logarithm, including for varying shifts above a fixed gap. -/
theorem normalized_log_mean_minus_potential_tendsto
    {d : ℝ} (hd : 0 < d) (k : ℕ → ℝ)
    (hk : ∀ᶠ n : ℕ in atTop, 2 + d ≤ k n) :
    Tendsto (fun n => normalizedLogMean n (k n) - SemicirclePotential.potential (k n))
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ normalizedLogMean n (k n) - SemicirclePotential.potential (k n) ∧
      normalizedLogMean n (k n) - SemicirclePotential.potential (k n) ≤
        Real.log (firstPrefactor d) / (n + 1 : ℝ) := by
    filter_upwards [meanAbsolute_upper_eventually hd, hk] with n hn hkn
    exact normalized_log_mean_bounds n hd hkn (hn (k n) hkn)
  have hm : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  exact squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
    (hm.const_div_atTop (Real.log (firstPrefactor d)))

/-- The actual normalized logarithm of the ordinary expected absolute GOE
determinant tends to the manuscript's literal Ω for every convergent shift
sequence whose limit lies above the positive edge. -/
theorem normalized_log_mean_tendsto
    (k : ℕ → ℝ) {z : ℝ} (hz : 2 < z) (hk : Tendsto k atTop (𝓝 z)) :
    Tendsto (fun n => normalizedLogMean n (k n)) atTop (𝓝 (SemicirclePotential.potential z)) := by
  let d := (z - 2) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hgap : ∀ᶠ n : ℕ in atTop, 2 + d ≤ k n := by
    have hdz : 2 + d < z := by dsimp [d]; linarith
    have hh := hk.eventually (Ioi_mem_nhds hdz)
    exact hh.mono (fun n h => (show 2 + d < k n from h).le)
  have h1 := normalized_log_mean_minus_potential_tendsto hd k hgap
  have h2 := (SemicirclePotential.potential_hasDerivAt hz).continuousAt.tendsto.comp hk
  change Tendsto (fun n => SemicirclePotential.potential (k n)) atTop
    (𝓝 (SemicirclePotential.potential z)) at h2
  convert h1.add h2 using 1
  · funext n; ring
  · simp

end
end SlowEquilibration.GOENormalizedPotential
