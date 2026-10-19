-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalBadCriticalCountPartition

/-! A vanishing-bad-count criterion from two matching finite first moments.
This is the precise probability step needed for the source pure high-Hessian
claim once the critical and negative-Hessian means are identified. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Filter MeasureTheory
open scoped ENNReal Topology
set_option autoImplicit false

theorem bad_probability_tendsto_zero_of_matching_means
    (A B C P : ℕ → ℝ≥0∞) (limit : ℝ)
    (hfinite : ∀ᶠ n : ℕ in atTop, C n < ⊤)
    (hpartition : ∀ n, A n+B n=C n)
    (hA : Tendsto (fun n => (A n).toReal) atTop (𝓝 limit))
    (hC : Tendsto (fun n => (C n).toReal) atTop (𝓝 limit))
    (hprob : ∀ n, P n ≤ B n) :
    Tendsto (fun n => (P n).toReal) atTop (𝓝 (0 : ℝ)) := by
  have hB : Tendsto (fun n => (B n).toReal) atTop (𝓝 (0 : ℝ)) := by
    have heq : (fun n => (B n).toReal) =ᶠ[atTop]
        (fun n => (C n).toReal-(A n).toReal) := by
      filter_upwards [hfinite] with n hn
      have hAn : A n ≠ ⊤ := by
        intro hh
        have hp := hpartition n
        rw [hh,top_add] at hp
        exact hn.ne hp.symm
      have hBn : B n ≠ ⊤ := by
        intro hh
        have hp := hpartition n
        rw [hh,add_top] at hp
        exact hn.ne hp.symm
      have hsum := ENNReal.toReal_add hAn hBn
      rw [hpartition n] at hsum
      linarith
    have hsub : Tendsto (fun n => (C n).toReal-(A n).toReal) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using hC.sub hA
    exact hsub.congr' heq.symm
  apply tendsto_order.2
  constructor
  · intro r hr
    filter_upwards [] with n
    exact hr.trans_le ENNReal.toReal_nonneg
  · intro r hr
    have hb : ∀ᶠ n : ℕ in atTop, (B n).toReal < r :=
      hB.eventually (gt_mem_nhds hr)
    filter_upwards [hfinite,hb] with n hn hbn
    have hBn : B n ≠ ⊤ := by
      intro hh
      have hp := hpartition n
      rw [hh,add_top] at hp
      exact hn.ne hp.symm
    exact (ENNReal.toReal_mono hBn (hprob n)).trans_lt hbn

end SlowEquilibration.SphericalMarkedWindows
