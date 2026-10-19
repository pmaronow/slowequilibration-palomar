-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedTailMonotonic

/-! A fixed-window selected-count limit plus the unselected upper-tail
limit gives the selected upper-tail limit by positivity and monotonicity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 350000

theorem retained_tail_tendsto_of_window_limits
    (b t : ℝ) (hb : 0 < b)
    (A B : ℕ → ℝ) (W : ℝ → ℕ → ℝ)
    (hupper : Tendsto B atTop (𝓝 (Real.exp (-b*t))))
    (hwindow : ∀ R : ℝ, t ≤ R →
      Tendsto (W R) atTop
        (𝓝 (Real.exp (-b*t)-Real.exp (-b*R))))
    (hbound : ∀ n : ℕ, ∀ R : ℝ, t ≤ R → W R n ≤ A n ∧ A n ≤ B n) :
    Tendsto A atTop (𝓝 (Real.exp (-b*t))) := by
  have hdecay : Tendsto (fun R : ℝ => Real.exp (-b*R)) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hb))
  apply tendsto_order.2
  constructor
  · intro r hr
    have hsmall : ∀ᶠ R : ℝ in atTop,
        Real.exp (-b*R) < Real.exp (-b*t)-r :=
      hdecay.eventually (gt_mem_nhds (sub_pos.mpr hr))
    obtain ⟨R,hRge,hRsmall⟩ :=
      ((eventually_ge_atTop t).and hsmall).exists
    have hWin : ∀ᶠ n : ℕ in atTop, r < W R n :=
      (hwindow R hRge).eventually
        (eventually_gt_nhds (by linarith : r < Real.exp (-b*t)-Real.exp (-b*R)))
    filter_upwards [hWin] with n hn
    exact hn.trans_le (hbound n R hRge).1
  · intro r hr
    filter_upwards [hupper.eventually (gt_mem_nhds hr)] with n hn
    exact (hbound n t le_rfl).2.trans_lt hn

end SlowEquilibration.PairConditionalDeterminantMoments
