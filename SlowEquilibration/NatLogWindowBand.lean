-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.NatLogWindowScales

@[expose] public section
namespace SlowEquilibration.NatLogWindowScales
noncomputable section
open Filter
open scoped Topology

theorem log_window_inside_band_eventually (D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,D*Real.log (n+2 : ℕ)+1 ≤ (n+2 : ℕ)*δ := by
  have ht : Tendsto (fun n : ℕ => (D*Real.log (n+2 : ℕ)+1)/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    have hh := ((log_power_div_dimension_tendsto_zero 1).const_mul D).add
      (log_power_div_dimension_tendsto_zero 0)
    simpa only [pow_one,pow_zero,mul_zero,zero_add,add_div,mul_div_assoc] using hh
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  exact (div_lt_iff₀ hN).mp hn |>.le.trans_eq (mul_comm _ _)

end
end SlowEquilibration.NatLogWindowScales
