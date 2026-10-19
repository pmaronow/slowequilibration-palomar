-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSQuadraticEnvelope

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology

namespace SlowEquilibration.CSLinearEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1200000

def objective {E : Type*} (a b : E → ℝ) (t : ℝ) (z : E) : ℝ :=
  t * a z + b z

/-- Directional envelope theorem for an actual compact minimum of an affine
parameter family. The minimizer is selected locally, with uniqueness only at
the parameter where the derivative is taken. -/
theorem hasDerivAt_minimum {E : Type*} [TopologicalSpace E] [CompactSpace E]
    (a b : E → ℝ) (ha : Continuous a) (hb : Continuous b)
    (C : ℝ) (hC : ∀ z, |a z| ≤ C)
    (m : ℝ → E) (s : ℝ)
    (hmin : ∀ᶠ t in 𝓝 s, ∀ z, objective a b t (m t) ≤ objective a b t z)
    (hmins : ∀ z, objective a b s (m s) ≤ objective a b s z)
    (hunique : ∀ z, objective a b s z ≤ objective a b s (m s) → z = m s) :
    HasDerivAt (fun t => objective a b t (m t)) (a (m s)) s := by
  let F := objective a b s
  have hF : Continuous F := (ha.const_mul s).add hb
  have hδ : Tendsto (fun t : ℝ => 2 * C * |t - s|) (𝓝 s) (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 0) := by
      have hc : Tendsto (fun _ : ℝ => s) (𝓝 s) (𝓝 s) := tendsto_const_nhds
      simpa only [id_eq, sub_self] using tendsto_id.sub hc
    simpa only [abs_zero, mul_zero] using ht.abs.const_mul (2 * C)
  have hnear : ∀ᶠ t in 𝓝 s, F (m t) ≤ F (m s) + 2 * C * |t - s| := by
    filter_upwards [hmin] with t ht
    have hc (z : E) : |objective a b t z - F z| ≤ C * |t - s| := by
      have heq : objective a b t z - F z = (t - s) * a z := by
        dsimp [objective, F]; ring
      rw [heq, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC z) (abs_nonneg _)
    have h1 := (abs_le.mp (hc (m t))).1
    have h2 := (abs_le.mp (hc (m s))).2
    have hm := ht (m s)
    dsimp [F] at *
    linarith
  have hmcont : Tendsto m (𝓝 s) (𝓝 (m s)) :=
    CSStability.approximate_minimizers_tendsto F hF (m s) hunique
      (𝓝 s) m (fun t => 2 * C * |t - s|) hδ hnear
  have hacont : Tendsto (fun t => a (m t)) (𝓝 s) (𝓝 (a (m s))) :=
    (ha.tendsto (m s)).comp hmcont
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => a (m s)) (𝓝[<] s) (𝓝 (a (m s))))
      (hacont.mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin, hmin.filter_mono nhdsWithin_le_nhds]
        with t ht hmt
      have hts : t - s < 0 := sub_neg.mpr ht
      have hupp : objective a b t (m t) - objective a b s (m s) ≤
          (t - s) * a (m s) := by
        have hh := hmt (m s)
        dsimp [objective] at *
        nlinarith
      rw [slope_def_field]
      exact (le_div_iff_of_neg hts).2 (by simpa only [mul_comm] using hupp)
    · filter_upwards [self_mem_nhdsWithin, hmin.filter_mono nhdsWithin_le_nhds]
        with t ht hmt
      have hts : t - s < 0 := sub_neg.mpr ht
      have hlow : (t - s) * a (m t) ≤
          objective a b t (m t) - objective a b s (m s) := by
        have hh := hmins (m t)
        dsimp [objective] at *
        nlinarith
      rw [slope_def_field]
      exact (div_le_iff_of_neg hts).2 (by simpa only [mul_comm] using hlow)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hacont.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => a (m s)) (𝓝[>] s) (𝓝 (a (m s))))
    · filter_upwards [self_mem_nhdsWithin, hmin.filter_mono nhdsWithin_le_nhds]
        with t ht hmt
      have hts : 0 < t - s := sub_pos.mpr ht
      have hlow : (t - s) * a (m t) ≤
          objective a b t (m t) - objective a b s (m s) := by
        have hh := hmins (m t)
        dsimp [objective] at *
        nlinarith
      rw [slope_def_field]
      exact (le_div_iff₀ hts).2 (by simpa only [mul_comm] using hlow)
    · filter_upwards [self_mem_nhdsWithin, hmin.filter_mono nhdsWithin_le_nhds]
        with t ht hmt
      have hts : 0 < t - s := sub_pos.mpr ht
      have hupp : objective a b t (m t) - objective a b s (m s) ≤
          (t - s) * a (m s) := by
        have hh := hmt (m s)
        dsimp [objective] at *
        nlinarith
      rw [slope_def_field]
      exact (div_le_iff₀ hts).2 (by simpa only [mul_comm] using hupp)

end SlowEquilibration.CSLinearEnvelope
