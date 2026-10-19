-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSStability

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology

namespace SlowEquilibration.QuadraticEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1200000

def objective {E : Type*} (a b : E → ℝ) (t : ℝ) (z : E) : ℝ :=
  t ^ 2 * a z + b z

/-- A compact, uniquely minimized quadratic parameter family obeys the envelope
derivative formula at the selected parameter. The selected minimizer need only
minimize in a neighborhood of that parameter. -/
theorem hasDerivAt_minimum {E : Type*} [TopologicalSpace E] [CompactSpace E]
    (a b : E → ℝ) (ha : Continuous a) (hb : Continuous b)
    (C : ℝ) (hC : ∀ z, |a z| ≤ C)
    (m : ℝ → E) (β : ℝ)
    (hmin : ∀ᶠ t in 𝓝 β, ∀ z, objective a b t (m t) ≤ objective a b t z)
    (hminβ : ∀ z, objective a b β (m β) ≤ objective a b β z)
    (hunique : ∀ z, objective a b β z ≤ objective a b β (m β) → z = m β) :
    HasDerivAt (fun t => objective a b t (m t)) (2 * β * a (m β)) β := by
  let F := objective a b β
  have hF : Continuous F := (ha.const_mul (β ^ 2)).add hb
  have hδ : Tendsto (fun t : ℝ => 2 * C * |t ^ 2 - β ^ 2|) (𝓝 β) (𝓝 0) := by
    have hp : Tendsto (fun t : ℝ => t ^ 2) (𝓝 β) (𝓝 (β ^ 2)) :=
      continuousAt_id.pow 2
    have hc : Tendsto (fun _ : ℝ => β ^ 2) (𝓝 β) (𝓝 (β ^ 2)) :=
      tendsto_const_nhds
    have hh : Tendsto (fun t : ℝ => t ^ 2 - β ^ 2) (𝓝 β) (𝓝 0) := by
      simpa only [sub_self] using hp.sub hc
    simpa only [abs_zero, mul_zero] using hh.abs.const_mul (2 * C)
  have hnear : ∀ᶠ t in 𝓝 β,
      F (m t) ≤ F (m β) + 2 * C * |t ^ 2 - β ^ 2| := by
    filter_upwards [hmin] with t ht
    have hc (z : E) :
        |objective a b t z - F z| ≤ C * |t ^ 2 - β ^ 2| := by
      have heq : objective a b t z - F z = (t ^ 2 - β ^ 2) * a z := by
        dsimp [objective, F]; ring
      rw [heq, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC z) (abs_nonneg _)
    have h1 := (abs_le.mp (hc (m t))).1
    have h2 := (abs_le.mp (hc (m β))).2
    have hm := ht (m β)
    dsimp [F] at *
    linarith
  have hmcont : Tendsto m (𝓝 β) (𝓝 (m β)) :=
    CSStability.approximate_minimizers_tendsto F hF (m β) hunique
      (𝓝 β) m (fun t => 2 * C * |t ^ 2 - β ^ 2|) hδ hnear
  have hacont : Tendsto (fun t => a (m t)) (𝓝 β) (𝓝 (a (m β))) :=
    (ha.tendsto (m β)).comp hmcont
  have hleft : Tendsto (fun t => (t + β) * a (m t)) (𝓝[<] β)
      (𝓝 (2 * β * a (m β))) := by
    have hs : Tendsto (fun t : ℝ => t + β) (𝓝[<] β) (𝓝 (β + β)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).add tendsto_const_nhds
    convert hs.mul (hacont.mono_left nhdsWithin_le_nhds) using 1; ring
  have hright : Tendsto (fun t => (t + β) * a (m t)) (𝓝[>] β)
      (𝓝 (2 * β * a (m β))) := by
    have hs : Tendsto (fun t : ℝ => t + β) (𝓝[>] β) (𝓝 (β + β)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).add tendsto_const_nhds
    convert hs.mul (hacont.mono_left nhdsWithin_le_nhds) using 1; ring
  have hfixedLeft : Tendsto (fun t => (t + β) * a (m β)) (𝓝[<] β)
      (𝓝 (2 * β * a (m β))) := by
    have hs : Tendsto (fun t : ℝ => t + β) (𝓝[<] β) (𝓝 (β + β)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).add tendsto_const_nhds
    convert hs.mul_const (a (m β)) using 1; ring
  have hfixedRight : Tendsto (fun t => (t + β) * a (m β)) (𝓝[>] β)
      (𝓝 (2 * β * a (m β))) := by
    have hs : Tendsto (fun t : ℝ => t + β) (𝓝[>] β) (𝓝 (β + β)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).add tendsto_const_nhds
    convert hs.mul_const (a (m β)) using 1; ring
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hfixedLeft hleft
    · filter_upwards [self_mem_nhdsWithin, hmin.filter_mono nhdsWithin_le_nhds] with t ht hmt
      have htb : t - β < 0 := sub_neg.mpr ht
      have hupp : objective a b t (m t) - objective a b β (m β) ≤
          (t ^ 2 - β ^ 2) * a (m β) := by
        have h := hmt (m β)
        dsimp [objective] at *
        nlinarith
      rw [slope_def_field]
      apply (le_div_iff_of_neg htb).2
      calc
        objective a b t (m t) - objective a b β (m β) ≤
            (t ^ 2 - β ^ 2) * a (m β) := hupp
        _ = (t + β) * a (m β) * (t - β) := by ring
    · filter_upwards [self_mem_nhdsWithin, hmin.filter_mono nhdsWithin_le_nhds] with t ht hmt
      have htb : t - β < 0 := sub_neg.mpr ht
      have hlow : (t ^ 2 - β ^ 2) * a (m t) ≤
          objective a b t (m t) - objective a b β (m β) := by
        have h := hminβ (m t)
        dsimp [objective] at *
        nlinarith
      rw [slope_def_field]
      apply (div_le_iff_of_neg htb).2
      calc
        (t + β) * a (m t) * (t - β) =
            (t ^ 2 - β ^ 2) * a (m t) := by ring
        _ ≤ objective a b t (m t) - objective a b β (m β) := hlow
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hright hfixedRight
    · filter_upwards [self_mem_nhdsWithin, hmin.filter_mono nhdsWithin_le_nhds] with t ht hmt
      have htb : 0 < t - β := sub_pos.mpr ht
      have hlow : (t ^ 2 - β ^ 2) * a (m t) ≤
          objective a b t (m t) - objective a b β (m β) := by
        have h := hminβ (m t)
        dsimp [objective] at *
        nlinarith
      rw [slope_def_field]
      apply (le_div_iff₀ htb).2
      calc
        (t + β) * a (m t) * (t - β) =
            (t ^ 2 - β ^ 2) * a (m t) := by ring
        _ ≤ objective a b t (m t) - objective a b β (m β) := hlow
    · filter_upwards [self_mem_nhdsWithin, hmin.filter_mono nhdsWithin_le_nhds] with t ht hmt
      have htb : 0 < t - β := sub_pos.mpr ht
      have hupp : objective a b t (m t) - objective a b β (m β) ≤
          (t ^ 2 - β ^ 2) * a (m β) := by
        have h := hmt (m β)
        dsimp [objective] at *
        nlinarith
      rw [slope_def_field]
      apply (div_le_iff₀ htb).2
      calc
        objective a b t (m t) - objective a b β (m β) ≤
            (t ^ 2 - β ^ 2) * a (m β) := hupp
        _ = (t + β) * a (m β) * (t - β) := by ring

end SlowEquilibration.QuadraticEnvelope
