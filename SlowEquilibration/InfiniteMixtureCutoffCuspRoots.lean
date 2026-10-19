-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCutoffDynamical
public import SlowEquilibration.InfiniteMixtureCuspEpsilon

/-! Stability of the actual rightmost superlevel endpoint under the source
nonnegative cutoff. The inclusion of cutoff superlevel sets makes the result
valid even when the limiting function has other tangencies. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (μ : InfiniteMixture)

theorem basedCutoff_plateauSuperlevel_subset (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    (n : ℕ) (β : ℝ) :
    Thresholds.plateauSuperlevel (μ.basedCutoff P₀ h₀ n).xi β ⊆
      Thresholds.plateauSuperlevel μ.xi β := by
  intro r hr
  exact ⟨hr.1,hr.2.trans_le (mul_le_mul_of_nonneg_left
    (μ.finiteCutoff_A_le _ _ hr.1) (sq_nonneg β))⟩

theorem basedCutoff_mem_plateauSuperlevel_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    {β r : ℝ} (hr : r ∈ Thresholds.plateauSuperlevel μ.xi β) :
    ∀ᶠ n in atTop, r ∈ Thresholds.plateauSuperlevel (μ.basedCutoff P₀ h₀ n).xi β := by
  have h := ((μ.basedCutoff_A_tendsto P₀ h₀ hr.1).const_mul (β^2)).eventually
    (Ioi_mem_nhds hr.2)
  exact h.mono (fun _ hn => ⟨hr.1,hn⟩)

/-- The literal supremum endpoint converges whenever the actual superlevel
set is nonempty; no root uniqueness or nondegeneracy is needed. -/
theorem basedCutoff_qStar_tendsto (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) (β : ℝ)
    (hne : (Thresholds.plateauSuperlevel μ.xi β).Nonempty) :
    Tendsto (fun n => Thresholds.qStar (μ.basedCutoff P₀ h₀ n).xi β)
      atTop (𝓝 (Thresholds.qStar μ.xi β)) := by
  have hbdd (ξ : ℝ → ℝ) : BddAbove (Thresholds.plateauSuperlevel ξ β) :=
    ⟨1,fun r hr => hr.1.2.le⟩
  obtain ⟨r₀,hr₀⟩ := hne
  have hneEventually : ∀ᶠ n in atTop,
      (Thresholds.plateauSuperlevel (μ.basedCutoff P₀ h₀ n).xi β).Nonempty :=
    (μ.basedCutoff_mem_plateauSuperlevel_eventually P₀ h₀ hr₀).mono
      (fun _ hn => ⟨r₀,hn⟩)
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨r,hr,hbr⟩ := exists_lt_of_lt_csSup ⟨r₀,hr₀⟩ hb
    filter_upwards [μ.basedCutoff_mem_plateauSuperlevel_eventually P₀ h₀ hr] with n hn
    exact hbr.trans_le (le_csSup (hbdd _) hn)
  · intro b hb
    filter_upwards [hneEventually] with n hn
    apply lt_of_le_of_lt _ hb
    apply csSup_le hn
    intro r hr
    exact le_csSup (hbdd μ.xi) (μ.basedCutoff_plateauSuperlevel_subset P₀ h₀ n β hr)

/-- Every fixed strictly intermediate temperature is eventually valid for
all the genuine finite models, with the static side valid for every cutoff. -/
theorem basedCutoff_temperature_window_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    {β : ℝ} (hd : Thresholds.dynamicalThreshold μ.xi < β)
    (hs : β < Thresholds.staticThreshold μ.xi) :
    ∀ᶠ n in atTop,
      Thresholds.dynamicalThreshold (μ.basedCutoff P₀ h₀ n).xi < β ∧
      β < Thresholds.staticThreshold (μ.basedCutoff P₀ h₀ n).xi := by
  filter_upwards [(μ.basedCutoff_dynamicalThreshold_tendsto P₀ h₀).eventually
    (Iio_mem_nhds hd)] with n hn
  exact ⟨hn,hs.trans_le (μ.staticThreshold_le_finiteCutoff _ _)⟩

namespace CuspCoordinate
variable {μ} (c : CuspCoordinate μ)

/-- At every sufficiently small fixed source epsilon, the genuine finite
cutoff `qStar` converges to the actual constructed right cusp root. -/
theorem basedCutoff_qStar_tendsto_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      Tendsto (fun n => Thresholds.qStar (μ.basedCutoff P₀ h₀ n).xi
        (c.epsilonTemperature ε)) atTop (𝓝 (c.qPlus ε)) := by
  filter_upwards [c.epsilon_roots_eventually] with ε he
  have hne : (Thresholds.plateauSuperlevel μ.xi (c.epsilonTemperature ε)).Nonempty := by
    by_contra hn
    have hempty := Set.not_nonempty_iff_eq_empty.mp hn
    have hz : Thresholds.qStar μ.xi (c.epsilonTemperature ε) = 0 := by
      rw [Thresholds.qStar,hempty,Real.sSup_empty]
    have hq := he.2.2.2.2.2.2
    have hp := he.2.2.2.1.1
    linarith
  simpa only [he.2.2.2.2.2.2] using
    μ.basedCutoff_qStar_tendsto P₀ h₀ (c.epsilonTemperature ε) hne

end CuspCoordinate
end SlowEquilibration.InfiniteMixture
