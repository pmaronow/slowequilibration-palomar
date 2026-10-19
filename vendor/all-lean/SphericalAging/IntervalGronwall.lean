module

public import SphericalAging.VolterraUniqueness

public section

/-! Integral Gronwall on a finite interval, used independently by AC comparison. -/

open Set MeasureTheory
open scoped Topology

namespace SphericalAging.IntervalGronwall

noncomputable section

/-- Integral Gronwall for a continuous nonnegative function on its actual domain. -/
theorem integral_gronwall_zero (f : ℝ → ℝ) (T K : ℝ) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (hn : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hle : ∀ t ∈ Icc 0 T, f t ≤ K * ∫ u in 0..t, f u) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  let clamp : ℝ → ℝ := fun t => max 0 (min T t)
  let g : ℝ → ℝ := fun t => f (clamp t)
  have hgcont : Continuous g := hf.comp_continuous
    (continuous_const.max (continuous_const.min continuous_id))
    (fun t => ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩)
  have hg (t : ℝ) (ht : t ∈ Icc 0 T) : g t = f t := by
    dsimp [g, clamp]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  let F : ℝ → ℝ := fun t => ∫ u in 0..t, g u
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) : F t = ∫ u in 0..t, f u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact hg u ⟨hu.1, hu.2.trans ht.2⟩
  have hd (t : ℝ) : HasDerivAt F (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hgcont.intervalIntegrable 0 t)
      hgcont.aestronglyMeasurable.stronglyMeasurableAtFilter hgcont.continuousAt
  have hbound := le_gronwallBound_of_liminf_deriv_right_le
    (δ := 0) (K := K) (ε := 0)
    (show ContinuousOn F (Icc 0 T) from
      (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn)
    (fun t ht r hr => (hd t).hasDerivWithinAt.liminf_right_slope_le hr)
    (show F 0 ≤ 0 by simp [F])
    (fun t ht => by
      rw [hg t ⟨ht.1, ht.2.le⟩, hi t ⟨ht.1, ht.2.le⟩]
      simpa using hle t ⟨ht.1, ht.2.le⟩)
  intro t ht
  have hFt : F t ≤ 0 := by simpa only [gronwallBound_ε0_δ0] using hbound t ht
  have hFpos : 0 ≤ F t := by
    rw [hi t ht]
    exact intervalIntegral.integral_nonneg ht.1
      (fun u hu => hn u ⟨hu.1, hu.2.trans ht.2⟩)
  have hFzero : F t = 0 := le_antisymm hFt hFpos
  have hft := hle t ht
  rw [← hi t ht, hFzero, mul_zero] at hft
  exact le_antisymm hft (hn t ht)

end
end SphericalAging.IntervalGronwall
