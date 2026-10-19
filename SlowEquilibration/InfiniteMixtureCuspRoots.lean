-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.RealAnalyticCuspNormalForm
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The rightmost maximizer gives a strict compact gap on every interval
strictly to its right; no uniqueness of the global maximizer is assumed. -/
theorem A_right_compact_gap (μ : InfiniteMixture) {r : ℝ}
    (hr : μ.qD < r) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc r 1, μ.A s ≤ μ.Amax - δ := by
  have hc : ContinuousOn μ.A (Icc r 1) := μ.continuousOn_A.mono
    (fun s hs => ⟨by linarith [hs.1],hs.2⟩)
  obtain ⟨z,hz,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hr1) hc
  have hlt : μ.A z < μ.Amax := by
    apply lt_of_le_of_ne (μ.A_le_Amax_closed ⟨hr0.trans hz.1,hz.2⟩)
    intro he
    have hmax : z ∈ μ.globalMaximizers := ⟨⟨hr0.trans hz.1,hz.2⟩,he⟩
    have hh := μ.globalMaximizer_le_qD hmax
    linarith [hz.1]
  refine ⟨μ.Amax - μ.A z,sub_pos.mpr hlt,fun s hs => ?_⟩
  calc
    μ.A s ≤ μ.A z := hm hs
    _ = μ.Amax - (μ.Amax - μ.A z) := by ring

/-- Concrete local coordinates for the source cusp, with a proved strictly
increasing inverse and a physical interval contained in `(0,1)`. -/
structure CuspCoordinate (μ : InfiniteMixture) where
  m : ℕ
  a : ℝ
  g : ℝ → ℝ
  radius : ℝ
  m_pos : 1 ≤ m
  a_pos : 0 < a
  radius_pos : 0 < radius
  analytic : AnalyticAt ℝ g 0
  zero : g 0 = 0
  derivative : HasDerivAt g 1 0
  remainder : (fun t : ℝ => g t - t) =O[𝓝 (0 : ℝ)] (fun t => t ^ 2)
  continuous : ContinuousOn g (Icc (-radius) radius)
  monotone : StrictMonoOn g (Icc (-radius) radius)
  interior : ∀ t ∈ Icc (-radius) radius, μ.qD + g t ∈ Ioo (0 : ℝ) 1
  normal : ∀ t ∈ Icc (-radius) radius,
    μ.A (μ.qD + g t) = μ.Amax / (1 + a * t ^ (2 * m))

/-- The coordinate data are derived from the actual source analytic contact. -/
theorem exists_cuspCoordinate (μ : InfiniteMixture)
    (hgap : Thresholds.dynamicalThreshold μ.xi < Thresholds.staticThreshold μ.xi) :
    Nonempty (CuspCoordinate μ) := by
  obtain ⟨m,a,g,hm,ha,hg,hg0,hgd,hO,hform⟩ := μ.qD_rational_normal_form hgap
  have hder : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < deriv g t :=
    hg.deriv.continuousAt.eventually (lt_mem_nhds (by rw [hgd.deriv]; norm_num))
  have hqi : μ.qD + g 0 ∈ Ioo (0 : ℝ) 1 := by
    simpa only [hg0,add_zero] using μ.qD_mem_interior hgap
  have hqi' : ∀ᶠ t in 𝓝 (0 : ℝ), μ.qD + g t ∈ Ioo (0 : ℝ) 1 :=
    (continuousAt_const.add hg.continuousAt).eventually (isOpen_Ioo.mem_nhds hqi)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp
    (hg.eventually_analyticAt.and (hder.and (hqi'.and hform)))
  let ρ : ℝ := δ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsub (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : dist t 0 < δ := by
    rw [Real.dist_eq,sub_zero]
    have hab : |t| ≤ ρ := abs_le.mpr ht
    dsimp [ρ] at hab
    linarith
  have hcont : ContinuousOn g (Icc (-ρ) ρ) :=
    fun t ht => (hd (hsub t ht)).1.continuousAt.continuousWithinAt
  refine ⟨⟨m,a,g,ρ,hm,ha,hρ,hg,hg0,hgd,hO,hcont,?_,?_,?_⟩⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro t ht
    exact (hd (hsub t (interior_subset ht))).2.1
  · intro t ht
    exact (hd (hsub t ht)).2.2.1
  · intro t ht
    exact (hd (hsub t ht)).2.2.2

namespace CuspCoordinate
variable {μ : InfiniteMixture} (c : CuspCoordinate μ)

def leftRoot (h : ℝ) : ℝ := μ.qD + c.g (-h)
def rightRoot (h : ℝ) : ℝ := μ.qD + c.g h

theorem left_lt_qD {h : ℝ} (hh : 0 < h) (hr : h ≤ c.radius) :
    c.leftRoot h < μ.qD := by
  have hg := c.monotone (show -h ∈ Icc (-c.radius) c.radius by constructor <;> linarith)
    (show (0 : ℝ) ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])
    (by linarith : -h < 0)
  rw [c.zero] at hg
  dsimp [leftRoot]
  linarith

theorem qD_lt_right {h : ℝ} (hh : 0 < h) (hr : h ≤ c.radius) :
    μ.qD < c.rightRoot h := by
  have hg := c.monotone
    (show (0 : ℝ) ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])
    (show h ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos]) hh
  rw [c.zero] at hg
  dsimp [rightRoot]
  linarith

theorem roots_interior {h : ℝ} (hh : 0 ≤ h) (hr : h ≤ c.radius) :
    c.leftRoot h ∈ Ioo (0 : ℝ) 1 ∧ c.rightRoot h ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact c.interior (-h) (by constructor <;> linarith [c.radius_pos])
  · exact c.interior h (by constructor <;> linarith [c.radius_pos])

theorem roots_level {h : ℝ} (hh : 0 ≤ h) (hr : h ≤ c.radius) :
    μ.A (c.leftRoot h) = μ.Amax / (1 + c.a * h ^ (2 * c.m)) ∧
    μ.A (c.rightRoot h) = μ.Amax / (1 + c.a * h ^ (2 * c.m)) := by
  constructor
  · have ht : -h ∈ Icc (-c.radius) c.radius := by constructor <;> linarith [c.radius_pos]
    have hn := c.normal (-h) ht
    have hp : (-h) ^ (2 * c.m) = h ^ (2 * c.m) := Even.neg_pow (even_two_mul c.m) h
    simpa only [leftRoot, hp] using hn
  · exact c.normal h (by constructor <;> linarith [c.radius_pos])

theorem rightRoot_remainder :
    (fun h : ℝ => c.rightRoot h - (μ.qD + h)) =O[𝓝 (0 : ℝ)] (fun h => h ^ 2) := by
  simpa only [rightRoot,add_sub_add_left_eq_sub] using c.remainder

theorem leftRoot_remainder :
    (fun h : ℝ => c.leftRoot h - (μ.qD - h)) =O[𝓝 (0 : ℝ)] (fun h => h ^ 2) := by
  have h := c.remainder.comp_tendsto (show Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) by
    simpa only [neg_zero, id_eq] using (tendsto_id.neg : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 (-0))))
  simpa only [leftRoot,Function.comp_def,neg_sq,sub_neg_eq_add,
    show ∀ h : ℝ, μ.qD + c.g (-h) - (μ.qD - h) = c.g (-h) + h by intro h; ring] using h

theorem coordinate_superlevel_iff {h β t : ℝ} (hh : 0 ≤ h)
    (hβ : β ^ 2 * μ.Amax = 1 + c.a * h ^ (2 * c.m))
    (ht : t ∈ Icc (-c.radius) c.radius) :
    μ.qD + c.g t ∈ Thresholds.plateauSuperlevel μ.xi β ↔ |t| < h := by
  have hden : 0 < 1 + c.a * t ^ (2 * c.m) := by
    have hp : 0 ≤ t ^ (2 * c.m) := by rw [pow_mul]; positivity
    nlinarith [c.a_pos]
  have hk : 2 * c.m ≠ 0 := by have := c.m_pos; omega
  have hqi := c.interior t ht
  change (μ.qD + c.g t ∈ Ioo (0 : ℝ) 1 ∧
    1 < β ^ 2 * Thresholds.A μ.xi (μ.qD + c.g t)) ↔ _
  rw [and_iff_right hqi, ← μ.A_eq_threshold hqi, c.normal t ht,
    ← mul_div_assoc, hβ, lt_div_iff₀ hden, one_mul]
  have he : (1 + c.a * t ^ (2 * c.m) < 1 + c.a * h ^ (2 * c.m)) ↔
      t ^ (2 * c.m) < h ^ (2 * c.m) := by
    rw [add_lt_add_iff_left, mul_lt_mul_iff_right₀ c.a_pos]
  rw [he, ← pow_abs_two_mul, pow_lt_pow_iff_left₀ (abs_nonneg t) hh hk]

theorem mem_coordinate_image {r : ℝ}
    (hr : r ∈ Icc (c.leftRoot c.radius) (c.rightRoot c.radius)) :
    ∃ t ∈ Icc (-c.radius) c.radius, r = μ.qD + c.g t := by
  have hmem : r - μ.qD ∈ Icc (c.g (-c.radius)) (c.g c.radius) := by
    rcases hr with ⟨hr1,hr2⟩
    dsimp [leftRoot,rightRoot] at hr1 hr2
    constructor <;> linarith
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by linarith [c.radius_pos] :
    -c.radius ≤ c.radius) c.continuous hmem
  exact ⟨t,ht,by linarith⟩

/-- On the actual fixed neighborhood, the strict superlevel set is exactly
the interval between the two constructed roots. -/
theorem local_superlevel_iff {h β r : ℝ} (hh : 0 < h) (hr : h ≤ c.radius)
    (hβ : β ^ 2 * μ.Amax = 1 + c.a * h ^ (2 * c.m))
    (hrange : r ∈ Icc (c.leftRoot c.radius) (c.rightRoot c.radius)) :
    r ∈ Thresholds.plateauSuperlevel μ.xi β ↔ r ∈ Ioo (c.leftRoot h) (c.rightRoot h) := by
  obtain ⟨t,ht,rfl⟩ := c.mem_coordinate_image hrange
  rw [c.coordinate_superlevel_iff hh.le hβ ht, abs_lt]
  have hminus : -h ∈ Icc (-c.radius) c.radius := by constructor <;> linarith [c.radius_pos]
  have hplus : h ∈ Icc (-c.radius) c.radius := by constructor <;> linarith [c.radius_pos]
  simp only [mem_Ioo, leftRoot, rightRoot, add_lt_add_iff_left,
    c.monotone.lt_iff_lt hminus ht, c.monotone.lt_iff_lt ht hplus]

/-- Once the compact right gap excludes further components, the literal
supremum defining `qStar` equals the constructed right root. -/
theorem qStar_eq_rightRoot_of_cutoff {h β : ℝ} (hh : 0 < h) (hr : h < c.radius)
    (hβ : β ^ 2 * μ.Amax = 1 + c.a * h ^ (2 * c.m))
    (hcut : ∀ r ∈ Icc (c.rightRoot c.radius) 1, β ^ 2 * μ.A r ≤ 1) :
    Thresholds.qStar μ.xi β = c.rightRoot h := by
  have hl := c.left_lt_qD hh hr.le
  have hu := c.qD_lt_right hh hr.le
  have houterL := c.left_lt_qD c.radius_pos le_rfl
  have houterR := c.qD_lt_right c.radius_pos le_rfl
  have hleft_le : c.leftRoot c.radius ≤ c.leftRoot h := by
    dsimp [leftRoot]
    apply add_le_add le_rfl
    exact c.monotone.monotoneOn
      (show -c.radius ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])
      (show -h ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])
      (by linarith)
  have hright_le : c.rightRoot h ≤ c.rightRoot c.radius := by
    dsimp [rightRoot]
    apply add_le_add le_rfl
    exact c.monotone.monotoneOn
      (show h ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])
      (show c.radius ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos]) hr.le
  have hsubset : Ioo (c.leftRoot h) (c.rightRoot h) ⊆ Thresholds.plateauSuperlevel μ.xi β := by
    intro r hrange
    apply (c.local_superlevel_iff hh hr.le hβ ?_).mpr hrange
    exact ⟨hleft_le.trans hrange.1.le,hrange.2.le.trans hright_le⟩
  have hne : (Thresholds.plateauSuperlevel μ.xi β).Nonempty :=
    ⟨μ.qD,hsubset ⟨hl,hu⟩⟩
  have hbound : ∀ r ∈ Thresholds.plateauSuperlevel μ.xi β, r ≤ c.rightRoot h := by
    intro r hrD
    by_cases hbelow : r ≤ c.leftRoot c.radius
    · exact hbelow.trans (hleft_le.trans (by linarith))
    by_cases hfar : c.rightRoot c.radius ≤ r
    · have hphys := hrD.1
      have hupper := hcut r ⟨hfar,hphys.2.le⟩
      rw [μ.A_eq_threshold hphys] at hupper
      exact False.elim (not_lt_of_ge hupper hrD.2)
    · exact ((c.local_superlevel_iff hh hr.le hβ ⟨le_of_not_ge hbelow,le_of_not_ge hfar⟩).mp hrD).2.le
  have hbdd : BddAbove (Thresholds.plateauSuperlevel μ.xi β) := ⟨c.rightRoot h,hbound⟩
  unfold Thresholds.qStar
  apply le_antisymm (csSup_le hne hbound)
  have hsup : sSup (Ioo (c.leftRoot h) (c.rightRoot h)) = c.rightRoot h :=
    csSup_Ioo (hl.trans hu)
  rw [← hsup]
  exact csSup_le_csSup hbdd (nonempty_Ioo.mpr (hl.trans hu)) hsubset

/-- The actual inverse temperature parametrized by the positive root scale. -/
def temperature (h : ℝ) : ℝ :=
  Thresholds.dynamicalThreshold μ.xi * Real.sqrt (1 + c.a * h ^ (2 * c.m))

theorem temperature_sq (h : ℝ) :
    c.temperature h ^ 2 * μ.Amax = 1 + c.a * h ^ (2 * c.m) := by
  have hp : 0 ≤ h ^ (2 * c.m) := by rw [pow_mul]; positivity
  have hden : 0 ≤ 1 + c.a * h ^ (2 * c.m) := by nlinarith [c.a_pos]
  rw [temperature,mul_pow,μ.dynamicalThreshold_sq,Real.sq_sqrt hden]
  field_simp [μ.Amax_pos.ne']

/-- Compact maximality excludes every superlevel component farther to the
right for all sufficiently small positive root scales. -/
theorem right_cutoff_eventually :
    ∀ᶠ h in 𝓝 (0 : ℝ), ∀ r ∈ Icc (c.rightRoot c.radius) 1,
      c.temperature h ^ 2 * μ.A r ≤ 1 := by
  have hri := (c.roots_interior c.radius_pos.le le_rfl).2
  obtain ⟨δ,hδ,hbound⟩ := μ.A_right_compact_gap
    (c.qD_lt_right c.radius_pos le_rfl) hri.1.le hri.2.le
  let p : ℝ → ℝ := fun h => ((1 + c.a * h ^ (2 * c.m)) / μ.Amax) * (μ.Amax - δ)
  have hpc : ContinuousAt p 0 := by unfold p; fun_prop
  have hp0 : p 0 < 1 := by
    have hk : 2 * c.m ≠ 0 := by have := c.m_pos; omega
    simp only [p,zero_pow hk,mul_zero,add_zero]
    rw [one_div_mul_eq_div,div_lt_one μ.Amax_pos]
    linarith
  have hpe := hpc.eventually (gt_mem_nhds hp0)
  filter_upwards [hpe] with h hh r hr
  have hβ : c.temperature h ^ 2 = (1 + c.a * h ^ (2 * c.m)) / μ.Amax :=
    (eq_div_iff μ.Amax_pos.ne').mpr (c.temperature_sq h)
  calc
    _ ≤ c.temperature h ^ 2 * (μ.Amax - δ) :=
      mul_le_mul_of_nonneg_left (hbound r hr) (sq_nonneg _)
    _ = p h := by rw [hβ]
    _ ≤ 1 := hh.le

/-- The literal source `qStar` is the right local branch for all small
positive inverse-temperature deviations. -/
theorem qStar_eq_rightRoot_eventually :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Thresholds.qStar μ.xi (c.temperature h) = c.rightRoot h := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds c.radius_pos),
    eventually_nhdsWithin_of_eventually_nhds c.right_cutoff_eventually] with h hh hr hc
  exact c.qStar_eq_rightRoot_of_cutoff hh hr (c.temperature_sq h) hc

theorem qStar_remainder :
    (fun h : ℝ => Thresholds.qStar μ.xi (c.temperature h) - (μ.qD + h))
      =O[𝓝[>] (0 : ℝ)] (fun h => h ^ 2) := by
  apply (c.rightRoot_remainder.mono nhdsWithin_le_nhds).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [c.qStar_eq_rightRoot_eventually] with h hh
  rw [hh]

end CuspCoordinate
end SlowEquilibration.InfiniteMixture
