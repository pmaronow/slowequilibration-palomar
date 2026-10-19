-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCompactTailCenter

/-! Stronger compact-support tail centering: integrability and positivity on
the interior suffice; the mark-truncated intensity itself need not be
continuous at the mark endpoints or inside the interval. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000

/-- A nonnegative integrable density which is positive at every interior
point has a strictly decreasing upper tail there, without differentiating
the density or assuming its continuity. -/
theorem tail_strictAntiOn_of_pos {f : ℝ → ℝ} (hi : Integrable f)
    (hf : ∀ H : ℝ, 0 ≤ f H)
    {l r : ℝ} (hp : ∀ H ∈ Ioo l r, 0 < f H) :
    StrictAntiOn (tail f) (Ioo l r) := by
  intro x hx y hy hxy
  have hIntegral : 0 < ∫ z in Ioc x y, f z := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (fun z => hf z))
      (hi.integrableOn (s := Ioc x y))).mpr
    have hsubset : Ioo x y ⊆ Function.support f ∩ Ioc x y := by
      intro z hz
      have hzMark : z ∈ Ioo l r := ⟨hx.1.trans hz.1,hz.2.trans hy.2⟩
      have hPos := hp z hzMark
      exact ⟨by simpa [Function.mem_support] using hPos.ne',⟨hz.1,hz.2.le⟩⟩
    have hVol : 0 < volume (Ioo x y) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)
    exact hVol.trans_le (measure_mono hsubset)
  have hDiff := intervalIntegral.integral_Ici_sub_Ici'
    (hi.integrableOn (s := Ici x)) (hi.integrableOn (s := Ici y))
  change tail f x-tail f y=∫ z in x..y,f z at hDiff
  rw [intervalIntegral.integral_of_le hxy.le] at hDiff
  linarith

/-- A strict finite bracket gives a globally unique tail-equals-one center
for a nonnegative integrable mark-truncated density, even if it jumps at
the interval boundary. -/
theorem exists_unique_normalized_center_compact_support_no_continuity {f : ℝ → ℝ}
    (hi : Integrable f) (hf : ∀ H : ℝ, 0 ≤ f H)
    {l r : ℝ} (hlr : l < r)
    (hp : ∀ H ∈ Ioo l r, 0 < f H)
    (hl : 1 < tail f l) (hr : tail f r < 1) :
    ∃! m : ℝ, tail f m=1 ∧ m ∈ Ioo l r := by
  have hTailCont := tail_continuous_of_integrable hi
  have hIVT := intermediate_value_Icc' hlr.le hTailCont.continuousOn
  obtain ⟨m,hm,he⟩ := hIVT ⟨hr.le,hl.le⟩
  have hMem : m ∈ Ioo l r := by
    constructor
    · rcases hm.1.eq_or_lt with hEq | hLt
      · subst m
        linarith
      · exact hLt
    · rcases hm.2.eq_or_lt with hEq | hLt
      · subst m
        linarith
      · exact hLt
  have hAnti := tail_antitone_of_nonneg hi hf
  have hStrict := tail_strictAntiOn_of_pos hi hf hp
  refine ⟨m,⟨he,hMem⟩,?_⟩
  intro y hy
  have hyMem : y ∈ Ioo l r := by
    constructor
    · by_contra hNot
      have hle : y ≤ l := le_of_not_gt hNot
      have hh := hAnti hle
      rw [hy.1] at hh
      linarith
    · by_contra hNot
      have hle : r ≤ y := le_of_not_gt hNot
      have hh := hAnti hle
      rw [hy.1] at hh
      linarith
  exact hStrict.injOn hyMem hMem (hy.1.trans he.symm)

end SlowEquilibration.ExpectedTailCentering
