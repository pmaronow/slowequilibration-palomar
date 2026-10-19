-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.StrongFieldGlobal

@[expose] public section

/-! Exact strong-field radial-score localization follows from the genuine
whole-line semicircle exponent and its two-point zero classification. -/

namespace SlowEquilibration.StrongFieldComplexity
noncomputable section
open Set
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_compact_exponent_gap_away_endpoints {a b variance : ℝ}
    (hb : 0<b) (hab : b<a) (hv : 0<variance) {K : Set (ℝ×ℝ)} (hK : IsCompact K)
    (hpos : (Real.sqrt a,radialEndpoint a b)∉K)
    (hneg : (-Real.sqrt a,-radialEndpoint a b)∉K) :
    ∃ η : ℝ,0<η ∧ ∀ z∈K,exponent a b variance z.1 z.2≤-η := by
  by_cases hne : K.Nonempty
  · obtain ⟨z,hz,hmax⟩ := hK.exists_isMaxOn hne (exponent_continuous a b variance).continuousOn
    have hle := exponent_nonpos_global hb hab hv z.1 z.2
    have hs : exponent a b variance z.1 z.2<0 := by
      apply lt_of_le_of_ne hle
      intro heq
      rcases (exponent_eq_zero_iff_global hb hab hv z.1 z.2).mp heq with h | h
      · apply hpos
        simpa only [← h.1,← h.2,Prod.eta] using hz
      · apply hneg
        simpa only [← h.1,← h.2,Prod.eta] using hz
    refine ⟨-exponent a b variance z.1 z.2/2,by linarith,?_⟩
    intro w hw
    have hm : exponent a b variance w.1 w.2≤exponent a b variance z.1 z.2 := hmax hw
    linarith
  · exact ⟨1,by norm_num,fun z hz => (hne ⟨z,hz⟩).elim⟩

/-- On a bounded nonnegative-height window, all radial scores outside any
fixed open neighborhood of the positive endpoint have a strict exponent gap. -/
theorem exists_compact_positive_radial_gap {a b variance : ℝ}
    (hb : 0<b) (hab : b<a) (hv : 0<variance) (H Z : ℝ) {δ : ℝ} (hδ : 0<δ) :
    ∃ η : ℝ,0<η ∧ ∀ h∈Icc (0 : ℝ) H,∀ k∈Icc (-Z) Z,
      δ≤|k-radialEndpoint a b| → exponent a b variance h k≤-η := by
  let K : Set (ℝ×ℝ) := (Icc (0 : ℝ) H ×ˢ Icc (-Z) Z)∩
    {z | δ≤|z.2-radialEndpoint a b|}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const ((continuous_snd.sub continuous_const).abs))
  have hpos : (Real.sqrt a,radialEndpoint a b)∉K := by
    rintro ⟨_,he⟩
    have hh : δ≤0 := by simpa using he
    linarith
  have hneg : (-Real.sqrt a,-radialEndpoint a b)∉K := by
    rintro ⟨⟨hh,_⟩,_⟩
    have ha := Real.sqrt_pos.mpr (hb.trans hab)
    have h0 : 0≤-Real.sqrt a := hh.1
    linarith
  obtain ⟨η,hη,hgap⟩ := exists_compact_exponent_gap_away_endpoints hb hab hv hK hpos hneg
  exact ⟨η,hη,fun h hh k hk hd => hgap (h,k) ⟨⟨hh,hk⟩,hd⟩⟩

end
end SlowEquilibration.StrongFieldComplexity
