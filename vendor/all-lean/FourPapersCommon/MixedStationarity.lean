module
public import FourPapersCommon.MixedInsertedFunctional
public import Targets.Section4StationarityInterior
public import FourPapersCommon.WeightedEndpointMinimum

@[expose] public section

/-! Genuine mixed finite-level stationarity, with the physical overlap.
The right competitors are actual inserted and merged probability measures.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000

private theorem scheme_eq_of_fields {k : ℕ} {s t : RSBScheme k}
    (hm : s.m = t.m) (hq : s.q = t.q) : s = t := by
  cases s
  cases t
  cases hm
  cases hq
  rfl

theorem mixedSection4Phi_stationarityBase_min (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    {u : ℝ} (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    mixedSection4Phi ξ (section4StationarityBase s r hr0 hr) h (r + 1) (s.m r) (s.q r) ≤
      mixedSection4Phi ξ (section4StationarityBase s r hr0 hr) h (r + 1) (s.m r) u := by
  let b := section4StationarityBase s r hr0 hr
  have hm : s.m r ∈ Set.Icc (b.m (r + 1 - 1)) (b.m (r + 1)) := by
    simp only [b, section4StationarityBase, RSBScheme.lowerMass, Nat.add_sub_cancel,
      ite_eq_right (show r + 1 ≠ r by omega)]
    exact ⟨s.m_mono' r (by omega) (r - 1) (by omega), s.m_mono r hr⟩
  have hq : s.q r ∈ Set.Icc (b.q (r + 1 - 1)) (b.q (r + 1)) := by
    exact ⟨le_rfl, s.q_mono r (by omega)⟩
  let si (u : ℝ) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :=
    b.insertLevel (r + 1) (by omega) (by omega) (s.m r) u hm hu
  have he (u : ℝ) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
      (si u hu).m (r - 1) = (si u hu).m (r - 1 + 1) := by
    simp [si, RSBScheme.insertLevel, section4Mass, b, section4StationarityBase,
      RSBScheme.lowerMass, show r - 1 + 1 = r by omega,
      show r - 1 < r + 1 by omega, show r - 1 ≠ r by omega]
  have heq : (si (s.q r) hq).mergeEqualMass (r - 1) (by omega) (he (s.q r) hq) = s := by
    apply scheme_eq_of_fields
    · funext j
      simp only [RSBScheme.mergeEqualMass, skipLevel, si, RSBScheme.insertLevel,
        section4Mass, b, section4StationarityBase, RSBScheme.lowerMass]
      split_ifs <;> first | rfl | (congr 1; omega)
    · funext j
      simp only [RSBScheme.mergeEqualMass, skipLevel, si, RSBScheme.insertLevel,
        section5Rho, b, section4StationarityBase, RSBScheme.lowerMass]
      split_ifs <;> first | rfl | (congr 1; omega)
  have hb : mixedSection4Phi ξ b h (r + 1) (s.m r) (s.q r) = mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedFunctional_insertLevel ξ b h (r + 1) (by omega) (by omega) (s.m r) (s.q r) hm hq]
    change mixedFunctional ξ h (Paper.parisiSchemeMeasure (si (s.q r) hq)) = _
    rw [← mixedFunctional_mergeEqualMass ξ (si (s.q r) hq) (r - 1) (by omega) (he (s.q r) hq), heq]
  have H := hmin ((si u hu).mergeEqualMass (r - 1) (by omega) (he u hu))
  rw [mixedFunctional_mergeEqualMass] at H
  change mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h
    (Paper.parisiSchemeMeasure (b.insertLevel (r + 1) (by omega) (by omega) (s.m r) u hm hu)) at H
  have hu' : u ∈ Set.Icc (b.q (r + 1 - 1)) (b.q (r + 1)) := hu
  exact hb.trans_le (H.trans_eq
    (mixedFunctional_insertLevel ξ b h (r + 1) (by omega) (by omega)
      (s.m r) u hm hu'))



theorem mixedClockScheme_stationarityBase (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k) :
    mixedClockScheme ξ (section4StationarityBase s r hr0 hr) =
      section4StationarityBase (mixedClockScheme ξ s) r hr0 hr := by
  apply scheme_eq_of_fields <;> rfl

/-- Opposite stationarity, including q=0 even when ξ″(0)=0. Positivity is
used strictly inside the genuine physical competitor interval. -/
theorem mixed_endpointQ_le_overlap_of_min (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k)
    (hm : s.m (r - 1) < s.m r) (hq : s.q r < s.q (r + 1))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1)) 0 ≤ s.q r := by
  let b := section4StationarityBase s r hr0 hr
  have hmass : b.m (r + 1 - 1) = s.m (r - 1) := by
    simp [b, section4StationarityBase, RSBScheme.lowerMass]
  have hqbase : b.q = s.q := rfl
  have hm0 : s.m r ∈ Icc (0 : ℝ) 1 := ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  let Q : ℝ → ℝ := fun z => section4TVarianceQ (mixedClockScheme ξ b) (mixedBeta ξ) h
    (r + 1) (s.m r) (mixedLeftSplitVariance ξ b (r + 1) 1 z)
  have hmaps : MapsTo (mixedLeftSplitVariance ξ b (r + 1) 1)
      (Icc (s.q r) (s.q (r + 1)))
      (Icc (0 : ℝ) ((mixedBeta ξ) ^ 2 *
        ((mixedClockScheme ξ b).q (r + 1) - (mixedClockScheme ξ b).q (r + 1 - 1)))) := by
    intro z hz
    exact mixedLeftSplitVariance_mem ξ b (by omega) (t := 1) (by norm_num) hz
  have hvarcts : ContinuousOn (mixedLeftSplitVariance ξ b (r + 1) 1)
      (Icc (s.q r) (s.q (r + 1))) := by
    intro z hz
    have hz0 : z ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [s.q_nonneg (p := r) (by omega), hz.1], hz.2.trans (s.q_le_one (by omega))⟩
    have H : HasDerivAt (mixedLeftSplitVariance ξ b (r + 1) 1) (-ξ.second z) z := by
      change HasDerivAt (fun x => 1 * (ξ.first (b.q (r + 1)) - ξ.first x)) (-ξ.second z) z
      simpa only [one_mul] using (ξ.hasDerivAt_first_unit hz0).const_sub (ξ.first (b.q (r + 1)))
    exact H.continuousAt.continuousWithinAt
  have hQcts : ContinuousOn Q (Icc (s.q r) (s.q (r + 1))) :=
    (continuousOn_section4TVarianceQ_variance (mixedClockScheme ξ b) (mixedBeta ξ) h
      (r := r + 1) (by omega) (by omega) hm0).comp hvarcts hmaps
  have hd (z : ℝ) (hz : z ∈ Icc (s.q r) (s.q (r + 1))) :=
    hasDerivWithinAt_mixedSection4Phi_overlap ξ b h (r := r + 1) (by omega) (by omega)
      hm0 (hmass ▸ hm.le) hz
  have hFcts : ContinuousOn (mixedSection4Phi ξ b h (r + 1) (s.m r))
      (Icc (s.q r) (s.q (r + 1))) := fun z hz => (hd z hz).continuousWithinAt
  have H := endpointQ_le_of_weighted_minimum hq hFcts
    (hQcts (s.q r) ⟨le_rfl, hq.le⟩)
    (w := fun z => ξ.second z * (s.m r - s.m (r - 1)) / 2)
    (fun z hz => by
      have HH := (hd z ⟨hz.1.le, hz.2.le⟩).hasDerivAt (Icc_mem_nhds hz.1 hz.2)
      simpa only [hmass, Q] using HH)
    (fun z hz => div_pos (mul_pos
      (ξ.second_pos ⟨(s.q_nonneg (p := r) (by omega)).trans_lt hz.1,
        hz.2.le.trans (s.q_le_one (by omega))⟩) (sub_pos.mpr hm)) (by norm_num))
    (fun z hz => mixedSection4Phi_stationarityBase_min ξ s h hr0 hr hmin hz)
  have hv : mixedLeftSplitVariance ξ b (r + 1) 1 (s.q r) =
      (mixedBeta ξ) ^ 2 * ((mixedClockScheme ξ s).q (r + 1) - (mixedClockScheme ξ s).q r) := by
    rw [mixedLeftSplitVariance_eq_clock, one_mul]
    rfl
  change section4TVarianceQ (mixedClockScheme ξ b) (mixedBeta ξ) h (r + 1) (s.m r)
    (mixedLeftSplitVariance ξ b (r + 1) 1 (s.q r)) ≤ s.q r at H
  rw [hv, mixedClockScheme_stationarityBase] at H
  have Hend := section4TVarianceQ_stationarityBase_endpoint (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr
  simp only [mixedClockScheme_m] at Hend
  rw [Hend] at H
  exact H

theorem mixed_endpointQ_eq_overlap_of_min_nonterminal (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1)) 0 = s.q r := by
  have hQ := section4TVarianceQ_mem_Icc (mixedClockScheme ξ s) (mixedBeta ξ) h r
    (m := s.m (r - 1)) ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ 0
  apply le_antisymm
  · rcases hright with hh | hh
    · exact mixed_endpointQ_le_overlap_of_min ξ s h hr0 hr hm hh hmin
    · simpa only [hh] using hQ.2
  · rcases hleft with hh | hh
    · exact mixed_overlap_le_endpointQ_of_min ξ s h hr0 (by omega) hm hh hmin
    · simpa only [hh] using hQ.1

end FourPapersCommon
