module
public import FourPapersCommon.MixedStationarity
public import Targets.Section4StationarityTerminal

@[expose] public section

/-! Genuine mixed terminal stationarity through actual inserted and merged
probability measures. The derivative weight may vanish at overlap zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000

private theorem terminal_scheme_eq_of_fields {k : ℕ} {s t : RSBScheme k}
    (hm : s.m = t.m) (hq : s.q = t.q) : s = t := by
  cases s
  cases t
  cases hm
  cases hq
  rfl

/-- Inserting mass one into the auxiliary base gives a genuine same-level
competitor after an exact equal-mass merge. -/
theorem mixedSection4Phi_terminalBase_min {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    {u : ℝ} (hu : u ∈ Set.Icc (s.q k) 1) :
    mixedSection4Phi ξ (section4TerminalBase s) h (k + 1) 1 (s.q (k + 1)) ≤
      mixedSection4Phi ξ (section4TerminalBase s) h (k + 1) 1 u := by
  let b := section4TerminalBase s
  have hm : (1 : ℝ) ∈ Set.Icc (b.m (k + 1 - 1)) (b.m (k + 1)) :=
    ⟨s.m_le_one (by omega), s.m_top.ge⟩
  have hq (u : ℝ) (hu : u ∈ Set.Icc (s.q k) 1) :
      u ∈ Set.Icc (b.q (k + 1 - 1)) (b.q (k + 1)) := by
    simpa [b, section4TerminalBase, show k ≠ k + 1 by omega] using hu
  have hq0 : s.q (k + 1) ∈ Set.Icc (s.q k) 1 :=
    ⟨s.q_mono k (by omega), s.q_le_one (by omega)⟩
  let si (u : ℝ) (hu : u ∈ Set.Icc (s.q k) 1) :=
    b.insertLevel (k + 1) (by omega) le_rfl 1 u hm (hq u hu)
  have he (u : ℝ) (hu : u ∈ Set.Icc (s.q k) 1) :
      (si u hu).m (k + 1) = (si u hu).m (k + 1 + 1) := by
    simp [si, RSBScheme.insertLevel, section4Mass, b, section4TerminalBase,
      show ¬k + 1 + 1 < k + 1 by omega, s.m_top]
  have heq : (si (s.q (k + 1)) hq0).mergeEqualMass (k + 1) le_rfl
      (he (s.q (k + 1)) hq0) = s := by
    apply terminal_scheme_eq_of_fields
    · funext j
      simp only [RSBScheme.mergeEqualMass, skipLevel, si, RSBScheme.insertLevel,
        section4Mass, b, section4TerminalBase]
      split_ifs <;> first | rfl | (congr 1; omega)
    · funext j
      simp only [RSBScheme.mergeEqualMass, skipLevel, si, RSBScheme.insertLevel,
        section5Rho, b, section4TerminalBase]
      split_ifs <;> first | rfl | (congr 1; omega)
  have hb : mixedSection4Phi ξ b h (k + 1) 1 (s.q (k + 1)) = mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedFunctional_insertLevel ξ b h (k + 1) (by omega) le_rfl 1 (s.q (k + 1)) hm (hq _ hq0)]
    change mixedFunctional ξ h (Paper.parisiSchemeMeasure (si (s.q (k + 1)) hq0)) = _
    rw [← mixedFunctional_mergeEqualMass ξ (si (s.q (k + 1)) hq0) (k + 1) le_rfl
      (he (s.q (k + 1)) hq0), heq]
  have H := hmin ((si u hu).mergeEqualMass (k + 1) le_rfl (he u hu))
  rw [mixedFunctional_mergeEqualMass] at H
  change mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure
    (b.insertLevel (k + 1) (by omega) le_rfl 1 u hm (hq u hu))) at H
  rw [mixedFunctional_insertLevel] at H
  exact hb.trans_le H

theorem mixedClockScheme_terminalBase (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) :
    mixedClockScheme ξ (section4TerminalBase s) =
      section4TerminalBase (mixedClockScheme ξ s) := by
  apply terminal_scheme_eq_of_fields
  · rfl
  · funext j
    by_cases hj : j=k+1
    · simp [mixedClockScheme_q,section4TerminalBase,hj,ξ.clock_one]
    · simp [mixedClockScheme_q,section4TerminalBase,hj]

theorem mixed_terminal_endpointQ_le_overlap_of_min (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (hm : s.m k < 1) (hq : s.q (k+1) < 1)
    (hmin : ∀ s' : RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h (k+1) (s.m k) 0 ≤ s.q (k+1) := by
  let b := section4TerminalBase s
  have hmass : b.m (k+1-1)=s.m k := by simp [b,section4TerminalBase]
  have hbq : b.q (k+1)=1 := by simp [b,section4TerminalBase]
  have hbq' : b.q (k+1-1)=s.q k := by simp [b,section4TerminalBase]
  let Q : ℝ → ℝ := fun z=>section4TVarianceQ (mixedClockScheme ξ b) (mixedBeta ξ) h
    (k+1) 1 (mixedLeftSplitVariance ξ b (k+1) 1 z)
  have hmaps : MapsTo (mixedLeftSplitVariance ξ b (k+1) 1) (Icc (s.q k) 1)
      (Icc (0 : ℝ) ((mixedBeta ξ)^2*((mixedClockScheme ξ b).q (k+1)-
        (mixedClockScheme ξ b).q (k+1-1)))) := by
    intro z hz
    apply mixedLeftSplitVariance_mem ξ b (by omega) (t := 1) (by norm_num)
    simpa only [hbq,hbq'] using hz
  have hvarcts : ContinuousOn (mixedLeftSplitVariance ξ b (k+1) 1) (Icc (s.q k) 1) := by
    intro z hz
    have hz0 : z∈Icc (-1 : ℝ) 1 := ⟨by linarith [s.q_nonneg (p := k) (by omega),hz.1],hz.2⟩
    have H : HasDerivAt (mixedLeftSplitVariance ξ b (k+1) 1) (-ξ.second z) z := by
      change HasDerivAt (fun x=>1*(ξ.first (b.q (k+1))-ξ.first x)) (-ξ.second z) z
      simpa only [one_mul] using (ξ.hasDerivAt_first_unit hz0).const_sub (ξ.first (b.q (k+1)))
    exact H.continuousAt.continuousWithinAt
  have hQcts : ContinuousOn Q (Icc (s.q k) 1) :=
    (continuousOn_section4TVarianceQ_variance (mixedClockScheme ξ b) (mixedBeta ξ) h
      (r := k+1) (by omega) le_rfl (show (1 : ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩)).comp hvarcts hmaps
  have hd (z : ℝ) (hz : z∈Icc (s.q k) 1) :=
    hasDerivWithinAt_mixedSection4Phi_overlap ξ b h (r := k+1) (by omega) le_rfl
      (show (1 : ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) (hmass ▸ hm.le)
      (show z∈Icc (b.q (k+1-1)) (b.q (k+1)) by simpa only [hbq,hbq'] using hz)
  have hFcts : ContinuousOn (mixedSection4Phi ξ b h (k+1) 1) (Icc (s.q (k+1)) 1) := by
    intro z hz
    exact (hd z ⟨(s.q_mono k (by omega)).trans hz.1,hz.2⟩).continuousWithinAt.mono
      (by simpa only [hbq,hbq'] using Icc_subset_Icc (s.q_mono k (by omega)) (le_rfl : (1 : ℝ)≤1))
  have H := endpointQ_le_of_weighted_minimum hq hFcts
    ((hQcts.mono (Icc_subset_Icc (s.q_mono k (by omega)) le_rfl))
      (s.q (k+1)) ⟨le_rfl,hq.le⟩)
    (w := fun z=>ξ.second z*(1-s.m k)/2)
    (fun z hz=>by
      have HH := (hd z ⟨(s.q_mono k (by omega)).trans hz.1.le,hz.2.le⟩).hasDerivAt
        (Icc_mem_nhds (by simpa only [hbq'] using (s.q_mono k (by omega)).trans_lt hz.1)
          (by simpa only [hbq] using hz.2))
      simpa only [hmass,Q] using HH)
    (fun z hz=>div_pos (mul_pos
      (ξ.second_pos ⟨(s.q_nonneg (p := k+1) (by omega)).trans_lt hz.1,hz.2.le⟩)
      (sub_pos.mpr hm)) (by norm_num))
    (fun z hz=>mixedSection4Phi_terminalBase_min ξ s h hmin
      ⟨(s.q_mono k (by omega)).trans hz.1,hz.2⟩)
  have hv : mixedLeftSplitVariance ξ b (k+1) 1 (s.q (k+1)) =
      (mixedBeta ξ)^2*(1-(mixedClockScheme ξ s).q (k+1)) := by
    rw [mixedLeftSplitVariance_eq_clock,one_mul,mixedClockScheme_q,hbq,ξ.clock_one]
    rfl
  change section4TVarianceQ (mixedClockScheme ξ b) (mixedBeta ξ) h (k+1) 1
    (mixedLeftSplitVariance ξ b (k+1) 1 (s.q (k+1))) ≤ s.q (k+1) at H
  rw [hv,mixedClockScheme_terminalBase,
    section4TVarianceQ_terminalBase_endpoint (mixedClockScheme ξ s) (mixedBeta ξ) h] at H
  exact H

theorem mixed_endpointQ_eq_overlap_of_min_terminal (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (hm : s.m k < 1)
    (hleft : s.q k < s.q (k+1) ∨ s.q (k+1)=0)
    (hmin : ∀ s' : RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h (k+1) (s.m k) 0=s.q (k+1) := by
  have hQ := section4TVarianceQ_mem_Icc (mixedClockScheme ξ s) (mixedBeta ξ) h (k+1)
    (m := s.m k) ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩ 0
  apply le_antisymm
  · by_cases hq : s.q (k+1)<1
    · exact mixed_terminal_endpointQ_le_overlap_of_min ξ s h hm hq hmin
    · exact hQ.2.trans (le_of_not_gt hq)
  · rcases hleft with hh|hh
    · have H := mixed_overlap_le_endpointQ_of_min ξ s h (r := k+1) (by omega) le_rfl
        (by simpa only [Nat.add_sub_cancel,s.m_top] using hm)
        (by simpa only [Nat.add_sub_cancel] using hh) hmin
      simpa only [Nat.add_sub_cancel] using H
    · simpa only [hh] using hQ.1

end FourPapersCommon
