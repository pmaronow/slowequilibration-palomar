module
public import FourPapersCommon.MixedInterleavedCompact

@[expose] public section

/-! Closed physical negative/outside witness extraction and compact margins.
All scalar positivity inputs are discharged from genuine mode inequalities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 900000
universe u

 theorem exists_mixedInterleavedComparison_witness_outside_left
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} {t v : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hr0 : 1 ≤ r) (hr : r ≤ k+1)
    (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hleft : s.q (r-1) < s.q r) (hv0 : 0 ≤ v) (hv : v < s.q (r-1)) :
    ∃j,1 ≤ j ∧ j ≤ k+1 ∧ |v|∈Icc (s.q (j-1)) (s.q j) ∧
      0 < mixedInterleavedComparisonDeficit ξ s h r j v 0 (t,v) := by
  obtain ⟨j,hj0,hjr,hj,hprev,hnext⟩ := section5OutsideLeft_exists_interval s hr0 hr hv0 hv
  have hu : |v| ∈ Icc (s.q (j-1)) (s.q j) := by
    rw [abs_of_nonneg hv0]
    exact ⟨hprev,hnext.le⟩
  have hbv : 0<t*(ξ.first (s.q j)-ξ.first |v|) := by
    apply mul_pos ht.1
    apply sub_pos.mpr
    rw [abs_of_nonneg hv0]
    exact ξ.first_strictMonoOn ⟨by linarith,hnext.le.trans (s.q_le_one (by omega))⟩
      ⟨by linarith [s.q_nonneg (p:=j) (by omega)],s.q_le_one (by omega)⟩ hnext
  have hcv : 0<(1-t)*(ξ.first (s.q r)-ξ.first (s.q (r-1))) := by
    apply mul_pos (sub_pos.mpr ht.2)
    apply sub_pos.mpr
    exact ξ.first_strictMonoOn
      ⟨by linarith [s.q_nonneg (p:=r-1) (by omega)],s.q_le_one (by omega)⟩
      ⟨by linarith [s.q_nonneg (p:=r) (by omega)],s.q_le_one (by omega)⟩ hleft
  refine ⟨j,hj0,hj,hu,?_⟩
  rw [mixedInterleavedComparisonDeficit_at_trial]
  exact mixedInterleavedScalarDeficit_pos_left_outside ξ s h
    ⟨ht.1.le,ht.2.le⟩ hr hj0 hjr hu hm hbv hcv

 theorem exists_mixedInterleavedComparison_witness_outside_right
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} {t v : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hr0 : 1 ≤ r) (hr : r ≤ k+1)
    (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hright : s.q r < s.q (r+1)) (hv : s.q (r+1) < v) (hv1 : v ≤ 1) :
    ∃j,1 ≤ j ∧ j ≤ k+2 ∧ |v|∈Icc (s.q (j-1)) (s.q j) ∧
      0 < mixedInterleavedComparisonDeficit ξ s.padOneLast h r j v 0 (t,v) := by
  obtain ⟨j,hj0,hj,hprev,hnext⟩ := exists_nat_adjacent_Ioc s.q
    (show s.q 0<v from (s.q_mono' (r+1) (by omega) 0 (by omega)).trans_lt hv)
    (show v ≤ s.q (k+2) by simpa only [s.q_top] using hv1)
  have hrj : r+1<j := by
    by_contra H
    have Hj : j ≤ r+1 := by omega
    exact (not_le_of_gt hv) (hnext.trans (s.q_mono' (r+1) (by omega) j Hj))
  have hv0 : 0 ≤ v := (s.q_nonneg (p:=r+1) (by omega)).trans hv.le
  have hu : |v| ∈ Icc (s.q (j-1)) (s.q j) := by
    rw [abs_of_nonneg hv0]
    exact ⟨hprev.le,hnext⟩
  have hmass : s.m r < s.m (j-1) :=
    hm (show (⟨r,by omega⟩ : Fin (k+2)) < ⟨j-1,by omega⟩ by simp only [Fin.mk_lt_mk]; omega)
  have hbv : 0<(1-t)*(ξ.first (s.q (r+1))-ξ.first (s.q r)) := by
    apply mul_pos (sub_pos.mpr ht.2)
    apply sub_pos.mpr
    exact ξ.first_strictMonoOn
      ⟨by linarith [s.q_nonneg (p:=r) (by omega)],s.q_le_one (by omega)⟩
      ⟨by linarith [s.q_nonneg (p:=r+1) (by omega)],s.q_le_one (by omega)⟩ hright
  have hcv : 0<t*(ξ.first |v|-ξ.first (s.q (j-1))) := by
    apply mul_pos ht.1
    apply sub_pos.mpr
    rw [abs_of_nonneg hv0]
    exact ξ.first_strictMonoOn
      ⟨by linarith [s.q_nonneg (p:=j-1) (by omega)],s.q_le_one (by omega)⟩
      ⟨by linarith,hv1⟩ hprev
  refine ⟨j,hj0,hj,hu,?_⟩
  rw [mixedInterleavedComparisonDeficit_at_trial]
  exact mixedInterleavedScalarDeficit_pos_right_padded_of_mass_lt ξ s h
    ⟨ht.1.le,ht.2.le⟩ hr0 hj hrj hu hmass hbv hcv

 theorem exists_mixedInterleavedComparison_witness_negative
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} {t v : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hr0 : 2 ≤ r) (hr : r ≤ k+1)
    (hm : 0<s.m 1) (hq : s.q 1<s.q 2) (hv : v<0) (hv1 : |v| ≤ 1) :
    ∃j,1 ≤ j ∧ j ≤ k+2 ∧ |v|∈Icc (s.q (j-1)) (s.q j) ∧
      0 < mixedInterleavedComparisonDeficit ξ s.padOneLast h r j v 0 (t,v) := by
  obtain ⟨j,hj0,hj,hprev,hnext⟩ := exists_nat_adjacent_Ioc s.q
    (by simpa only [s.q_zero] using abs_pos.mpr (ne_of_lt hv))
    (show |v| ≤ s.q (k+2) by simpa only [s.q_top] using hv1)
  refine ⟨j,hj0,hj,⟨hprev.le,hnext⟩,?_⟩
  rw [mixedInterleavedComparisonDeficit_at_trial]
  exact mixedInterleavedScalarDeficit_pos_negative_padded ξ s h ht hr0 hr hj0 hj hm hq hv
    ⟨hprev.le,hnext⟩

 theorem exists_mixedInterleavedComparison_witness_negative_first_beyond
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {t v : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hm : 0<s.m 1) (hq1 : 0<s.q 1)
    (hq : s.q 1<s.q 2) (hv : v<0) (hvq : s.q 1 < |v|) (hv1 : |v| ≤ 1) :
    ∃j,1 ≤ j ∧ j ≤ k+2 ∧ |v|∈Icc (s.q (j-1)) (s.q j) ∧
      0 < mixedInterleavedComparisonDeficit ξ s.padOneLast h 1 j v 0 (t,v) := by
  obtain ⟨j,hj0,hj,hprev,hnext⟩ := exists_nat_adjacent_Ioc s.q
    (by simpa only [s.q_zero] using abs_pos.mpr (ne_of_lt hv))
    (show |v| ≤ s.q (k+2) by simpa only [s.q_top] using hv1)
  have hj2 : 2 ≤ j := by
    by_contra H
    have he:j=1 := by omega
    rw [he] at hnext
    exact (not_le_of_gt hvq) hnext
  refine ⟨j,hj0,hj,⟨hprev.le,hnext⟩,?_⟩
  rw [mixedInterleavedComparisonDeficit_at_trial]
  exact mixedInterleavedScalarDeficit_pos_negative_first_padded ξ s h ht hj2 hj hm hq1 hq hv hvq
    ⟨hprev.le,hnext⟩

 theorem exists_mixed_constrainedPhi_compact_negative_gap_all_spaces
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k+1) (hm : 0<s.m 1) (hq : s.q 1<s.q 2)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (ht : ∀p∈S,p.1∈Ioo (0:ℝ) 1)
    (hu : ∀p∈S,p.2∈Ico (-1:ℝ) 0) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀p∈S,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=p.2)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) p.1 p.2 ≤
        2*mixedInterpolationPsi ξ s h p.1-delta := by
  apply exists_mixed_constrainedPhi_compact_paddedInterleaved_gap_all_spaces ξ s h (by omega) hr hS
    (fun p hp => ⟨(hu p hp).1,(hu p hp).2.le.trans zero_le_one⟩)
    (fun p hp => ⟨(ht p hp).1.le,(ht p hp).2.le⟩)
  intro p hp
  obtain ⟨j,hj0,hj,hv,H⟩ := exists_mixedInterleavedComparison_witness_negative ξ s h
    (ht p hp) hr0 hr hm hq (hu p hp).2 (by rw [abs_of_neg (hu p hp).2]; linarith [(hu p hp).1])
  exact ⟨j,hj0,hj,p.2,hv,0,H⟩

 theorem exists_mixed_constrainedPhi_compact_negative_first_beyond_gap_all_spaces
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (hm : 0<s.m 1) (hq1 : 0<s.q 1) (hq : s.q 1<s.q 2)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (ht : ∀p∈S,p.1∈Ioo (0:ℝ) 1)
    (hu : ∀p∈S,p.2∈Ico (-1:ℝ) 0) (haway : ∀p∈S,s.q 1 < |p.2|) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀p∈S,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=p.2)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) p.1 p.2 ≤
        2*mixedInterpolationPsi ξ s h p.1-delta := by
  have H := exists_mixed_constrainedPhi_compact_paddedInterleaved_gap_all_spaces ξ s h
    (r:=1) le_rfl (by omega) hS
    (fun p hp => ⟨(hu p hp).1,(hu p hp).2.le.trans zero_le_one⟩)
    (fun p hp => ⟨(ht p hp).1.le,(ht p hp).2.le⟩) (by
      intro p hp
      obtain ⟨j,hj0,hj,hv,H⟩ := exists_mixedInterleavedComparison_witness_negative_first_beyond ξ s h
        (ht p hp) hm hq1 hq (hu p hp).2 (haway p hp)
        (by rw [abs_of_neg (hu p hp).2]; linarith [(hu p hp).1])
      exact ⟨j,hj0,hj,p.2,hv,0,H⟩)
  simpa only [show k+2-1=k+1 by omega] using H

 theorem exists_mixed_constrainedPhi_compact_outside_left_gap_all_spaces
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1) (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hleft : s.q (r-1)<s.q r)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (ht : ∀p∈S,p.1∈Ioo (0:ℝ) 1)
    (hu : ∀p∈S,p.2∈Ico (0:ℝ) (s.q (r-1))) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀p∈S,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=p.2)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) p.1 p.2 ≤
        2*mixedInterpolationPsi ξ s h p.1-delta := by
  apply exists_mixed_constrainedPhi_compact_interleaved_gap_all_spaces ξ s h hr0 hr hS
    (fun p hp => ⟨by linarith [(hu p hp).1],(hu p hp).2.le.trans (s.q_le_one (by omega))⟩)
    (fun p hp => ⟨(ht p hp).1.le,(ht p hp).2.le⟩)
  intro p hp
  obtain ⟨j,hj0,hj,hv,H⟩ := exists_mixedInterleavedComparison_witness_outside_left ξ s h
    (ht p hp) hr0 hr hm hleft (hu p hp).1 (hu p hp).2
  exact ⟨j,hj0,hj,p.2,hv,0,H⟩

 theorem exists_mixed_constrainedPhi_compact_outside_right_gap_all_spaces
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1) (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hright : s.q r<s.q (r+1))
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (ht : ∀p∈S,p.1∈Ioo (0:ℝ) 1)
    (hu : ∀p∈S,p.2∈Ioc (s.q (r+1)) 1) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀p∈S,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=p.2)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) p.1 p.2 ≤
        2*mixedInterpolationPsi ξ s h p.1-delta := by
  apply exists_mixed_constrainedPhi_compact_paddedInterleaved_gap_all_spaces ξ s h hr0 hr hS
    (fun p hp => ⟨by linarith [(hu p hp).1,s.q_nonneg (p:=r+1) (by omega)],(hu p hp).2⟩)
    (fun p hp => ⟨(ht p hp).1.le,(ht p hp).2.le⟩)
  intro p hp
  obtain ⟨j,hj0,hj,hv,H⟩ := exists_mixedInterleavedComparison_witness_outside_right ξ s h
    (ht p hp) hr0 hr hm hright (hu p hp).1 (hu p hp).2
  exact ⟨j,hj0,hj,p.2,hv,0,H⟩

end FourPapersCommon
