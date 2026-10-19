module
public import FourPapersCommon.MixedInterleavedScalarGaps
public import Targets.Section5InterleavedMassPair

@[expose] public section

/-! Genuine mixed outside-neighbor gaps with breakpoint-safe trial selection.
Only the witness mass pair is used on the right, so the terminal interval is
included through exact redundant padding. All margins precede Ω and n. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000
universe u

 theorem mixedInterleavedScalarDeficit_pos_right_padded_of_mass_lt
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r j : ℕ} {t v : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hr0 : 1 ≤ r)
    (hj : j ≤ k+2) (hrj : r+1 < j) (hu : |v| ∈ Icc (s.q (j-1)) (s.q j))
    (hm : s.m r < s.m (j-1))
    (hbv : 0 < (1-t)*(ξ.first (s.q (r+1))-ξ.first (s.q r)))
    (hcv : 0 < t*(ξ.first |v|-ξ.first (s.q (j-1)))) :
    0 < section5InterleavedScalarDeficit (mixedClockScheme ξ s.padOneLast)
      (mixedBeta ξ) h r j t (ξ.clock v) := by
  have H := section5InterleavedScalarV_zero_lt_right_of_mass_lt
    (mixedClockScheme ξ s.padOneLast) (mixedBeta ξ) h ht (by omega) hrj
    (clock_mem_abs_interval ξ s.padOneLast (by omega) (by
      simpa only [s.padOneLast_q (p:=j-1) (by omega),s.padOneLast_q hj] using hu))
    (by simpa only [mixedClockScheme_m,s.padOneLast_m (p:=r) (by omega),
      s.padOneLast_m (p:=j-1) (by omega)] using hm)
    (by simpa only [mixedClockScheme_q,s.padOneLast_q (p:=r+1) (by omega),
      s.padOneLast_q (p:=r) (by omega),mixed_first_increment] using hbv)
    (by simpa only [mixedClockScheme_q,s.padOneLast_q (p:=j-1) (by omega),
      ←clock_abs,mixed_first_increment] using hcv)
  exact sub_pos.mpr H

 theorem exists_mixed_constrainedPhi_gap_outside_left
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} {t v : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hr0 : 1 ≤ r) (hr : r ≤ k+1)
    (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hleft : s.q (r-1) < s.q r) (hv0 : 0 ≤ v) (hv : v < s.q (r-1)) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=v)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t v ≤
        2*mixedInterpolationPsi ξ s h t-delta := by
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
  let delta := section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock v)
  refine ⟨delta,mixedInterleavedScalarDeficit_pos_left_outside ξ s h
    ⟨ht.1.le,ht.2.le⟩ hr hj0 hjr hu hm hbv hcv,?_⟩
  intro Ω _ _ n hn sk hatt
  exact mixed_constrainedPhi_le_Psi_sub_interleavedDeficit hn ξ s h sk hr0 hr hj0 hj
    ⟨ht.1.le,ht.2.le⟩ hu hatt

 theorem exists_mixed_constrainedPhi_gap_outside_right
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} {t v : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hr0 : 1 ≤ r) (hr : r ≤ k+1)
    (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hright : s.q r < s.q (r+1)) (hv : s.q (r+1) < v) (hv1 : v ≤ 1) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=v)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t v ≤
        2*mixedInterpolationPsi ξ s h t-delta := by
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
  let delta := section5InterleavedScalarDeficit (mixedClockScheme ξ s.padOneLast)
    (mixedBeta ξ) h r j t (ξ.clock v)
  refine ⟨delta,mixedInterleavedScalarDeficit_pos_right_padded_of_mass_lt ξ s h
    ⟨ht.1.le,ht.2.le⟩ hr0 hj hrj hu hmass hbv hcv,?_⟩
  intro Ω _ _ n hn sk hatt
  exact mixed_constrainedPhi_le_Psi_sub_paddedInterleavedDeficit hn ξ s h sk hr0 hr hj0 hj
    ⟨ht.1.le,ht.2.le⟩ hu hatt

end FourPapersCommon
