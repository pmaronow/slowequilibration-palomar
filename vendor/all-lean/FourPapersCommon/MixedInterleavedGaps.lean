module
public import FourPapersCommon.MixedInterleavedEndpoint
public import Targets.Section5InterleavedBound

@[expose] public section

/-! Actual mixed constrained-pressure strict gaps away from physical neighbors.
The scalar witness is independent of system size and Gaussian realization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem tangentRemainder_self (ξ : AdmissibleEvenMixture) (u : ℝ) :
    ξ.tangentRemainder u u=0 := by simp [AdmissibleEvenMixture.tangentRemainder]

 theorem mixed_constrainedPhi_le_Psi_sub_interleavedDeficit
    {n k : ℕ} (hn : 0<n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) {r j : ℕ}
    (hr0 : 1≤r) (hr : r≤k+1) (hj0 : 1≤j) (hj : j≤k+1) {t u : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hu : |u|∈Icc (s.q (j-1)) (s.q j))
    (hatt : ∃σ τ:Config n,overlap n σ τ=u) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
      2*mixedInterpolationPsi ξ s h t-
        section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock u) := by
  have H:=mixed_constrainedPhi_le_interleavedOffDiagonalMajorant hn ξ s h sk hr0 hr hj0 hj
    (v:=u) (ell:=0) ht hu hatt
  simp only [tangentRemainder_self,zero_mul,sub_zero,mul_zero,add_zero] at H
  dsimp [mixedInterpolationPsi,section5InterleavedScalarDeficit]
  linarith

 theorem exists_mixed_constrainedPhi_interleaved_gap_negative
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r j : ℕ} {t u : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hr0 : 2≤r) (hr : r≤k+1)
    (hj0 : 1≤j) (hj : j≤k+1) (hm : 0<s.m 1) (hq : s.q 1<s.q 2)
    (huneg : u<0) (hu : |u|∈Icc (s.q (j-1)) (s.q j)) :
    ∃δ>0,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
        2*mixedInterpolationPsi ξ s h t-δ := by
  let δ:=section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock u)
  have hu1 : |u|≤1:=hu.2.trans (s.q_le_one (by omega))
  have hqc : (mixedClockScheme ξ s).q 1<(mixedClockScheme ξ s).q 2 :=
    ξ.clock_strictMonoOn ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
      ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hq
  have H:=section5InterleavedScalarV_zero_lt_negative (mixedClockScheme ξ s)
    (mixedBeta ξ) h (mixedBeta_ne_zero ξ) ht hr0 hj0 hj
    (by simpa only [mixedClockScheme_m] using hm) hqc
    ((clock_lt_zero_iff ξ u hu1).mpr huneg) (clock_mem_abs_interval ξ s hj hu)
  refine ⟨δ,sub_pos.mpr H,?_⟩
  intro n hn sk hatt
  exact mixed_constrainedPhi_le_Psi_sub_interleavedDeficit hn ξ s h sk (by omega) hr hj0 hj
    ⟨ht.1.le,ht.2.le⟩ hu hatt

 theorem exists_mixed_constrainedPhi_interleaved_gap_negative_first
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {j : ℕ} {t u : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hj0 : 2≤j) (hj : j≤k+1)
    (hm : 0<s.m 1) (hq1 : 0<s.q 1) (hq : s.q 1<s.q 2)
    (huneg : u<0) (hu1 : s.q 1 < |u|) (hu : |u|∈Icc (s.q (j-1)) (s.q j)) :
    ∃δ>0,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t u≤
        2*mixedInterpolationPsi ξ s h t-δ := by
  let δ:=section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h 1 j t (ξ.clock u)
  have habs : |u|≤1:=hu.2.trans (s.q_le_one (by omega))
  have hqc : (mixedClockScheme ξ s).q 1<(mixedClockScheme ξ s).q 2 :=
    ξ.clock_strictMonoOn ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
      ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hq
  have hq1c : 0<(mixedClockScheme ξ s).q 1 := by
    have hh:=ξ.clock_strictMonoOn (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1)
      ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hq1
    simpa only [ξ.clock_zero, mixedClockScheme_q] using hh
  have hu1c : (mixedClockScheme ξ s).q 1< |ξ.clock u| := by
    rw [←clock_abs]
    exact ξ.clock_strictMonoOn ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
      ⟨abs_nonneg u,habs⟩ hu1
  have H:=section5InterleavedScalarV_zero_lt_negative_of_q1_pos (mixedClockScheme ξ s)
    (mixedBeta ξ) h (mixedBeta_ne_zero ξ) ht (by omega : 1≤(1:ℕ)) hj0 hj
    (by simpa only [mixedClockScheme_m] using hm) hq1c hqc
    ((clock_lt_zero_iff ξ u habs).mpr huneg) hu1c (clock_mem_abs_interval ξ s hj hu)
  refine ⟨δ,sub_pos.mpr H,?_⟩
  intro n hn sk hatt
  simpa only [show k+2-1=k+1 by omega] using
    mixed_constrainedPhi_le_Psi_sub_interleavedDeficit hn ξ s h sk (r:=1) le_rfl
      (by omega) (by omega) hj ⟨ht.1.le,ht.2.le⟩ hu hatt

 theorem exists_mixed_constrainedPhi_interleaved_gap_left_outside
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r j : ℕ} {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hr : r≤k+1)
    (hj0 : 1≤j) (hjr : j<r) (hu : |u|∈Icc (s.q (j-1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hbv : 0<t*(ξ.first (s.q j)-ξ.first |u|))
    (hcv : 0<(1-t)*(ξ.first (s.q r)-ξ.first (s.q (r-1)))) :
    ∃δ>0,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
        2*mixedInterpolationPsi ξ s h t-δ := by
  have hj : j≤k+1:=by omega
  have hB : 0<t*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q j-|ξ.clock u|)) := by
    simpa only [mixedClockScheme_q,←clock_abs,mixed_first_increment] using hbv
  have hC : 0<(1-t)*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q r-(mixedClockScheme ξ s).q (r-1))) := by
    simpa only [mixedClockScheme_q,mixed_first_increment] using hcv
  have H:=section5InterleavedScalarV_zero_lt_left_outside (mixedClockScheme ξ s) (mixedBeta ξ)
    h ht hr hj0 hjr (clock_mem_abs_interval ξ s hj hu)
    (by simpa only [mixedClockScheme_m] using hm) hB hC
  refine ⟨section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock u),
    sub_pos.mpr H,?_⟩
  intro n hn sk hatt
  exact mixed_constrainedPhi_le_Psi_sub_interleavedDeficit hn ξ s h sk (by omega) hr hj0 hj ht hu hatt

 theorem exists_mixed_constrainedPhi_interleaved_gap_right_outside
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r j : ℕ} {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hr0 : 1≤r) (hj : j≤k+1)
    (hrj : r+1<j) (hu : |u|∈Icc (s.q (j-1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hbv : 0<(1-t)*(ξ.first (s.q (r+1))-ξ.first (s.q r)))
    (hcv : 0<t*(ξ.first |u|-ξ.first (s.q (j-1)))) :
    ∃δ>0,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
        2*mixedInterpolationPsi ξ s h t-δ := by
  have hB : 0<(1-t)*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q (r+1)-(mixedClockScheme ξ s).q r)) := by
    simpa only [mixedClockScheme_q,mixed_first_increment] using hbv
  have hC : 0<t*((mixedBeta ξ)^2*(|ξ.clock u|-(mixedClockScheme ξ s).q (j-1))) := by
    simpa only [mixedClockScheme_q,←clock_abs,mixed_first_increment] using hcv
  have H:=section5InterleavedScalarV_zero_lt_right_outside (mixedClockScheme ξ s) (mixedBeta ξ)
    h ht hj hrj (clock_mem_abs_interval ξ s hj hu)
    (by simpa only [mixedClockScheme_m] using hm) hB hC
  refine ⟨section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock u),
    sub_pos.mpr H,?_⟩
  intro n hn sk hatt
  exact mixed_constrainedPhi_le_Psi_sub_interleavedDeficit hn ξ s h sk hr0 (by omega) (by omega) hj ht hu hatt

end FourPapersCommon
