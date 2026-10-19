module
public import FourPapersCommon.MixedInterleavedGaps
public import Targets.Section5TerminalPadding
public import Targets.Section5OutsideIntervals

@[expose] public section

/-! Terminal trial intervals are covered by exact redundant padding. The
original mixed Hamiltonian, correction, and pressure are unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem mixedClockScheme_padOneLast (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) :
    mixedClockScheme ξ s.padOneLast=(mixedClockScheme ξ s).padOneLast := rfl

 theorem mixedSchemeCorrection_padOneLast (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) :
    mixedSchemeCorrection ξ s.padOneLast=mixedSchemeCorrection ξ s := by
  rw [mixedSchemeCorrection_eq_schemeCorrection,mixedSchemeCorrection_eq_schemeCorrection]
  unfold schemeCorrection
  rw [Finset.sum_range_succ]
  have hz : s.padOneLast.q (k+1+2)=s.padOneLast.q (k+1+1) := by simp [RSBScheme.padOneLast]
  rw [hz,sub_self,mul_zero,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp':=Finset.mem_range.mp hp
  rw [s.padOneLast_m (by omega),s.padOneLast_q (by omega),s.padOneLast_q (by omega)]

 theorem mixedInterpolationPsi_padOneLast (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h t : ℝ) :
    mixedInterpolationPsi ξ s.padOneLast h t=mixedInterpolationPsi ξ s h t := by
  simp only [mixedInterpolationPsi,mixedClockScheme_padOneLast,
    show k+1+2=(k+2)+1 by omega,parisiF_padOneLast_succ,mixedSchemeCorrection_padOneLast]

 private theorem mixed_negative_gap_with_final_trial {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {r j : ℕ} {t u : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hr0 : 2≤r) (hr : r≤k+1) (hj0 : 1≤j) (hj : j≤k+2)
    (hm : 0<s.m 1) (hq : s.q 1<s.q 2) (huneg : u<0)
    (hu : |u|∈Icc (s.q (j-1)) (s.q j)) :
    ∃δ>0,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
        2*mixedInterpolationPsi ξ s h t-δ := by
  have hmp : 0<s.padOneLast.m 1:=by simpa only [s.padOneLast_m (p:=1) (by omega)] using hm
  have hqp : s.padOneLast.q 1<s.padOneLast.q 2:=by
    simpa only [s.padOneLast_q (p:=1) (by omega),s.padOneLast_q (p:=2) (by omega)] using hq
  have hup : |u|∈Icc (s.padOneLast.q (j-1)) (s.padOneLast.q j):=by
    simpa only [s.padOneLast_q (p:=j-1) (by omega),s.padOneLast_q hj] using hu
  obtain ⟨δ,hδ,H⟩:=exists_mixed_constrainedPhi_interleaved_gap_negative (Ω:=Ω) ξ s.padOneLast h
    ht hr0 (by omega) hj0 (by omega) hmp hqp huneg hup
  refine ⟨δ,hδ,?_⟩
  intro n hn sk hatt
  have HH:=H hn sk hatt
  simpa only [mixedClockScheme_padOneLast,show k+1+2-r=(k+2-r)+1 by omega,
    constrainedPhi_padOneLast,mixedInterpolationPsi_padOneLast] using HH

 theorem exists_mixed_constrainedPhi_gap_negative_all_trials {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {r : ℕ} {t u : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hr0 : 2≤r) (hr : r≤k+1) (hm : 0<s.m 1)
    (hq : s.q 1<s.q 2) (huneg : u<0) (hutop : |u| ≤ 1) :
    ∃δ>0,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u≤
        2*mixedInterpolationPsi ξ s h t-δ := by
  obtain ⟨j,hj0,hj,hprev,hnext⟩:=exists_nat_adjacent_Ioc s.q
    (by simpa only [s.q_zero] using abs_pos.mpr (ne_of_lt huneg))
    (show |u| ≤ s.q (k+2) by simpa only [s.q_top] using hutop)
  exact mixed_negative_gap_with_final_trial ξ s h ht hr0 hr hj0 hj hm hq huneg ⟨hprev.le,hnext⟩

 theorem exists_mixed_constrainedPhi_gap_negative_first_beyond {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {t u : ℝ}
    (ht : t∈Ioo (0:ℝ) 1) (hm : 0<s.m 1) (hq1 : 0<s.q 1)
    (hq : s.q 1<s.q 2) (huneg : u<0) (hu1 : s.q 1 < |u|) (hutop : |u| ≤ 1) :
    ∃δ>0,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=u)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+1) t u≤
        2*mixedInterpolationPsi ξ s h t-δ := by
  obtain ⟨j,hj0,hj,hprev,hnext⟩:=exists_nat_adjacent_Ioc s.q
    (by simpa only [s.q_zero] using abs_pos.mpr (ne_of_lt huneg))
    (show |u| ≤ s.q (k+2) by simpa only [s.q_top] using hutop)
  have hj2 : 2≤j:=by
    by_contra hh
    have he:j=1:=by omega
    rw [he] at hnext
    exact (not_le_of_gt hu1) hnext
  have hmp : 0<s.padOneLast.m 1:=by simpa only [s.padOneLast_m (p:=1) (by omega)] using hm
  have hq1p : 0<s.padOneLast.q 1:=by simpa only [s.padOneLast_q (p:=1) (by omega)] using hq1
  have hqp : s.padOneLast.q 1<s.padOneLast.q 2:=by
    simpa only [s.padOneLast_q (p:=1) (by omega),s.padOneLast_q (p:=2) (by omega)] using hq
  have hu1p : s.padOneLast.q 1 < |u|:=by simpa only [s.padOneLast_q (p:=1) (by omega)] using hu1
  have hup : |u|∈Icc (s.padOneLast.q (j-1)) (s.padOneLast.q j):=by
    simpa only [mem_Icc, s.padOneLast_q (p:=j-1) (by omega),s.padOneLast_q hj] using And.intro hprev.le hnext
  obtain ⟨δ,hδ,H⟩:=exists_mixed_constrainedPhi_interleaved_gap_negative_first (Ω:=Ω) ξ s.padOneLast h
    ht hj2 (by omega) hmp hq1p hqp huneg hu1p hup
  refine ⟨δ,hδ,?_⟩
  intro n hn sk hatt
  simpa only [mixedClockScheme_padOneLast,constrainedPhi_padOneLast,mixedInterpolationPsi_padOneLast]
    using H hn sk hatt

end FourPapersCommon
