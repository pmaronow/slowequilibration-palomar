module
public import FourPapersCommon.MixedTerminalPadding

@[expose] public section

/-! Scalar gaps are selected before any probability space or system size.
These purely analytic witnesses can therefore be used in compactness arguments
for arbitrary sequences of actual mixed disorder models. -/
noncomputable section
open Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000

 theorem mixedInterleavedScalarDeficit_pos_negative
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r j : ℕ} {t u : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hr0 : 2≤r) (hr : r≤k+1)
    (hj0 : 1≤j) (hj : j≤k+1) (hm : 0<s.m 1) (hq : s.q 1<s.q 2)
    (huneg : u<0) (hu : |u|∈Icc (s.q (j-1)) (s.q j)) :
    0 < section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock u) := by
  have hu1 : |u|≤1:=hu.2.trans (s.q_le_one (by omega))
  have hqc : (mixedClockScheme ξ s).q 1<(mixedClockScheme ξ s).q 2 :=
    ξ.clock_strictMonoOn ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
      ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩ hq
  have H:=section5InterleavedScalarV_zero_lt_negative (mixedClockScheme ξ s)
    (mixedBeta ξ) h (mixedBeta_ne_zero ξ) ht hr0 hj0 hj
    (by simpa only [mixedClockScheme_m] using hm) hqc
    ((clock_lt_zero_iff ξ u hu1).mpr huneg) (clock_mem_abs_interval ξ s hj hu)
  exact sub_pos.mpr H

 theorem mixedInterleavedScalarDeficit_pos_negative_first
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {j : ℕ} {t u : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hj0 : 2≤j) (hj : j≤k+1)
    (hm : 0<s.m 1) (hq1 : 0<s.q 1) (hq : s.q 1<s.q 2)
    (huneg : u<0) (hu1 : s.q 1 < |u|) (hu : |u|∈Icc (s.q (j-1)) (s.q j)) :
    0 < section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h 1 j t (ξ.clock u) := by
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
  exact sub_pos.mpr H

 theorem mixedInterleavedScalarDeficit_pos_left_outside
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r j : ℕ} {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hr : r≤k+1)
    (hj0 : 1≤j) (hjr : j<r) (hu : |u|∈Icc (s.q (j-1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hbv : 0<t*(ξ.first (s.q j)-ξ.first |u|))
    (hcv : 0<(1-t)*(ξ.first (s.q r)-ξ.first (s.q (r-1)))) :
    0 < section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock u) := by
  have hj : j≤k+1:=by omega
  have hB : 0<t*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q j-|ξ.clock u|)) := by
    simpa only [mixedClockScheme_q,←clock_abs,mixed_first_increment] using hbv
  have hC : 0<(1-t)*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q r-(mixedClockScheme ξ s).q (r-1))) := by
    simpa only [mixedClockScheme_q,mixed_first_increment] using hcv
  have H:=section5InterleavedScalarV_zero_lt_left_outside (mixedClockScheme ξ s) (mixedBeta ξ)
    h ht hr hj0 hjr (clock_mem_abs_interval ξ s hj hu)
    (by simpa only [mixedClockScheme_m] using hm) hB hC
  exact sub_pos.mpr H

 theorem mixedInterleavedScalarDeficit_pos_right_outside
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r j : ℕ} {t u : ℝ} (ht : t∈Icc (0:ℝ) 1) (hr0 : 1≤r) (hj : j≤k+1)
    (hrj : r+1<j) (hu : |u|∈Icc (s.q (j-1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k+2) => s.m p))
    (hbv : 0<(1-t)*(ξ.first (s.q (r+1))-ξ.first (s.q r)))
    (hcv : 0<t*(ξ.first |u|-ξ.first (s.q (j-1)))) :
    0 < section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock u) := by
  have hB : 0<(1-t)*((mixedBeta ξ)^2*((mixedClockScheme ξ s).q (r+1)-(mixedClockScheme ξ s).q r)) := by
    simpa only [mixedClockScheme_q,mixed_first_increment] using hbv
  have hC : 0<t*((mixedBeta ξ)^2*(|ξ.clock u|-(mixedClockScheme ξ s).q (j-1))) := by
    simpa only [mixedClockScheme_q,←clock_abs,mixed_first_increment] using hcv
  have H:=section5InterleavedScalarV_zero_lt_right_outside (mixedClockScheme ξ s) (mixedBeta ξ)
    h ht hj hrj (clock_mem_abs_interval ξ s hj hu)
    (by simpa only [mixedClockScheme_m] using hm) hB hC
  exact sub_pos.mpr H

 theorem mixedInterleavedScalarDeficit_pos_negative_padded
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r j : ℕ} {t u : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hr0 : 2 ≤ r) (hr : r ≤ k+1)
    (hj0 : 1 ≤ j) (hj : j ≤ k+2) (hm : 0 < s.m 1) (hq : s.q 1 < s.q 2)
    (huneg : u < 0) (hu : |u| ∈ Icc (s.q (j-1)) (s.q j)) :
    0 < section5InterleavedScalarDeficit (mixedClockScheme ξ s.padOneLast)
      (mixedBeta ξ) h r j t (ξ.clock u) := by
  exact mixedInterleavedScalarDeficit_pos_negative ξ s.padOneLast h ht hr0 (by omega)
    hj0 (by omega)
    (by simpa only [s.padOneLast_m (p:=1) (by omega)] using hm)
    (by simpa only [s.padOneLast_q (p:=1) (by omega),s.padOneLast_q (p:=2) (by omega)] using hq)
    huneg
    (by simpa only [s.padOneLast_q (p:=j-1) (by omega),s.padOneLast_q hj] using hu)

 theorem mixedInterleavedScalarDeficit_pos_negative_first_padded
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {j : ℕ} {t u : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hj0 : 2 ≤ j) (hj : j ≤ k+2)
    (hm : 0 < s.m 1) (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2)
    (huneg : u < 0) (hu1 : s.q 1 < |u|) (hu : |u| ∈ Icc (s.q (j-1)) (s.q j)) :
    0 < section5InterleavedScalarDeficit (mixedClockScheme ξ s.padOneLast)
      (mixedBeta ξ) h 1 j t (ξ.clock u) := by
  exact mixedInterleavedScalarDeficit_pos_negative_first ξ s.padOneLast h ht hj0 (by omega)
    (by simpa only [s.padOneLast_m (p:=1) (by omega)] using hm)
    (by simpa only [s.padOneLast_q (p:=1) (by omega)] using hq1)
    (by simpa only [s.padOneLast_q (p:=1) (by omega),s.padOneLast_q (p:=2) (by omega)] using hq)
    huneg
    (by simpa only [s.padOneLast_q (p:=1) (by omega)] using hu1)
    (by simpa only [s.padOneLast_q (p:=j-1) (by omega),s.padOneLast_q hj] using hu)

open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
 theorem mixed_constrainedPhi_le_Psi_sub_paddedInterleavedDeficit
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) {r j : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1)
    (hj0 : 1 ≤ j) (hj : j ≤ k+2) {t u : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hu : |u| ∈ Icc (s.q (j-1)) (s.q j)) (hatt : ∃σ τ:Config n,overlap n σ τ=u) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u ≤
      2*mixedInterpolationPsi ξ s h t-
        section5InterleavedScalarDeficit (mixedClockScheme ξ s.padOneLast)
          (mixedBeta ξ) h r j t (ξ.clock u) := by
  have hup : |u| ∈ Icc (s.padOneLast.q (j-1)) (s.padOneLast.q j) := by
    simpa only [s.padOneLast_q (p:=j-1) (by omega),s.padOneLast_q hj] using hu
  have H := mixed_constrainedPhi_le_Psi_sub_interleavedDeficit hn ξ s.padOneLast h sk
    hr0 (by omega) hj0 (by omega) ht hup hatt
  rw [mixedInterpolationPsi_padOneLast] at H
  simpa only [mixedClockScheme_padOneLast,show k+1+2-r=(k+2-r)+1 by omega,
    constrainedPhi_padOneLast] using H

end FourPapersCommon
