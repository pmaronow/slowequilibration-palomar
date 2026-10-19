module
public import FourPapersCommon.MixedInsertedFunctional
public import FourPapersCommon.MixedSecondCorrection
public import Targets.Section4RightInsertedScheme

@[expose] public section

/-! Actual mixed right insertions. Physical theta corrections accompany the
clocked Gaussian recursion, and all competitors are probability measures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1000000

private theorem scheme_eq_of_fields {k : ℕ} {s t : RSBScheme k}
    (hm : s.m=t.m) (hq : s.q=t.q) : s=t := by
  cases s; cases t; cases hm; cases hq; rfl

theorem mixedClockScheme_insertRightLevel (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k+1) (m u : ℝ)
    (hm : m∈Icc (s.m (r-1)) (s.m r)) (hu : u∈Icc (s.q r) (s.q (r+1))) :
    mixedClockScheme ξ (s.insertRightLevel r hr0 hr m u hm hu)=
      (mixedClockScheme ξ s).insertRightLevel r hr0 hr m (ξ.clock u) hm
        (clock_mem_right_interval ξ s hr hu) := by
  apply scheme_eq_of_fields
  · rfl
  · funext j
    simp only [mixedClockScheme_q,RSBScheme.insertRightLevel,section5RightRho,section5Rho]
    split_ifs <;> rfl

theorem schemeCorrection_insertRightLevel (θ : ℝ→ℝ) {k : ℕ} (s : RSBScheme k)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k+1) (m u : ℝ)
    (hm : m∈Icc (s.m (r-1)) (s.m r)) (hu : u∈Icc (s.q r) (s.q (r+1))) :
    schemeCorrection θ (s.insertRightLevel r hr0 hr m u hm hu)=
      schemeCorrection θ s+(m-s.m r)/2*(θ u-θ (s.q r)) := by
  have hcoeff (p : ℕ) :
      (if p<r+1 then (2 : ℝ) else 1)*section5RightMass s r m p=section4Mass s r m p := by
    unfold section5RightMass section5Mass section4Mass
    split_ifs <;> first | omega | ring
  have H := rightInsertedCorrection_sum θ s r hr m u
  simp_rw [hcoeff] at H
  unfold schemeCorrection
  change (1/2 : ℝ)*(∑ p∈Finset.range (k+3),section4Mass s r m p*
    (θ (section5RightRho s r u (p+1))-θ (section5RightRho s r u p)))=_
  rw [H]
  ring

def mixedSection4RightPhi (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (m u : ℝ) : ℝ :=
  Real.log 2+section4RightT (mixedClockScheme ξ s) (mixedBeta ξ) h r m
    (mixedRightSplitVariance ξ s r 1 u)-mixedSchemeCorrection ξ s+
    (s.m r-m)/2*(ξ.correction u-ξ.correction (s.q r))

theorem mixedFunctional_insertRightLevel (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k+1) (m u : ℝ)
    (hm : m∈Icc (s.m (r-1)) (s.m r)) (hu : u∈Icc (s.q r) (s.q (r+1))) :
    mixedFunctional ξ h (Paper.parisiSchemeMeasure (s.insertRightLevel r hr0 hr m u hm hu))=
      mixedSection4RightPhi ξ s h r m u := by
  rw [mixedFunctional_scheme,mixedClockScheme_insertRightLevel,
    parisiF_insertRightLevel (mixedClockScheme ξ s) (mixedBeta ξ) r hr0 hr m (ξ.clock u)
      hm (clock_mem_right_interval ξ s hr hu) le_rfl,
    mixedSchemeCorrection_eq_schemeCorrection,schemeCorrection_insertRightLevel,
    ←mixedSchemeCorrection_eq_schemeCorrection]
  rw [mixedSection4RightPhi,mixedRightSplitVariance_eq_clock]
  simp only [one_mul]
  change Real.log 2+section4RightT (mixedClockScheme ξ s) (mixedBeta ξ) h r m
    ((mixedBeta ξ)^2*(ξ.clock u-(mixedClockScheme ξ s).q r))-_=_
  ring

theorem mixedSection4RightPhi_baseline (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k+1) {u : ℝ}
    (hu : u∈Icc (s.q r) (s.q (r+1))) :
    mixedSection4RightPhi ξ s h r (s.m r) u=mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  have hv := mixedRightSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu
  rw [mixedSection4RightPhi,mixedFunctional_scheme]
  simp only [sub_self,zero_div,zero_mul,add_zero]
  rw [show s.m r=(mixedClockScheme ξ s).m r from rfl,
    section4RightT_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv]

theorem mixedSection4RightPhi_at_lower_overlap (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k+1) (m : ℝ) :
    mixedSection4RightPhi ξ s h r m (s.q r)=mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  simp only [mixedSection4RightPhi,mixedRightSplitVariance,sub_self,mul_zero,
    section4RightT_zero_variance (mixedClockScheme ξ s) (mixedBeta ξ) h hr m,add_zero,
    mixedFunctional_scheme]

theorem mixedSection4RightPhi_near_min (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1) {m u : ℝ}
    (hm : m∈Icc (s.m (r-1)) (s.m r)) (hu : u∈Icc (s.q r) (s.q (r+1)))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h+ε) :
    mixedSection4RightPhi ξ s h r (s.m r) u-ε ≤ mixedSection4RightPhi ξ s h r m u := by
  have H : mixedPressure ξ h ≤ mixedFunctional ξ h
      (Paper.parisiSchemeMeasure (s.insertRightLevel r hr0 hr m u hm hu)) := by
    rw [←mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  rw [mixedFunctional_insertRightLevel] at H
  rw [mixedSection4RightPhi_baseline ξ s h hr hu]
  linarith

theorem mixedSection4RightPhi_lower_mass_min (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1) {u : ℝ}
    (hu : u∈Icc (s.q r) (s.q (r+1)))
    (hmin : ∀ s' : RSBScheme k,mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    mixedSection4RightPhi ξ s h r (s.m r) u ≤ mixedSection4RightPhi ξ s h r (s.m (r-1)) u := by
  have hm : s.m (r-1)∈Icc (s.m (r-1)) (s.m r) :=
    ⟨le_rfl,s.m_mono' r hr (r-1) (by omega)⟩
  let s' := s.insertRightLevel r hr0 hr (s.m (r-1)) u hm hu
  have heq : s'.m (r-1)=s'.m (r-1+1) := by
    simp [s',RSBScheme.insertRightLevel,section4Mass,show r-1<r by omega,Nat.sub_add_cancel hr0]
  have H := hmin (s'.mergeEqualMass (r-1) (by omega) heq)
  rw [mixedFunctional_mergeEqualMass] at H
  change mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
    mixedFunctional ξ h (Paper.parisiSchemeMeasure
      (s.insertRightLevel r hr0 hr (s.m (r-1)) u hm hu)) at H
  rwa [mixedFunctional_insertRightLevel,←mixedSection4RightPhi_baseline ξ s h hr hu] at H

end FourPapersCommon
