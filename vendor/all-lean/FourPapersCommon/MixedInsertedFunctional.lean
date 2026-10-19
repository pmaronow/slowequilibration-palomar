module
public import FourPapersCommon.MixedLeftEndpoint
public import FourPapersCommon.SchemeCorrectionAlgebra
public import FourPapersCommon.MixedMinimizer
public import Targets.Section4Stationarity

@[expose] public section

/-! Actual mixed finite-scheme insertion, optimality, and derivatives.

The mass and overlap variations use genuine competing probability measures.
The original physical correction θ(q)=q ξ′(q)−ξ(q) is kept throughout.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
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

theorem mixedClockScheme_insertLevel (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Icc (s.m (r - 1)) (s.m r)) (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    mixedClockScheme ξ (s.insertLevel r hr0 hr m u hm hu) =
      (mixedClockScheme ξ s).insertLevel r hr0 hr m (ξ.clock u) hm
        (clock_mem_left_interval ξ s hr hu) := by
  apply scheme_eq_of_fields
  · rfl
  · funext j
    simp only [mixedClockScheme_q, RSBScheme.insertLevel, section5Rho]
    split_ifs <;> rfl

theorem mixedClockScheme_mergeEqualMass (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme (k + 1)) (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) :
    mixedClockScheme ξ (s.mergeEqualMass p hp hm) =
      (mixedClockScheme ξ s).mergeEqualMass p hp hm := by
  apply scheme_eq_of_fields <;> rfl

theorem mixedFunctional_mergeEqualMass (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme (k + 1)) (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) (h : ℝ) :
    mixedFunctional ξ h (Paper.parisiSchemeMeasure (s.mergeEqualMass p hp hm)) =
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  rw [mixedFunctional_scheme, mixedFunctional_scheme, mixedClockScheme_mergeEqualMass,
    parisiF_mergeEqualMass (mixedClockScheme ξ s) p hp hm (mixedBeta ξ),
    mixedSchemeCorrection_eq_schemeCorrection, mixedSchemeCorrection_eq_schemeCorrection,
    schemeCorrection_mergeEqualMass]

def mixedSection4Phi (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (m u : ℝ) : ℝ :=
  Real.log 2 + section4T (mixedClockScheme ξ s) (mixedBeta ξ) h r m
    (mixedLeftSplitVariance ξ s r 1 u) - mixedSchemeCorrection ξ s +
    (s.m (r - 1) - m) / 2 * (ξ.correction (s.q r) - ξ.correction u)

theorem mixedFunctional_insertLevel (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Icc (s.m (r - 1)) (s.m r)) (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    mixedFunctional ξ h (Paper.parisiSchemeMeasure (s.insertLevel r hr0 hr m u hm hu)) =
      mixedSection4Phi ξ s h r m u := by
  rw [mixedFunctional_scheme, mixedClockScheme_insertLevel,
    parisiF_insertLevel (mixedClockScheme ξ s) (mixedBeta ξ) r hr0 hr m (ξ.clock u)
      hm (clock_mem_left_interval ξ s hr hu) le_rfl,
    mixedSchemeCorrection_eq_schemeCorrection,
    schemeCorrection_insertLevel, ← mixedSchemeCorrection_eq_schemeCorrection]
  rw [mixedSection4Phi, mixedLeftSplitVariance_eq_clock]
  simp only [one_mul]
  change Real.log 2 + section4T (mixedClockScheme ξ s) (mixedBeta ξ) h r m
    ((mixedBeta ξ) ^ 2 * ((mixedClockScheme ξ s).q r - ξ.clock u)) - _ = _
  ring

theorem mixedSection4Phi_baseline (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    mixedSection4Phi ξ s h r (s.m (r - 1)) u =
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  have hv := mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu
  rw [mixedSection4Phi, mixedFunctional_scheme]
  simp only [sub_self, zero_div, zero_mul, add_zero]
  rw [show s.m (r - 1) = (mixedClockScheme ξ s).m (r - 1) from rfl,
    section4T_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv]

theorem mixedSection4Phi_at_upper_overlap (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m : ℝ) :
    mixedSection4Phi ξ s h r m (s.q r) =
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
  simp only [mixedSection4Phi, mixedLeftSplitVariance, sub_self, mul_zero,
    section4T_zero_variance (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr m,
    add_zero, mixedFunctional_scheme]

theorem mixedSection4Phi_near_min (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {m u : ℝ} (hm : m ∈ Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε) :
    mixedSection4Phi ξ s h r (s.m (r - 1)) u - ε ≤ mixedSection4Phi ξ s h r m u := by
  have H : mixedPressure ξ h ≤ mixedFunctional ξ h
      (Paper.parisiSchemeMeasure (s.insertLevel r hr0 hr m u hm hu)) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  rw [mixedFunctional_insertLevel] at H
  rw [mixedSection4Phi_baseline ξ s h hr0 hr hu]
  linarith

theorem mixedSection4Phi_upper_mass_min (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    mixedSection4Phi ξ s h r (s.m (r - 1)) u ≤ mixedSection4Phi ξ s h r (s.m r) u := by
  have hm : s.m r ∈ Icc (s.m (r - 1)) (s.m r) :=
    ⟨s.m_mono' r hr (r - 1) (by omega), le_rfl⟩
  let s' := s.insertLevel r hr0 hr (s.m r) u hm hu
  have heq : s'.m r = s'.m (r + 1) := by
    simp [s', RSBScheme.insertLevel, section4Mass, show ¬r + 1 < r by omega]
  have H := hmin (s'.mergeEqualMass r hr heq)
  rw [mixedFunctional_mergeEqualMass] at H
  change mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
    mixedFunctional ξ h (Paper.parisiSchemeMeasure (s.insertLevel r hr0 hr (s.m r) u hm hu)) at H
  rwa [mixedFunctional_insertLevel, ← mixedSection4Phi_baseline ξ s h hr0 hr hu] at H

theorem hasDerivWithinAt_mixedSection4Phi_overlap (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hmm : s.m (r - 1) ≤ m) {u : ℝ}
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (mixedSection4Phi ξ s h r m)
      (ξ.second u * (m - s.m (r - 1)) / 2 *
        (u - section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r m
          (mixedLeftSplitVariance ξ s r 1 u)))
      (Icc (s.q (r - 1)) (s.q r)) u := by
  have hmap : MapsTo (mixedLeftSplitVariance ξ s r 1)
      (Icc (s.q (r - 1)) (s.q r))
      (Icc (0 : ℝ) ((mixedBeta ξ) ^ 2 *
        ((mixedClockScheme ξ s).q r - (mixedClockScheme ξ s).q (r - 1)))) :=
    fun z hz => mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hz
  have hu0 : u ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [s.q_nonneg (p := r - 1) (by omega), hu.1], hu.2.trans (s.q_le_one (by omega))⟩
  have hv : HasDerivAt (mixedLeftSplitVariance ξ s r 1) (-ξ.second u) u := by
    change HasDerivAt (fun z => 1 * (ξ.first (s.q r) - ξ.first z)) (-ξ.second u) u
    simpa only [one_mul] using
      (ξ.hasDerivAt_first_unit hu0).const_sub (ξ.first (s.q r))
  have H := (hasDerivWithinAt_section4T_variance_factor (mixedClockScheme ξ s)
    (mixedBeta ξ) h hr0 hr hm hmm (hmap hu)).comp u hv.hasDerivWithinAt hmap
  have hu54 : |u| < 5 / 4 := by have hh := abs_le.mpr hu0; linarith
  have HP := ((ξ.hasDerivAt_correction hu54).const_sub (ξ.correction (s.q r))).const_mul
    ((s.m (r - 1) - m) / 2)
  convert! ((H.const_add (Real.log 2)).sub_const (mixedSchemeCorrection ξ s)).add
    HP.hasDerivWithinAt using 1
  simp only [mixedClockScheme_m]
  ring

def mixedSection4FirstVariation (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r 1 u) / 2 -
    (ξ.correction (s.q r) - ξ.correction u) / 2

theorem hasDerivAt_mixedSection4Phi_mass_baseline (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    HasDerivAt (fun m => mixedSection4Phi ξ s h r m u)
      (mixedSection4FirstVariation ξ s h r u) (s.m (r - 1)) := by
  have hT := hasDerivAt_section4T_mass_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h
    hr0 hr (mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu)
  have hC := ((hasDerivAt_id (s.m (r - 1))).const_sub (s.m (r - 1))).div_const 2 |>.mul_const
    (ξ.correction (s.q r) - ξ.correction u)
  convert! ((hT.const_add (Real.log 2)).sub_const (mixedSchemeCorrection ξ s)).add hC using 1
  simp only [mixedSection4FirstVariation]
  ring

/-- Genuine one-sided stationarity at a positive physical overlap; no
positivity of ξ″(0) is assumed. -/
theorem mixed_overlap_le_endpointQ_of_min (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hq : s.q (r - 1) < s.q r)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    s.q r ≤ section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1)) 0 := by
  have hd := hasDerivWithinAt_mixedSection4Phi_overlap ξ s h hr0 hr
    ⟨s.m_nonneg hr, s.m_le_one hr⟩ hm.le (u := s.q r) ⟨hq.le, le_rfl⟩
  simp only [mixedLeftSplitVariance, sub_self, mul_zero] at hd
  rw [section4TVarianceQ_zero_mass_independent (mixedClockScheme ξ s) (mixedBeta ξ) h
    hr0 hr (s.m r) (s.m (r - 1))] at hd
  have H := derivative_nonpos_of_min_at_right hq (f := mixedSection4Phi ξ s h r (s.m r))
    (fun u hu => by
      rw [mixedSection4Phi_at_upper_overlap ξ s h hr0 hr]
      simpa only [mixedSection4Phi_baseline ξ s h hr0 hr hu] using
        mixedSection4Phi_upper_mass_min ξ s h hr0 hr hu hmin) hd
  have hsec := ξ.second_pos ⟨(s.q_nonneg (p := r - 1) (by omega)).trans_lt hq, s.q_le_one (by omega)⟩
  have hc : 0 < ξ.second (s.q r) * (s.m r - s.m (r - 1)) / 2 :=
    div_pos (mul_pos hsec (sub_pos.mpr hm)) (by norm_num)
  nlinarith

end FourPapersCommon
