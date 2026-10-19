module
public import FourPapersCommon.MixedScalarComparison
public import FourPapersCommon.MixedRightOptimality
public import Targets.Section4RightConvexity

@[expose] public section

/-! Physical mixed far-right scalar witnesses, with the genuine mixed
tangent remainder and the actual inserted-mass near-optimality estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem mixedSection4RightU_interpolation_slope_upper_bound
    (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (hm : 0 < s.m r) {u t : ℝ}
    (hu : u ∈ Icc (s.q r) (s.q (r + 1))) (ht : t ∈ Icc (0 : ℝ) 1) :
    section4RightU (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedRightSplitVariance ξ s r t u) -
      t * (ξ.correction u - ξ.correction (s.q r)) ≤
    2 * mixedSection4RightFirstVariation ξ s h r u -
      (1 - t) * ξ.tangentRemainder u (s.q r) -
      (1 - t) * (ξ.first u - ξ.first (s.q r)) *
        (section4RightQ (mixedClockScheme ξ s) (mixedBeta ξ) h r
          (mixedRightSplitVariance ξ s r t u) - u) := by
  have hv := mixedRightSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu
  have htv := mixedRightSplitVariance_mem ξ s hr ht hu
  have H := section4RightU_ge_supportingLine (mixedClockScheme ξ s) (mixedBeta ξ) h hr hm htv hv
  simp only [mixedSection4RightFirstVariation, mixedRightSplitVariance, one_mul,
    AdmissibleEvenMixture.correction, AdmissibleEvenMixture.tangentRemainder]
  simp only [mixedRightSplitVariance, one_mul] at H
  nlinarith only [H]

def mixedRightComparison (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (m ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * Real.log 2 + section5RightV (mixedClockScheme ξ s) (mixedBeta ξ) h r m
    (mixedRightSplitVariance ξ s r p.1 p.2) ℓ - ℓ * p.2 -
    p.1 * (2 * mixedSchemeCorrection ξ s +
      (m - s.m r) * (ξ.correction p.2 - ξ.correction (s.q r)))

def mixedRightComparisonDeficit (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (m ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * mixedInterpolationPsi ξ s h p.1 - mixedRightComparison ξ s h r m ℓ p

theorem continuousOn_mixedRightComparison (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ)
    {S : Set (ℝ × ℝ)} (hS : ∀ p ∈ S, p.2 ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (mixedRightComparison ξ s h r m ℓ) S := by
  have hfirst : ContinuousOn (fun p : ℝ × ℝ => ξ.first p.2) S :=
    ξ.continuousOn_first.comp continuous_snd.continuousOn
      (fun p hp => ⟨by linarith [(hS p hp).1], (hS p hp).2⟩)
  have hcorr : ContinuousOn (fun p : ℝ × ℝ => ξ.correction p.2) S := by
    have hc : ContinuousOn ξ.correction (Icc (0 : ℝ) 1) := fun x hx =>
      (ξ.hasDerivAt_correction (by rw [abs_of_nonneg hx.1]; linarith [hx.2])).continuousAt.continuousWithinAt
    exact hc.comp continuous_snd.continuousOn hS
  have hv : ContinuousOn (fun p : ℝ × ℝ => (mixedRightSplitVariance ξ s r p.1 p.2, ℓ)) S :=
    (continuous_fst.continuousOn.mul (hfirst.sub continuousOn_const)).prodMk continuousOn_const
  have HV := (continuous_section5RightV_variance_lambda (mixedClockScheme ξ s) (mixedBeta ξ) h hr hm).comp_continuousOn hv
  unfold mixedRightComparison
  exact ((continuousOn_const.add HV).sub (continuousOn_const.mul continuous_snd.continuousOn)).sub
    (continuous_fst.continuousOn.mul (continuousOn_const.add
      (continuousOn_const.mul (hcorr.sub continuousOn_const))))

theorem continuousOn_mixedRightComparisonDeficit (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ)
    {S : Set (ℝ × ℝ)} (hS : ∀ p ∈ S, p.2 ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (mixedRightComparisonDeficit ξ s h r m ℓ) S := by
  have H : Continuous (fun p : ℝ × ℝ => 2 * mixedInterpolationPsi ξ s h p.1) := by
    unfold mixedInterpolationPsi
    fun_prop
  exact H.continuousOn.sub (continuousOn_mixedRightComparison ξ s h hr hm ℓ hS)

theorem exists_mixedRightMass_improvement (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k + 1)
    (hmpos : 0 < s.m r) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (s.q r) (s.q (r + 1)))
    (hD : section4RightU (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedRightSplitVariance ξ s r t u) -
      t * (ξ.correction u - ξ.correction (s.q r)) < 0) :
    ∃ m ∈ Icc (s.m r) (2 * s.m r),
      2 * section4RightT (mixedClockScheme ξ s) (mixedBeta ξ) h r m (mixedRightSplitVariance ξ s r t u) -
        (m - s.m r) * t * (ξ.correction u - ξ.correction (s.q r)) <
      2 * section4RightT (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m r) (mixedRightSplitVariance ξ s r t u) := by
  let v := mixedRightSplitVariance ξ s r t u
  let c := t * (ξ.correction u - ξ.correction (s.q r))
  let f := fun m => 2 * section4RightT (mixedClockScheme ξ s) (mixedBeta ξ) h r m v - (m - s.m r) * c
  have hv := mixedRightSplitVariance_mem ξ s hr ht hu
  have hd : HasDerivAt f (section4RightU (mixedClockScheme ξ s) (mixedBeta ξ) h r v - c) (s.m r) := by
    convert! ((hasDerivAt_section4RightT_mass_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv.1).const_mul 2).sub
      (((hasDerivAt_id (s.m r)).sub_const (s.m r)).mul_const c) using 1
    ring
  by_contra! H
  have hmin : ∀ m ∈ Icc (s.m r) (2 * s.m r), f (s.m r) ≤ f m := by
    intro m hm
    have HH := H m hm
    dsimp [f, v, c]
    nlinarith only [HH]
  have Hnonneg := derivative_nonneg_of_min_at_left (by linarith : s.m r < 2 * s.m r) hmin hd.hasDerivWithinAt
  exact (not_le_of_gt hD) Hnonneg

theorem exists_mixedRightComparison_witness_of_gap (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
      (1 - t) * ξ.tangentRemainder u (s.q r)) :
    ∃ m ∈ Icc (s.m (r - 1)) (2 * s.m r), ∃ ℓ : ℝ,
      0 < mixedRightComparisonDeficit ξ s h r m ℓ (t, u) := by
  have hv := mixedRightSplitVariance_mem ξ s hr ht hu
  have hmpos : 0 < s.m r := (s.m_nonneg (by omega)).trans_lt hgap
  by_cases hQ : section4RightQ (mixedClockScheme ξ s) (mixedBeta ξ) h r
      (mixedRightSplitVariance ξ s r t u) = u
  · have hf := mixedSection4RightFirstVariation_upper_bound ξ s h ε hr0 hr hgap hu hmin hnear
    have HD := mixedSection4RightU_interpolation_slope_upper_bound ξ s h hr hmpos hu ht
    rw [hQ, sub_self, mul_zero, sub_zero] at HD
    have hD : section4RightU (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedRightSplitVariance ξ s r t u) -
        t * (ξ.correction u - ξ.correction (s.q r)) < 0 := by linarith
    obtain ⟨m, hm, H⟩ := exists_mixedRightMass_improvement ξ s h hr hmpos ht hu hD
    refine ⟨m, ⟨hgap.le.trans hm.1, hm.2⟩, 0, ?_⟩
    have hm0 : 0 ≤ m := hmpos.le.trans hm.1
    unfold mixedRightComparisonDeficit mixedRightComparison
    rw [section5RightV_zero_eq_two_section4RightT (mixedClockScheme ξ s) (mixedBeta ξ) h hr hm0 hv]
    have HB := section4RightT_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv
    simp only [mixedClockScheme_m] at HB
    rw [HB] at H
    simp only [zero_mul, sub_zero, mixedInterpolationPsi]
    nlinarith only [H]
  · obtain ⟨ℓ, H⟩ := section5RightV_lambda_gain (mixedClockScheme ξ s) (mixedBeta ξ) h hr
      (m := s.m r) ⟨hmpos.le, (s.m_le_one hr).trans (by norm_num)⟩
      (mixedRightSplitVariance ξ s r t u) u
    have HB := section5RightV_zero_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv
    have HD := deriv_section5RightV_zero_eq_Q_all_levels (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv
    simp only [mixedClockScheme_m] at HB HD
    rw [HB, HD] at H
    refine ⟨s.m r, ⟨hgap.le, by linarith⟩, ℓ, ?_⟩
    have HP := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hQ)) (by norm_num : (0 : ℝ) < 2)
    unfold mixedRightComparisonDeficit mixedRightComparison mixedInterpolationPsi
    simp only [sub_self, zero_mul, add_zero]
    linarith

theorem exists_mixedRightComparison_compact_witnesses
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hgap : s.m (r - 1) < s.m r)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) 1)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : ∀ z ∈ S, 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
      (1 - z.1) * ξ.tangentRemainder z.2 (s.q r)) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∃ m ∈ Icc (s.m (r - 1)) (2 * s.m r), ∃ ℓ : ℝ,
      δ ≤ mixedRightComparisonDeficit ξ s h r m ℓ z := by
  let I := {m : ℝ // m ∈ Icc (s.m (r - 1)) (2 * s.m r)} × ℝ
  let f := fun (i : I) => mixedRightComparisonDeficit ξ s h r i.1.1 i.2
  have hc (i : I) : ContinuousOn (f i) S :=
    continuousOn_mixedRightComparisonDeficit ξ s h hr
      ((s.m_nonneg (by omega)).trans i.1.2.1) i.2
      (fun z hz => ⟨(s.q_nonneg (by omega)).trans (hu z hz).1,
        (hu z hz).2.trans (s.q_le_one (by omega))⟩)
  have hp : ∀ z ∈ S, ∃ i : I, 0 < f i z := by
    intro z hz
    obtain ⟨m, hm, ℓ, H⟩ := exists_mixedRightComparison_witness_of_gap ξ s h ε
      hr0 hr hgap (ht z hz) (hu z hz) hmin hnear (hsmall z hz)
    exact ⟨(⟨m, hm⟩, ℓ), H⟩
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses hS f hc hp
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  obtain ⟨i, hi⟩ := Hδ z hz
  exact ⟨i.1.1, i.1.2, i.2, hi⟩

end FourPapersCommon
