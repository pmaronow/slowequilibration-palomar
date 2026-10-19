module
public import FourPapersCommon.MixedMassGain
public import FourPapersCommon.MixedSecondInterpolationComparison
public import Targets.Section5ScalarComparisonContinuity
public import Targets.Section5CompactWitness

@[expose] public section

/-! True scalar witnesses and compact finite-model gaps for physical mixed
left intervals. Witness continuity concerns the actual scalar recursion, not
the discrete constrained free energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def mixedLeftComparison (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (m ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * Real.log 2 + section5V (mixedClockScheme ξ s) (mixedBeta ξ) h r m
    (mixedLeftSplitVariance ξ s r p.1 p.2) ℓ - ℓ * p.2 -
    p.1 * (2 * mixedSchemeCorrection ξ s +
      (m - s.m (r - 1)) * (ξ.correction (s.q r) - ξ.correction p.2))

def mixedLeftComparisonDeficit (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (m ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * mixedInterpolationPsi ξ s h p.1 - mixedLeftComparison ξ s h r m ℓ p

theorem continuousOn_mixedLeftComparison (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ)
    {S : Set (ℝ × ℝ)} (hS : ∀ p ∈ S, p.2 ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (mixedLeftComparison ξ s h r m ℓ) S := by
  have hfirst : ContinuousOn (fun p : ℝ × ℝ => ξ.first p.2) S :=
    ξ.continuousOn_first.comp continuous_snd.continuousOn (fun p hp => ⟨by linarith [(hS p hp).1], (hS p hp).2⟩)
  have hcorr : ContinuousOn (fun p : ℝ × ℝ => ξ.correction p.2) S := by
    have hc : ContinuousOn ξ.correction (Icc (0 : ℝ) 1) := fun x hx =>
      (ξ.hasDerivAt_correction (by rw [abs_of_nonneg hx.1]; linarith [hx.2])).continuousAt.continuousWithinAt
    exact hc.comp continuous_snd.continuousOn hS
  have hv : ContinuousOn (fun p : ℝ × ℝ => (mixedLeftSplitVariance ξ s r p.1 p.2, ℓ)) S := by
    exact (continuous_fst.continuousOn.mul (continuousOn_const.sub hfirst)).prodMk continuousOn_const
  have HV := (continuous_section5V_variance_lambda (mixedClockScheme ξ s) (mixedBeta ξ) h hr hm).comp_continuousOn hv
  unfold mixedLeftComparison
  exact ((continuousOn_const.add HV).sub (continuousOn_const.mul continuous_snd.continuousOn)).sub
    (continuous_fst.continuousOn.mul (continuousOn_const.add
      (continuousOn_const.mul (continuousOn_const.sub hcorr))))

theorem continuousOn_mixedLeftComparisonDeficit (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ)
    {S : Set (ℝ × ℝ)} (hS : ∀ p ∈ S, p.2 ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (mixedLeftComparisonDeficit ξ s h r m ℓ) S := by
  have H : Continuous (fun p : ℝ × ℝ => 2 * mixedInterpolationPsi ξ s h p.1) := by
    unfold mixedInterpolationPsi
    fun_prop
  exact H.continuousOn.sub (continuousOn_mixedLeftComparison ξ s h hr hm ℓ hS)

theorem exists_mixedLeftMass_improvement (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hmpos : 0 < s.m (r - 1)) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hD : 0 < section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r t u) -
      t * (ξ.correction (s.q r) - ξ.correction u)) :
    ∃ m ∈ Icc (s.m (r - 1) / 2) (s.m (r - 1)),
      2 * section4T (mixedClockScheme ξ s) (mixedBeta ξ) h r m (mixedLeftSplitVariance ξ s r t u) -
        (m - s.m (r - 1)) * t * (ξ.correction (s.q r) - ξ.correction u) <
      2 * section4T (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1)) (mixedLeftSplitVariance ξ s r t u) := by
  let v := mixedLeftSplitVariance ξ s r t u
  let c := t * (ξ.correction (s.q r) - ξ.correction u)
  let f := fun m => 2 * section4T (mixedClockScheme ξ s) (mixedBeta ξ) h r m v - (m - s.m (r - 1)) * c
  have hv := mixedLeftSplitVariance_mem ξ s hr ht hu
  have hd : HasDerivAt f (section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r v - c) (s.m (r - 1)) := by
    convert! ((hasDerivAt_section4T_mass_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv).const_mul 2).sub
      (((hasDerivAt_id (s.m (r - 1))).sub_const (s.m (r - 1))).mul_const c) using 1
    ring
  by_contra! H
  have hmin : ∀ m ∈ Icc (s.m (r - 1) / 2) (s.m (r - 1)), f (s.m (r - 1)) ≤ f m := by
    intro m hm
    have HH := H m hm
    dsimp [f, v, c]
    nlinarith only [HH]
  have Hnonpos := derivative_nonpos_of_min_at_right (by linarith : s.m (r - 1) / 2 < s.m (r - 1)) hmin hd.hasDerivWithinAt
  exact (not_le_of_gt hD) Hnonpos

theorem exists_mixedLeftComparison_witness_of_gap (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
      (1 - t) * ξ.tangentRemainder u (s.q r)) :
    ∃ m ∈ Icc (s.m (r - 1) / 2) (s.m r), ∃ ℓ : ℝ,
      0 < mixedLeftComparisonDeficit ξ s h r m ℓ (t, u) := by
  have hv := mixedLeftSplitVariance_mem ξ s hr ht hu
  by_cases hQ : section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1))
      (mixedLeftSplitVariance ξ s r t u) = u
  · have hf := mixedSection4FirstVariation_lower_bound ξ s h ε hr0 hr hgap hu hmin hnear
    have HD := mixedSection4U_interpolation_slope_lower_bound ξ s h hr0 hr (hgap.trans_le (s.m_le_one hr)) hu ht
    rw [hQ, sub_self, mul_zero, sub_zero] at HD
    have hD : 0 < section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r t u) -
        t * (ξ.correction (s.q r) - ξ.correction u) := by linarith
    obtain ⟨m, hm, H⟩ := exists_mixedLeftMass_improvement ξ s h hr0 hr hmpos ht hu hD
    refine ⟨m, ⟨hm.1, hm.2.trans hgap.le⟩, 0, ?_⟩
    have hm0 : 0 ≤ m := (div_nonneg hmpos.le (by norm_num)).trans hm.1
    unfold mixedLeftComparisonDeficit mixedLeftComparison
    rw [section5V_zero_eq_two_section4T (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hm0 hv]
    have HB := section4T_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv
    simp only [mixedClockScheme_m] at HB
    rw [HB] at H
    simp only [zero_mul, sub_zero, mixedInterpolationPsi]
    nlinarith only [H]
  · obtain ⟨ℓ, H⟩ := section5V_baseline_lambda_gain_Q (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv u
    simp only [mixedClockScheme_m] at H
    refine ⟨s.m (r - 1), ⟨by linarith, hgap.le⟩, ℓ, ?_⟩
    have HP := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hQ)) (by norm_num : (0 : ℝ) < 2)
    unfold mixedLeftComparisonDeficit mixedLeftComparison mixedInterpolationPsi
    simp only [sub_self, zero_mul, add_zero]
    linarith

/- The compactness selection takes place entirely in the scalar recursion.
Keeping it separate makes the resulting margin usable for a sequence of
finite models whose probability spaces depend on the system size. -/
theorem exists_mixedLeftComparison_compact_witnesses
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hmpos : 0 < s.m (r - 1))
    (hgap : s.m (r - 1) < s.m r)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) 1)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : ∀ z ∈ S, 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
      (1 - z.1) * ξ.tangentRemainder z.2 (s.q r)) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∃ m ∈ Icc (s.m (r - 1) / 2) (s.m r), ∃ ℓ : ℝ,
      δ ≤ mixedLeftComparisonDeficit ξ s h r m ℓ z := by
  let I := {m : ℝ // m ∈ Icc (s.m (r - 1) / 2) (s.m r)} × ℝ
  let f := fun (i : I) => mixedLeftComparisonDeficit ξ s h r i.1.1 i.2
  have hc (i : I) : ContinuousOn (f i) S :=
    continuousOn_mixedLeftComparisonDeficit ξ s h hr
      ((div_nonneg hmpos.le (by norm_num)).trans i.1.2.1) i.2
      (fun z hz => ⟨(s.q_nonneg (by omega)).trans (hu z hz).1,
        (hu z hz).2.trans (s.q_le_one (by omega))⟩)
  have hp : ∀ z ∈ S, ∃ i : I, 0 < f i z := by
    intro z hz
    obtain ⟨m, hm, ℓ, H⟩ := exists_mixedLeftComparison_witness_of_gap ξ s h ε
      hr0 hr hmpos hgap (ht z hz) (hu z hz) hmin hnear (hsmall z hz)
    exact ⟨(⟨m, hm⟩, ℓ), H⟩
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses hS f hc hp
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  obtain ⟨i, hi⟩ := Hδ z hz
  exact ⟨i.1.1, i.1.2, i.2, hi⟩

universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem mixed_constrainedPhi_le_leftComparison
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {m t u : ℝ} (hm : m ∈ Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] (ℓ : ℝ) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      mixedLeftComparison ξ s h r m ℓ (t, u) := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  have H := mixedLeftInterpolation_endpoint_bound hn ξ s h sk hr0 hr hm ht hu
  rw [mixedLeftPairCorrection_eq ξ s u m hr0 hr] at H
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  have H0 := mixedLeftInterpolation_zero_le hn ξ s h sk.U hr hm0 ht hu ⟨p.1.1, p.1.2, p.2⟩ ℓ
  dsimp only [mixedLeftComparison]
  linarith

theorem exists_mixed_constrainedPhi_compact_left_gap
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S) (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) 1)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : ∀ z ∈ S, 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
      (1 - z.1) * ξ.tangentRemainder z.2 (s.q r)) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n → ∀ sk : MixedDisorder (Ω := Ω) n ξ,
      Nonempty (AT.ConstrainedPair n z.2) →
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * mixedInterpolationPsi ξ s h z.1 - δ := by
  let I := {m : ℝ // m ∈ Icc (s.m (r - 1) / 2) (s.m r)} × ℝ
  let f := fun (i : I) => mixedLeftComparisonDeficit ξ s h r i.1.1 i.2
  have hc (i : I) : ContinuousOn (f i) S :=
    continuousOn_mixedLeftComparisonDeficit ξ s h hr ((div_nonneg hmpos.le (by norm_num)).trans i.1.2.1) i.2
      (fun z hz => ⟨(s.q_nonneg (by omega)).trans (hu z hz).1, (hu z hz).2.trans (s.q_le_one (by omega))⟩)
  have hp : ∀ z ∈ S, ∃ i : I, 0 < f i z := by
    intro z hz
    obtain ⟨m, hm, ℓ, H⟩ := exists_mixedLeftComparison_witness_of_gap ξ s h ε hr0 hr hmpos hgap
      (ht z hz) (hu z hz) hmin hnear (hsmall z hz)
    exact ⟨(⟨m, hm⟩, ℓ), H⟩
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses hS f hc hp
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  let := hatt
  obtain ⟨i, hi⟩ := Hδ z hz
  have H := mixed_constrainedPhi_le_leftComparison hn ξ s h sk hr0 hr i.1.2 (ht z hz) (hu z hz) i.2
  change δ ≤ 2 * mixedInterpolationPsi ξ s h z.1 - mixedLeftComparison ξ s h r i.1.1 i.2 z at hi
  exact H.trans (by linarith)

end FourPapersCommon
