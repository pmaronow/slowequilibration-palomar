module
public import FourPapersCommon.MixedPressureGain
public import Targets.Section4Concavity

@[expose] public section

/-! Actual downward mass gain and the physical mixed supporting-line gap.
These inequalities retain the genuine mixed theta correction and do not
assume a constrained-pressure bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

theorem mixed_constrainedPhi_le_two_Psi_sub_mass_gain
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (hmpos : 0 < s.m (r - 1))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hD : 0 < section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r t u) -
      t * (ξ.correction (s.q r) - ξ.correction u)) :
    let D := section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r t u) -
      t * (ξ.correction (s.q r) - ξ.correction u)
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤ 2 * mixedInterpolationPsi ξ s h t -
      D / 2 * min (s.m (r - 1) / 2) (D / (4 * (section4MassSecondBound ((mixedBeta ξ) ^ 2) + 1))) := by
  let a := s.m (r - 1)
  let C := section4MassSecondBound ((mixedBeta ξ) ^ 2)
  let D := section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r t u) -
    t * (ξ.correction (s.q r) - ξ.correction u)
  let δ := min (a / 2) (D / (4 * (C + 1)))
  have hC : 0 ≤ C := section4MassSecondBound_nonneg _
  have hden : 0 < 4 * (C + 1) := by positivity
  have hδ : 0 < δ := lt_min (by dsimp [a]; linarith) (div_pos hD hden)
  have hδa : δ ≤ a / 2 := min_le_left _ _
  have hδD : 4 * (C + 1) * δ ≤ D := by
    have H := (le_div_iff₀ hden).mp (min_le_right (a / 2) (D / (4 * (C + 1))))
    simpa only [mul_comm] using H
  have hm : a - δ ∈ Set.Icc (s.m (r - 1) / 2) (s.m r) := by
    have ha : a ≤ s.m r := s.m_mono' r hr (r - 1) (by omega)
    change a / 2 ≤ a - δ ∧ a - δ ≤ s.m r
    constructor <;> linarith
  have H := mixed_constrainedPhi_le_two_Psi_mass_taylor hn ξ s h sk hr0 hr hm ht hu
  change constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
    2 * mixedInterpolationPsi ξ s h t + D * (a - δ - a) + 2 * C * (a - δ - a) ^ 2 at H
  have HC := mul_le_mul_of_nonneg_right hδD hδ.le
  change constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤ 2 * mixedInterpolationPsi ξ s h t - D / 2 * δ
  nlinarith only [H, HC, sq_nonneg δ]

/-- Strict improvement from the explicit positive mass deficit. The initial
mass-zero interval is deliberately excluded from this downward variation. -/
theorem mixed_constrainedPhi_lt_two_Psi_of_mass_slope_pos
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (hmpos : 0 < s.m (r - 1))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hD : 0 < section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r t u) -
      t * (ξ.correction (s.q r) - ξ.correction u)) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u < 2 * mixedInterpolationPsi ξ s h t := by
  have H := mixed_constrainedPhi_le_two_Psi_sub_mass_gain hn ξ s h sk hr0 hr hmpos ht hu hD
  have hden : 0 < 4 * (section4MassSecondBound ((mixedBeta ξ) ^ 2) + 1) := by
    linarith [section4MassSecondBound_nonneg ((mixedBeta ξ) ^ 2)]
  exact H.trans_lt (sub_lt_self _ (mul_pos (div_pos hD (by norm_num))
    (lt_min (by linarith) (div_pos hD hden))))


omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem mixedSection4U_interpolation_slope_lower_bound
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1)
    {u t : ℝ} (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) (ht : t ∈ Icc (0 : ℝ) 1) :
    2 * mixedSection4FirstVariation ξ s h r u +
      (1 - t) * ξ.tangentRemainder u (s.q r) -
      (1 - t) * (ξ.first (s.q r) - ξ.first u) *
        (section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1))
          (mixedLeftSplitVariance ξ s r t u) - u) ≤
    section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r t u) -
      t * (ξ.correction (s.q r) - ξ.correction u) := by
  have hv := mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu
  have H := section4U_sub_ge_supportingLine (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hm hv ht
  simp only [mixedClockScheme_m] at H
  have htv : t * mixedLeftSplitVariance ξ s r 1 u = mixedLeftSplitVariance ξ s r t u := by
    simp only [mixedLeftSplitVariance, one_mul]
  rw [htv] at H
  simp only [mixedSection4FirstVariation, mixedLeftSplitVariance, one_mul,
    AdmissibleEvenMixture.correction, AdmissibleEvenMixture.tangentRemainder]
  simp only [mixedLeftSplitVariance, one_mul] at H
  nlinarith only [H]

theorem mixed_constrainedPhi_lt_two_Psi_of_left_gap
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : 2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
      (1 - t) * ξ.tangentRemainder u (s.q r)) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u <
      2 * mixedInterpolationPsi ξ s h t := by
  by_cases hQ : section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1))
      (mixedLeftSplitVariance ξ s r t u) = u
  · have hf := mixedSection4FirstVariation_lower_bound ξ s h ε hr0 hr hgap hu hmin hnear
    have H := mixedSection4U_interpolation_slope_lower_bound ξ s h hr0 hr
      (hgap.trans_le (s.m_le_one hr)) hu ht
    rw [hQ, sub_self, mul_zero, sub_zero] at H
    apply mixed_constrainedPhi_lt_two_Psi_of_mass_slope_pos hn ξ s h sk hr0 hr hmpos ht hu
    linarith
  · have H := mixed_constrainedPhi_le_two_Psi_sub_left_factor_sq hn ξ s h sk hr0 hr ht hu
    have Hpos := sq_pos_of_ne_zero (sub_ne_zero.mpr hQ)
    linarith

end FourPapersCommon
