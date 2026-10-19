module
public import FourPapersCommon.MixedCubicTaylor
public import FourPapersCommon.MixedTerminalStationarity
public import FourPapersCommon.MixedQuantitativeOptimality
public import Targets.Section4Curvature

@[expose] public section

/-! Genuine mixed stationarity and the sixth-root near-minimum curvature estimate. -/
noncomputable section
open Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem mixed_endpointQ_eq_overlap_of_min_all_levels (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1)) 0 = s.q r := by
  by_cases hrk : r ≤ k
  · exact mixed_endpointQ_eq_overlap_of_min_nonterminal ξ s h hr0 hrk hm hleft hright hmin
  · have he : r = k + 1 := by omega
    subst r
    simp only [Nat.add_sub_cancel, s.m_top] at hm hleft ⊢
    exact mixed_endpointQ_eq_overlap_of_min_terminal ξ s h hm hleft hmin

theorem mixedSection4FirstVariationD_upper_zero (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    mixedSection4FirstVariationD ξ s h r (s.q r) = 0 := by
  simp only [mixedSection4FirstVariationD, mixedSection4Q, mixedLeftSplitVariance,
    sub_self, mul_zero, mixed_endpointQ_eq_overlap_of_min_all_levels ξ s h hr0 hr hm hleft hright hmin]

theorem mixedSection4FirstVariationD2_upper (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) :
    mixedSection4FirstVariationD2 ξ s h r (s.q r) =
      ξ.second (s.q r) / 2 * (1 - ξ.second (s.q r) *
        section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h r 0) := by
  simp only [mixedSection4FirstVariationD2, mixedSection4Q, mixedSection4R, mixedLeftSplitVariance,
    sub_self, mul_zero, mixed_endpointQ_eq_overlap_of_min_all_levels ξ s h hr0 hr hm hleft hright hmin,
    sub_self, mul_zero, zero_add]

theorem mixedSection4FirstVariation_stationary_cubic (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    {u : ℝ} (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    |mixedSection4FirstVariation ξ s h r u -
      mixedSection4FirstVariationD2 ξ s h r (s.q r) / 2 * (u - s.q r) ^ 2| ≤
      mixedCurvatureLipschitz ξ * |u - s.q r| ^ 3 := by
  have H := mixedSection4FirstVariation_cubic_taylor ξ s h hr0 hr
    (hm.trans_le (s.m_le_one hr)) hu
    (show s.q r ∈ Icc (s.q (r - 1)) (s.q r) from ⟨s.q_mono' r (by omega) (r - 1) (by omega), le_rfl⟩)
  simpa only [mixedSection4FirstVariation_upper ξ s h hr0 hr,
    mixedSection4FirstVariationD_upper_zero ξ s h hr0 hr hm hleft hright hmin,
    zero_mul, sub_zero] using H

theorem mixedSection4FirstVariation_noninitial_curvature_bound (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε) :
    -mixedSection4FirstVariationD2 ξ s h r (s.q r) ≤
      2 * (mixedCurvatureLipschitz ξ + section4OptimalityBound (mixedBeta ξ)) * ε ^ (1 / 6 : ℝ) := by
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  exact neg_curvature_le_sixth_root_of_cubic_remainder hleft
    (mixedCurvatureLipschitz_nonneg ξ) (section4OptimalityBound_pos (mixedBeta ξ)).le hε
    (mixedSection4FirstVariation_lower_nonneg ξ s h hr0 hr hm hmin)
    (fun u hu => mixedSection4FirstVariation_lower_bound ξ s h ε (by omega) hr hm hu hmin hnear)
    (fun u hu => mixedSection4FirstVariation_stationary_cubic ξ s h (by omega) hr hm (Or.inl hleft) hright hmin hu)

private theorem mixed_neg_curvature_le_long_gap_pos
    {f : ℝ → ℝ} {a b κ C L η : ℝ} (hη : 0 < η) (hgap : η ≤ b - a)
    (hlower : ∀ u ∈ Set.Icc a b, -L * η ^ 3 ≤ f u)
    (hupper : ∀ u ∈ Set.Icc a b,
      f u ≤ κ / 2 * (b - u) ^ 2 + C * (b - u) ^ 3) :
    -κ ≤ 2 * (C + L) * η := by
  have hu : b - η ∈ Set.Icc a b := by constructor <;> linarith
  have H := (hlower (b - η) hu).trans (hupper (b - η) hu)
  have Hprod : 0 ≤ (κ / 2 + (C + L) * η) * η ^ 2 := by
    nlinarith only [H]
  have Hslope := nonneg_of_mul_nonneg_left Hprod (sq_pos_of_pos hη)
  linarith

theorem mixed_neg_curvature_le_long_gap
    {f : ℝ → ℝ} {a b κ C L η : ℝ} (hab : a < b) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hη : 0 ≤ η) (hgap : η ≤ b - a)
    (hlower : ∀ u ∈ Set.Icc a b, -L * η ^ 3 ≤ f u)
    (hupper : ∀ u ∈ Set.Icc a b,
      f u ≤ κ / 2 * (b - u) ^ 2 + C * (b - u) ^ 3) :
    -κ ≤ 2 * (C + L) * η := by
  rcases eq_or_lt_of_le hη with hzero | hpos
  · subst η
    simp only [zero_pow (by norm_num : 3 ≠ 0), mul_zero] at hlower ⊢
    by_contra hn
    have hκ : 0 < -κ := lt_of_not_ge hn
    let δ := min ((b - a) / 2) (-κ / (4 * (C + L + 1)))
    have hden : 0 < 4 * (C + L + 1) := by linarith
    have hδ : 0 < δ := lt_min (by linarith) (div_pos hκ hden)
    have hδgap : δ ≤ b - a := (min_le_left _ _).trans (by linarith)
    have H := mixed_neg_curvature_le_long_gap_pos hδ hδgap
      (fun u hu => (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL)
        (pow_nonneg hδ.le 3)).trans (hlower u hu)) hupper
    have he : δ * (4 * (C + L + 1)) ≤ -κ :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith only [H, he, hδ, mul_nonneg hC hδ.le, mul_nonneg hL hδ.le]
  · exact mixed_neg_curvature_le_long_gap_pos hpos hgap hlower hupper


theorem mixedSection4FirstVariation_long_initial_curvature_bound (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h ε : ℝ) (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hlong : ε ^ (1 / 6 : ℝ) ≤ s.q 1) :
    -mixedSection4FirstVariationD2 ξ s h 1 (s.q 1) ≤
      2 * (mixedCurvatureLipschitz ξ + section4OptimalityBound (mixedBeta ξ)) * ε ^ (1 / 6 : ℝ) := by
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  have hpower : (ε ^ (1 / 6 : ℝ)) ^ (3 : ℕ) = Real.sqrt ε := by
    rw [← Real.rpow_mul_natCast hε, Real.sqrt_eq_rpow]
    norm_num
  apply mixed_neg_curvature_le_long_gap hq (mixedCurvatureLipschitz_nonneg ξ)
    (section4OptimalityBound_pos (mixedBeta ξ)).le (Real.rpow_nonneg hε _) (by simpa only [sub_zero] using hlong)
    (f := mixedSection4FirstVariation ξ s h 1)
  · intro u hu
    rw [hpower]
    exact mixedSection4FirstVariation_lower_bound ξ s h ε (r := 1) le_rfl (by omega)
      (by simpa only [Nat.sub_self] using hm) (by simpa only [Nat.sub_self, s.q_zero] using hu) hmin hnear
  · intro u hu
    have H := (abs_le.mp (mixedSection4FirstVariation_stationary_cubic ξ s h (r := 1)
      le_rfl (by omega) (by simpa only [Nat.sub_self] using hm)
      (Or.inl (by simpa only [Nat.sub_self, s.q_zero] using hq)) hright hmin
      (by simpa only [Nat.sub_self, s.q_zero] using hu))).2
    rw [abs_of_nonpos (sub_nonpos.mpr hu.2)] at H
    nlinarith only [H]

/-- Removing the positive curvature weight does not require a lower bound
on ξ″. If ξ″≤1 the probabilistic range of R already supplies the estimate. -/
theorem mixed_instability_le_of_weighted_curvature {S R E : ℝ}
    (hS : 0 ≤ S) (hR : R ∈ Icc (0 : ℝ) 1) (hE : 0 ≤ E)
    (hcurv : -(S / 2 * (1 - S * R)) ≤ E) : S * R - 1 ≤ 2 * E := by
  by_cases hsmall : S * R ≤ 1
  · linarith
  · have hS1 : 1 ≤ S := by nlinarith only [hsmall, hR.2, hS]
    have H := mul_le_mul_of_nonneg_right hS1 (by linarith : 0 ≤ S * R - 1)
    nlinarith only [H, hcurv]

theorem mixed_noninitial_instability_bound (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε) :
    ξ.second (s.q r) * section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h r 0 - 1 ≤
      4 * (mixedCurvatureLipschitz ξ + section4OptimalityBound (mixedBeta ξ)) * ε ^ (1 / 6 : ℝ) := by
  have H := mixedSection4FirstVariation_noninitial_curvature_bound ξ s h ε hr0 hr hm hleft hright hmin hnear
  rw [mixedSection4FirstVariationD2_upper ξ s h (by omega) hr hm (Or.inl hleft) hright hmin] at H
  have HE : 0 ≤ 2 * (mixedCurvatureLipschitz ξ + section4OptimalityBound (mixedBeta ξ)) * ε ^ (1 / 6 : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (mixedCurvatureLipschitz_nonneg ξ)
      (section4OptimalityBound_pos (mixedBeta ξ)).le)) (Real.rpow_nonneg (by
        have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
          rw [← mixedMinimizer_value ξ h]; exact isMixedMinimizer_selected ξ h _
        linarith) _)
  have HH := mixed_instability_le_of_weighted_curvature (ξ.second_nonneg (s.q r))
    (section4THessianSquare_mem_Icc (mixedClockScheme ξ s) (mixedBeta ξ) h hr 0) HE H
  nlinarith only [HH]

end FourPapersCommon
