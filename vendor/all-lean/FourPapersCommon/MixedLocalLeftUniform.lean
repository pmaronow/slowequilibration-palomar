module
public import FourPapersCommon.MixedLocalLeft
public import FourPapersCommon.MixedCurvatureUniform

@[expose] public section

/-! A genuine local quadratic pressure gain for actual near-minimizing mixed
schemes, with constants depending only on the covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000

def mixedLocalLeftConstant (ξ : AdmissibleEvenMixture) : ℝ :=
  32 + 4 * mixedLocalSlopeConstant ξ + 4 * mixedInstabilityConstant ξ

theorem mixedLocalLeftConstant_bounds (ξ : AdmissibleEvenMixture) :
    32 ≤ mixedLocalLeftConstant ξ ∧ 4 * mixedLocalSlopeConstant ξ ≤ mixedLocalLeftConstant ξ ∧
      4 * mixedInstabilityConstant ξ ≤ mixedLocalLeftConstant ξ := by
  have hL := mixedLocalSlopeConstant_nonneg ξ
  have hI := mixedInstabilityConstant_nonneg ξ
  dsimp [mixedLocalLeftConstant]
  constructor
  · linarith
  · constructor <;> linarith

theorem mixedLocalLeftConstant_pos (ξ : AdmissibleEvenMixture) : 0 < mixedLocalLeftConstant ξ := by
  linarith [mixedLocalLeftConstant_bounds ξ |>.1]

theorem mixedLeftSlope_ge_local_of_near_minimum (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (s.q r - u) ≤ 1 - t₀) :
    (1 - t₀) / 2 * (s.q r - u) ≤ mixedLeftSlope ξ s h r t u := by
  have hp : mixedPressure ξ h ≤ mixedFunctional ξ h (Paper.parisiSchemeMeasure s) := by
    rw [← mixedMinimizer_value ξ h]
    exact isMixedMinimizer_selected ξ h _
  have hε : 0 ≤ ε := by linarith
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  let e := mixedInstabilityConstant ξ * ε ^ (1 / 6 : ℝ)
  have he : 0 ≤ e := mul_nonneg (mixedInstabilityConstant_nonneg ξ) hη
  have hc := mixedLocalLeftConstant_bounds ξ
  have he_small : e ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.2 hη
    change 4 * mixedInstabilityConstant ξ * ε ^ (1 / 6 : ℝ) ≤ _ at H
    dsimp [e]
    nlinarith only [H, hsmall]
  have hu_small : mixedLocalSlopeConstant ξ * (s.q r - u) ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.1 (sub_nonneg.mpr hu.2)
    nlinarith only [H, hlocal]
  have Hcurv := mixed_instability_bound_all_levels ξ s h ε hr0 hr hm hleft hright hmin hnear
  have hR : ξ.second (s.q r) * section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h r 0 ≤ 1 + e := by
    dsimp [e]
    linarith
  exact mixedLeftSlope_ge_local_of_endpoint_curvature ξ s h hr0 hr ht ht₀ he hu
    (mixed_endpointQ_eq_overlap_of_min_all_levels ξ s h hr0 hr hm (Or.inl hleft) hright hmin)
    hR he_small hu_small

theorem exists_mixedLeft_lambda_local_gain (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (s.q r - u) ≤ 1 - t₀) :
    ∃ ℓ : ℝ, section5V (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1))
      (mixedLeftSplitVariance ξ s r t u) ℓ - ℓ * u ≤
        2 * parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
          (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 := by
  have HS := mixedLeftSlope_ge_local_of_near_minimum ξ s h ε hr0 hr hm hleft hright
    ht ht₀ hu hmin hnear hsmall hlocal
  obtain ⟨ℓ, HL⟩ := section5V_baseline_lambda_gain_Q (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr
    (mixedLeftSplitVariance_mem ξ s hr ⟨ht.1, ht.2.trans ht₀.le⟩ hu) u
  simp only [mixedClockScheme_m] at HL
  change _ ≤ 2 * parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h - (mixedLeftSlope ξ s h r t u) ^ 2 / 2 at HL
  have HN : 0 ≤ (1 - t₀) / 2 * (s.q r - u) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.2)
  have HQ := mul_self_le_mul_self HN HS
  refine ⟨ℓ, ?_⟩
  nlinarith only [HL, HQ]

universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem mixed_constrainedPhi_local_left_of_near_minimum
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h ε : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s'))
    (hnear : mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε)
    (hsmall : mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : mixedLocalLeftConstant ξ * (s.q r - u) ≤ 1 - t₀) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      2 * mixedInterpolationPsi ξ s h t - (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 := by
  have HS := mixedLeftSlope_ge_local_of_near_minimum ξ s h ε hr0 hr hm hleft hright
    ht ht₀ hu hmin hnear hsmall hlocal
  have H := mixed_constrainedPhi_le_two_Psi_sub_left_factor_sq hn ξ s h sk hr0 hr
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu
  change _ ≤ 2 * mixedInterpolationPsi ξ s h t - (mixedLeftSlope ξ s h r t u) ^ 2 / 2 at H
  have HN : 0 ≤ (1 - t₀) / 2 * (s.q r - u) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.2)
  have HQ := mul_self_le_mul_self HN HS
  nlinarith only [H, HQ]

end FourPapersCommon
