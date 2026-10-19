module
public import FourPapersCommon.MixedSecondInterpolationBounds
public import FourPapersCommon.MixedSecondCorrection
public import FourPapersCommon.MixedQuantitativeOptimality
public import Targets.TalagrandRightZero

@[expose] public section

/-! Actual constrained-pressure gains for the mixed covariance. The Gaussian
recursion is clocked, while every overlap constraint and theta correction stays
in physical coordinates. These are genuine finite-model estimates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

private theorem mixed_overlap_attainable {n : ℕ} {u : ℝ}
    [Nonempty (AT.ConstrainedPair n u)] : ∃ σ τ : Config n, overlap n σ τ = u := by
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  exact ⟨p.1.1, p.1.2, p.2⟩

theorem mixed_constrainedPhi_le_two_Psi_sub_left_factor_sq
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      2 * mixedInterpolationPsi ξ s h t -
        (section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1))
          (mixedLeftSplitVariance ξ s r t u) - u) ^ 2 / 2 := by
  have hm0 := s.m_nonneg (p := r - 1) (by omega)
  have hm : s.m (r - 1) ∈ Icc (s.m (r - 1) / 2) (s.m r) :=
    ⟨by linarith, s.m_mono' r hr (r - 1) (by omega)⟩
  have H := mixedLeftInterpolation_endpoint_bound hn ξ s h sk hr0 hr hm ht hu
  rw [mixedLeftPairCorrection_eq ξ s u (s.m (r - 1)) hr0 hr] at H
  simp only [sub_self, zero_mul, add_zero] at H
  have H0 := mixedLeftInterpolation_zero_lambda_gain hn ξ s h sk.U hr0 hr ht hu
    mixed_overlap_attainable
  unfold mixedInterpolationPsi
  linarith

theorem mixed_constrainedPhi_le_two_Psi_sub_right_factor_sq
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      2 * mixedInterpolationPsi ξ s h t -
        (deriv (section5RightV (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m r)
          (mixedRightSplitVariance ξ s r t u)) 0 - u) ^ 2 / 2 := by
  have hm0 := s.m_nonneg (p := r) hr
  have hm : s.m r ∈ Icc (s.m (r - 1)) (2 * s.m r) :=
    ⟨s.m_mono' r hr (r - 1) (by omega), by linarith⟩
  have H := mixedRightInterpolation_endpoint_bound hn ξ s h sk hr0 hr hm ht hu
  rw [mixedRightPairCorrection_eq ξ s u (s.m r) hr] at H
  simp only [sub_self, zero_mul, add_zero] at H
  have hv := mixedRightSplitVariance_mem ξ s hr ht hu
  obtain ⟨ℓ, hℓ⟩ := section5RightV_lambda_gain (mixedClockScheme ξ s) (mixedBeta ξ) h hr
    (m := s.m r) ⟨hm0, (s.m_le_one hr).trans (by norm_num)⟩
    (mixedRightSplitVariance ξ s r t u) u
  have hbase := section5RightV_zero_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr hv
  simp only [mixedClockScheme_m] at hbase
  rw [hbase] at hℓ
  have H0 := mixedRightInterpolation_zero_le hn ξ s h sk.U hr hm0 ht hu
    mixed_overlap_attainable ℓ
  unfold mixedInterpolationPsi
  linarith

theorem mixed_constrainedPhi_le_two_Psi_mass_taylor
    {n k : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {m t u : ℝ} (hm : m ∈ Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      2 * mixedInterpolationPsi ξ s h t +
        (section4U (mixedClockScheme ξ s) (mixedBeta ξ) h r (mixedLeftSplitVariance ξ s r t u) -
          t * (ξ.correction (s.q r) - ξ.correction u)) * (m - s.m (r - 1)) +
        2 * section4MassSecondBound ((mixedBeta ξ) ^ 2) * (m - s.m (r - 1)) ^ 2 := by
  have ha : s.m (r - 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hm0 : 0 ≤ m := by linarith [ha.1, hm.1]
  have hb : m ∈ Icc (0 : ℝ) 1 := ⟨hm0, hm.2.trans (s.m_le_one hr)⟩
  have hv := mixedLeftSplitVariance_mem ξ s hr ht hu
  have H := mixedLeftInterpolation_endpoint_bound hn ξ s h sk hr0 hr hm ht hu
  rw [mixedLeftPairCorrection_eq ξ s u m hr0 hr] at H
  have H0 := mixedLeftInterpolation_zero_le hn ξ s h sk.U hr hm0 ht hu
    mixed_overlap_attainable 0
  rw [section5V_zero_eq_two_section4T (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hm0 hv] at H0
  simp only [zero_mul, sub_zero] at H0
  have HT := (abs_le.mp (section4T_mass_taylor_bound (mixedClockScheme ξ s) (mixedBeta ξ) h hr ha hb hv)).2
  have hd := (hasDerivAt_section4T_mass_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv).deriv
  have hbase := section4T_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hv
  simp only [mixedClockScheme_m] at hd hbase HT
  rw [hd, hbase] at HT
  unfold mixedInterpolationPsi
  nlinarith only [H, H0, HT]

end FourPapersCommon
