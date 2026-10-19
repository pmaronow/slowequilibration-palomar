module
public import FourPapersCommon.MixedEndpointOptimality
public import FourPapersCommon.MixtureJetBounds
public import Targets.Section4HessianUniform

@[expose] public section

/-! Genuine inward differentiation of the physical mixed first variation.
All normalized factors are the actual scalar Gaussian recursion observables. -/
noncomputable section
open Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 800000

def mixedSection4Q (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  section4TVarianceQ (mixedClockScheme ξ s) (mixedBeta ξ) h r (s.m (r - 1))
    (mixedLeftSplitVariance ξ s r 1 u)

def mixedSection4R (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  section4THessianSquare (mixedClockScheme ξ s) (mixedBeta ξ) h r
    (mixedLeftSplitVariance ξ s r 1 u)

def mixedSection4FirstVariationD (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (u : ℝ) : ℝ := ξ.second u / 2 * (u - mixedSection4Q ξ s h r u)

def mixedSection4FirstVariationD2 (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  deriv ξ.second u / 2 * (u - mixedSection4Q ξ s h r u) +
    ξ.second u / 2 * (1 - ξ.second u * mixedSection4R ξ s h r u)

theorem hasDerivAt_mixedLeftSplitVariance (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (mixedLeftSplitVariance ξ s r 1) (-ξ.second u) u := by
  change HasDerivAt (fun z => 1 * (ξ.first (s.q r) - ξ.first z)) (-ξ.second u) u
  simpa only [one_mul] using (ξ.hasDerivAt_first_unit ⟨by linarith [hu.1], hu.2⟩).const_sub (ξ.first (s.q r))

theorem mixedSection4Q_mem (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) {r : ℕ} (hr : r ≤ k + 1) (u : ℝ) : mixedSection4Q ξ s h r u ∈ Icc (0 : ℝ) 1 :=
  section4TVarianceQ_mem_Icc (mixedClockScheme ξ s) (mixedBeta ξ) h r
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ _

theorem mixedSection4R_mem (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) {r : ℕ} (hr : r ≤ k + 1) (u : ℝ) : mixedSection4R ξ s h r u ∈ Icc (0 : ℝ) 1 :=
  section4THessianSquare_mem_Icc (mixedClockScheme ξ s) (mixedBeta ξ) h hr _

theorem hasDerivWithinAt_mixedSection4Q (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {u : ℝ} (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (mixedSection4Q ξ s h r) (ξ.second u * mixedSection4R ξ s h r u)
      (Icc (s.q (r - 1)) (s.q r)) u := by
  have hmap : MapsTo (mixedLeftSplitVariance ξ s r 1)
      (Icc (s.q (r - 1)) (s.q r))
      (Icc (0 : ℝ) ((mixedBeta ξ) ^ 2 *
        ((mixedClockScheme ξ s).q r - (mixedClockScheme ξ s).q (r - 1)))) :=
    fun z hz => mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hz
  have hu0 : u ∈ Icc (0 : ℝ) 1 :=
    ⟨(s.q_nonneg (by omega)).trans hu.1, hu.2.trans (s.q_le_one (by omega))⟩
  have H := (hasDerivWithinAt_section4TVarianceQ_baseline (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr (hmap hu)).comp u
    (hasDerivAt_mixedLeftSplitVariance ξ s r hu0).hasDerivWithinAt hmap
  convert! H using 1
  simp only [mixedSection4R]
  ring

theorem hasDerivWithinAt_mixedSection4FirstVariation (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < 1) {u : ℝ} (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (mixedSection4FirstVariation ξ s h r)
      (mixedSection4FirstVariationD ξ s h r u) (Icc (s.q (r - 1)) (s.q r)) u := by
  have hmap : MapsTo (mixedLeftSplitVariance ξ s r 1)
      (Icc (s.q (r - 1)) (s.q r))
      (Icc (0 : ℝ) ((mixedBeta ξ) ^ 2 *
        ((mixedClockScheme ξ s).q r - (mixedClockScheme ξ s).q (r - 1)))) :=
    fun z hz => mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hz
  have hu0 : u ∈ Icc (0 : ℝ) 1 :=
    ⟨(s.q_nonneg (by omega)).trans hu.1, hu.2.trans (s.q_le_one (by omega))⟩
  have H := (hasDerivWithinAt_section4U (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr hm (hmap hu)).comp u
    (hasDerivAt_mixedLeftSplitVariance ξ s r hu0).hasDerivWithinAt hmap
  have HC := (ξ.hasDerivAt_correction (by rw [abs_of_nonneg hu0.1]; linarith [hu0.2])).const_sub (ξ.correction (s.q r))
  convert! (H.div_const 2).sub (HC.div_const 2).hasDerivWithinAt using 1
  simp only [mixedSection4FirstVariationD, mixedSection4Q, mixedClockScheme_m]
  ring

theorem hasDerivWithinAt_mixedSection4FirstVariationD (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {u : ℝ} (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (mixedSection4FirstVariationD ξ s h r)
      (mixedSection4FirstVariationD2 ξ s h r u) (Icc (s.q (r - 1)) (s.q r)) u := by
  have hu0 : u ∈ Icc (0 : ℝ) 1 :=
    ⟨(s.q_nonneg (by omega)).trans hu.1, hu.2.trans (s.q_le_one (by omega))⟩
  have H := ((ξ.hasDerivAt_second_unit hu0).div_const 2).hasDerivWithinAt.mul
    ((hasDerivAt_id u).hasDerivWithinAt.sub (hasDerivWithinAt_mixedSection4Q ξ s h hr0 hr hu))
  exact H

theorem mixedSection4FirstVariation_upper (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    mixedSection4FirstVariation ξ s h r (s.q r) = 0 := by
  simp [mixedSection4FirstVariation, mixedLeftSplitVariance,
    section4U_zero_variance (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr]

theorem mixedSection4Q_lipschitz (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {u w : ℝ} (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Icc (s.q (r - 1)) (s.q r)) :
    |mixedSection4Q ξ s h r u - mixedSection4Q ξ s h r w| ≤ ξ.jetBound * |u - w| := by
  have H := (convex_Icc (s.q (r - 1)) (s.q r)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => hasDerivWithinAt_mixedSection4Q ξ s h hr0 hr hz)
    (fun z hz => by
      have hz0 : z ∈ Icc (0 : ℝ) 1 := ⟨(s.q_nonneg (by omega)).trans hz.1, hz.2.trans (s.q_le_one (by omega))⟩
      have hR := mixedSection4R_mem ξ s h hr z
      have hS := ξ.abs_second_le_at_one (abs_le.mpr ⟨by linarith [hz0.1], hz0.2⟩)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ξ.second_nonneg z), abs_of_nonneg hR.1]
      have hS' : ξ.second z ≤ ξ.jetBound := (le_abs_self _).trans (hS.trans ξ.jetBound_spec.2.1)
      exact (mul_le_of_le_one_right (ξ.second_nonneg z) hR.2).trans hS') hw hu
  simpa only [Real.norm_eq_abs] using H

theorem mixedSection4R_lipschitz (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {u w : ℝ} (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Icc (s.q (r - 1)) (s.q r)) :
    |mixedSection4R ξ s h r u - mixedSection4R ξ s h r w| ≤ 535 * ξ.jetBound * |u - w| := by
  have H := section4THessianSquare_lipschitz_uniform (mixedClockScheme ξ s) (mixedBeta ξ) h hr0 hr
    (mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hu)
    (mixedLeftSplitVariance_mem ξ s hr (t := 1) (by norm_num) hw)
  have hu0 : u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [s.q_nonneg (p := r - 1) (by omega), hu.1], hu.2.trans (s.q_le_one (by omega))⟩
  have hw0 : w ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [s.q_nonneg (p := r - 1) (by omega), hw.1], hw.2.trans (s.q_le_one (by omega))⟩
  have HF := (ξ.first_lipschitz_unit hu0 hw0).trans
    (mul_le_mul_of_nonneg_right ξ.jetBound_spec.2.1 (abs_nonneg _))
  have he : |mixedLeftSplitVariance ξ s r 1 u - mixedLeftSplitVariance ξ s r 1 w| = |ξ.first u - ξ.first w| := by
    simp only [mixedLeftSplitVariance, one_mul]
    rw [show ξ.first (s.q r) - ξ.first u - (ξ.first (s.q r) - ξ.first w) = -(ξ.first u - ξ.first w) by ring, abs_neg]
  rw [he] at H
  exact H.trans (by nlinarith only [HF])

end FourPapersCommon
