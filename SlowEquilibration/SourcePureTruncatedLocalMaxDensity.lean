-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCompactTailCenterNoContinuity
public import SlowEquilibration.SourcePureLocalMaxIntensityTransfer
public import SlowEquilibration.SourcePureOnePointContactEnvelope

/-! The actual pure local-maximum energy density restricted to an open source
mark interval. The cutoff may jump at its two endpoints. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory GOEMaximumDeterminant SphericalSequentialRegression
open TwoAtomStationarity SphericalTAPCertificate Filter
open scoped ENNReal
set_option maxHeartbeats 400000

def pureTruncatedLocalMaxDensity (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) (Q l r H : ℝ) : ℝ :=
  (Ioo l r).indicator
    (fun H => (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal) H

theorem pureLocalMaxPhysicalIntensity_measurable (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) (Q : ℝ) :
    Measurable (pureLocalMaxPhysicalIntensity n p hp a ha Q) := by
  let μ := FiniteMixture.pure p hp a ha
  have hmean : Measurable (fun H : ℝ =>
      maximumMean n (n+2) (Q^2*μ.xi2 Q) ((p : ℝ)*(H/(n+2 : ℕ)))) :=
    (maximumMean_measurable n (n+2) (Q^2*μ.xi2 Q)).comp
      (measurable_const.mul (measurable_id.div_const _))
  have hpdf : Measurable (fun H : ℝ => physicalValuePdf (n+2) μ Q (H/(n+2 : ℕ))) :=
    (physicalValuePdf_measurable (n+2) μ Q).comp (measurable_id.div_const _)
  exact measurable_const.mul ((measurable_const.mul hpdf).mul hmean.ennreal_ofReal)

theorem pureTruncatedLocalMaxDensity_measurable (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) (Q l r : ℝ) :
    Measurable (pureTruncatedLocalMaxDensity n p hp a ha Q l r) := by
  exact ((pureLocalMaxPhysicalIntensity_measurable n p hp a ha Q).ennreal_toReal).indicator
    measurableSet_Ioo

theorem pureTruncatedLocalMaxDensity_nonneg (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) (Q l r H : ℝ) :
    0 ≤ pureTruncatedLocalMaxDensity n p hp a ha Q l r H := by
  by_cases hH : H ∈ Ioo l r
  · simp [pureTruncatedLocalMaxDensity, hH]
  · simp [pureTruncatedLocalMaxDensity, hH]

theorem pureTruncatedLocalMaxDensity_integrable_of_bound (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) (Q l r C : ℝ)
    (hC : ∀ H ∈ Ioo l r,
      (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal ≤ C) :
    Integrable (pureTruncatedLocalMaxDensity n p hp a ha Q l r) := by
  let g := fun H : ℝ => (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal
  have hmeas : Measurable g :=
    (pureLocalMaxPhysicalIntensity_measurable n p hp a ha Q).ennreal_toReal
  have hvol : volume (Ioo l r) < ∞ := by simp [Real.volume_Ioo]
  have hbound : ∀ᵐ H ∂(volume.restrict (Ioo l r)), ‖g H‖ ≤ C :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun H hH => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by exact ENNReal.toReal_nonneg)]
      exact hC H hH)
  have hi : IntegrableOn g (Ioo l r) volume :=
    IntegrableOn.of_bound hvol hmeas.aestronglyMeasurable C hbound
  exact hi.integrable_indicator measurableSet_Ioo

/-- On any compact positive-exterior mark interval, the actual truncated
local-maximum intensity is integrable for all sufficiently large dimensions.
The bound comes from the literal Kac--Rice prefactor and the source contact
tangent, not from an assumed regularity of the intensity. -/
theorem pureTruncatedLocalMaxDensity_integrable_eventually
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ} (_hlr : l < r) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    ∀ᶠ n : ℕ in atTop, Integrable
      (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  obtain ⟨c,C,hc,hC,hPref⟩ := pure_localMax_physical_prefactors
    p hp a ha h.overlap_range.1 (Z := Z) hg
  filter_upwards [hPref] with n hn
  let N : ℝ := (n+2 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  let B : ℝ := C * (Real.sqrt N)⁻¹ * Real.exp (N*(β*x)*(E-l))
  apply pureTruncatedLocalMaxDensity_integrable_of_bound n p hp a ha Q
    (N*l) (N*r) B
  intro H hH
  let e := H/N
  have he : e ∈ Ioo l r := by
    dsimp [e] at *
    constructor
    · apply (lt_div_iff₀ hN).mpr
      nlinarith [hH.1]
    · apply (div_lt_iff₀ hN).mpr
      nlinarith [hH.2]
  have heMark : (p : ℝ)*e ∈ Icc
      (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z := by
    constructor
    · have hm := mul_le_mul_of_nonneg_left he.1.le hp0.le
      dsimp [μ] at *
      linarith
    · have hm := mul_le_mul_of_nonneg_left he.2.le hp0.le
      linarith
  have hH : H = N*e := by dsimp [e]; field_simp
  have hPrefUpper := (hn e heMark).2.1.trans (hn e heMark).2.2
  rw [← hH] at hPrefUpper
  have hUpper : (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal ≤
      C*(Real.sqrt N)⁻¹*Real.exp (N*pureMarkedComplexity p hp a ha Q e) := by
    have hh := ENNReal.toReal_mono (by simp) hPrefUpper
    change _ ≤ (ENNReal.ofReal
      (C*(Real.sqrt N)⁻¹*Real.exp (N*pureMarkedComplexity p hp a ha Q e))).toReal at hh
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    exact hh
  have hLoss := sourcePureMarkedComplexity_global_linear_loss p hp a ha h e
  have hExponent : N*pureMarkedComplexity p hp a ha Q e ≤ N*(β*x)*(E-l) := by
    have hs := mul_le_mul_of_nonneg_left hLoss hN.le
    have ht := mul_le_mul_of_nonneg_left he.1.le hc0.le
    dsimp [E, μ] at *
    nlinarith
  have hExp := Real.exp_le_exp.mpr hExponent
  have hMul := mul_le_mul_of_nonneg_left hExp
    (by positivity : 0 ≤ C*(Real.sqrt N)⁻¹)
  exact hUpper.trans (by simpa only [B] using hMul)

/-- The open interior of the exterior mark window has strictly positive
actual local-maximum density, uniformly for all sufficiently large N. -/
theorem pureTruncatedLocalMaxDensity_pos_eventually
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ} (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    ∀ᶠ n : ℕ in atTop, ∀ H ∈ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r),
      0 < pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) H := by
  let μ := FiniteMixture.pure p hp a ha
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  obtain ⟨c,C,hc,hC,hPref⟩ := pure_localMax_physical_prefactors
    p hp a ha h.overlap_range.1 (Z := Z) hg
  filter_upwards [hPref] with n hn
  intro H hH
  let N : ℝ := (n+2 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  let e := H/N
  have he : e ∈ Ioo l r := by
    dsimp [e] at *
    constructor
    · apply (lt_div_iff₀ hN).mpr
      nlinarith [hH.1]
    · apply (div_lt_iff₀ hN).mpr
      nlinarith [hH.2]
  have heMark : (p : ℝ)*e ∈ Icc
      (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z := by
    constructor
    · have hm := mul_le_mul_of_nonneg_left he.1.le hp0.le
      dsimp [μ] at *
      linarith
    · have hm := mul_le_mul_of_nonneg_left he.2.le hp0.le
      linarith
  have hHEq : H = N*e := by dsimp [e]; field_simp
  have hBounds := hn e heMark
  rw [← hHEq] at hBounds
  have hFinite : pureLocalMaxPhysicalIntensity n p hp a ha Q H < ∞ :=
    lt_of_le_of_lt (hBounds.2.1.trans hBounds.2.2) (by simp)
  have hPosReal : 0 < c*(Real.sqrt N)⁻¹ *
      Real.exp (N*pureMarkedComplexity p hp a ha Q e) := by
    apply mul_pos
    · exact mul_pos hc (inv_pos.mpr (Real.sqrt_pos.mpr hN))
    · exact Real.exp_pos _
  have hLowerReal := ENNReal.toReal_mono hFinite.ne hBounds.1
  change (ENNReal.ofReal (c*(Real.sqrt N)⁻¹ *
      Real.exp (N*pureMarkedComplexity p hp a ha Q e))).toReal ≤
        (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal at hLowerReal
  rw [ENNReal.toReal_ofReal hPosReal.le] at hLowerReal
  have hPositive : 0 < (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal :=
    hPosReal.trans_le hLowerReal
  change H ∈ Ioo (N*l) (N*r) at hH
  change 0 < pureTruncatedLocalMaxDensity n p hp a ha Q (N*l) (N*r) H
  simpa [pureTruncatedLocalMaxDensity, hH] using hPositive

end SlowEquilibration.SphericalMarkedWindows
