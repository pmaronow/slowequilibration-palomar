-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalPhysicalWindowBridge
public import SlowEquilibration.SourcePureLocalMaxCenterCountLimits
public import SlowEquilibration.SphericalMaximumAllDimensionRegularity

/-! Uniform transfer from negative-Hessian local-max window means to the
literal all-critical window means on the proper-pure exterior mark band. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open GOEMaximumDeterminant
open scoped ENNReal Topology
set_option maxHeartbeats 500000

theorem pureLocalMaxPhysicalIntensity_le_critical_all_dimensions
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q H : ℝ) :
    pureLocalMaxPhysicalIntensity n p hp a ha Q H ≤
      pureCriticalPhysicalIntensity n p hp a ha Q H := by
  unfold pureLocalMaxPhysicalIntensity pureCriticalPhysicalIntensity
    pureNegativeIntensity pureCriticalIntensity
  dsimp only
  gcongr
  exact sourceMaximumMean_le_physicalMean n (n+2)
    (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)
    ((p : ℝ)*(H/(n+2 : ℕ)))

theorem sourcePure_criticalWindowMean_relative_comparison
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ L R : ℝ,
        sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r L R ≤
          sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r L R ∧
        sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r L R ≤
          (1+C*Real.exp (-c*(n+2 : ℕ)))*
            sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r L R := by
  obtain ⟨C,c,hC,hc,hComp⟩ :=
    sourcePure_critical_localMax_physical_comparison p hp a ha h.overlap_range.1
      hg hLeft hRight
  refine ⟨C,c,hC,hc,?_⟩
  have hInt := pureTruncatedLocalMaxDensity_integrable_eventually
    p hp a ha h (hm.1.trans hm.2) hg hLeft hRight
  filter_upwards [hComp,hInt] with n hn hmax
  let d : ℝ := 1+C*Real.exp (-c*(n+2 : ℕ))
  let fmax : ℝ → ℝ := pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  let fcrit : ℝ → ℝ := sourcePureTruncatedCriticalDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hpoint : ∀ H, 0 ≤ fmax H ∧ fmax H ≤ fcrit H ∧ fcrit H ≤ d*fmax H := by
    intro H
    by_cases hH : H ∈ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
    · simp only [fmax, fcrit, pureTruncatedLocalMaxDensity,
        sourcePureTruncatedCriticalDensity, indicator_of_mem hH]
      have hlo := pureLocalMaxPhysicalIntensity_le_critical_all_dimensions
        n p hp a ha Q H
      exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono
        (pureCriticalPhysicalIntensity_ne_top n p hp a ha Q H) hlo, hn H hH⟩
    · simp only [fmax, fcrit, pureTruncatedLocalMaxDensity,
        sourcePureTruncatedCriticalDensity, indicator_of_notMem hH]
      exact ⟨by simp, by simp, by simp⟩
  have hmeas : Measurable fcrit := by
    exact ((pureCriticalPhysicalIntensity_measurable n p hp a ha Q).ennreal_toReal).indicator
      measurableSet_Ioo
  have hcInt : Integrable fcrit := by
    apply (hmax.const_mul d).mono' hmeas.aestronglyMeasurable
    exact ae_of_all _ (fun H => by
      rw [Real.norm_of_nonneg ((hpoint H).1.trans (hpoint H).2.1)]
      exact (hpoint H).2.2)
  intro L R
  rw [sourcePureTruncatedLocalMaxWindowMean_eq_integral n p hp a ha
        h.overlap_range.1,
      sourcePureTruncatedCriticalWindowMean_eq_integral n p hp a ha
        h.overlap_range.1]
  constructor
  · apply integral_mono_ae hmax.integrableOn hcInt.integrableOn
    exact ae_of_all _ (fun H => (hpoint H).2.1)
  · calc
      (∫ H in Icc L R, fcrit H) ≤ ∫ H in Icc L R, d*fmax H := by
        apply integral_mono_ae hcInt.integrableOn (hmax.const_mul d).integrableOn
        exact ae_of_all _ (fun H => (hpoint H).2.2)
      _ = d*(∫ H in Icc L R, fmax H) := integral_const_mul d fmax

end SlowEquilibration.SphericalMarkedWindows
