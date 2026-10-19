-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumRadialConcentration
public import SlowEquilibration.SphericalMaximumEnergySlopeBounds

/-! All printed conclusions of manuscript Lemma10.5 for the literal nonpure
mixed spherical model, with actual saddle, raw determinant normalization,
radial probability law and physical energy derivative, including finite N. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity
open scoped Topology ContDiff ENNReal

structure SourceMarkedRadialConclusions (μ : FiniteMixture) (β x Q L R δ : ℝ) : Prop where
  saddle_smooth : ContDiffOn ℝ ∞ (sourceRadialSaddle μ Q) (Icc (markE μ β x Q-δ) (markE μ β x Q+δ))
  optimized_smooth : ContDiffOn ℝ ∞ (sourceSaddleComplexity μ Q) (Icc (markE μ β x Q-δ) (markE μ β x Q+δ))
  contact_zero : sourceSaddleComplexity μ Q (markE μ β x Q)=0
  contact_derivative : HasDerivAt (sourceSaddleComplexity μ Q) (-(β*x)) (markE μ β x Q)
  quadratic_remainder : ∀ e : ℝ,|sourceSaddleComplexity μ Q e+β*x*(e-markE μ β x Q)| ≤
    sourceEnergyCurvature μ Q/2*(e-markE μ β x Q)^2
  physical_normalization : ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
    c*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)/Real.sqrt (n+2 : ℕ) ≤
      sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*e) ∧
    sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*e) ≤
      C*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)/Real.sqrt (n+2 : ℕ)
  raw_exact : ∀ n : ℕ,∀ e : ℝ,sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*e)=
    sourcePhysicalRadialFactor n μ Q*sourceRawRadialNormalization n μ Q (Ioo L R) e
  raw_normalization : ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
    c*Real.exp ((n+2 : ℕ)*(sourceSaddleComplexity μ Q e-1/2+Real.log (Q*μ.xi1 Q)/2))/Real.sqrt (n+2 : ℕ) ≤
      sourceRawRadialNormalization n μ Q (Ioo L R) e ∧
    sourceRawRadialNormalization n μ Q (Ioo L R) e ≤
      C*Real.exp ((n+2 : ℕ)*(sourceSaddleComplexity μ Q e-1/2+Real.log (Q*μ.xi1 Q)/2))/Real.sqrt (n+2 : ℕ)
  radial_probability : ∀ n : ℕ,∀ e : ℝ,IsProbabilityMeasure (sourceMaximumRadialLaw n μ Q (Ioo L R) e)
  radial_concentration : ∃ C c : ℝ,0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ t : ℝ,0 ≤ t →
    (sourceMaximumRadialLaw n μ Q (Ioo L R) e).real {k : ℝ | t ≤ |k-sourceRadialSaddle μ Q e|} ≤
      C*Real.exp (-c*(n+2 : ℕ)*t^2)
  exact_energy_slope : ∀ n : ℕ,∀ H : ℝ,
    HasDerivAt (fun v => Real.log (sourceMaximumEnergyDensity n μ Q (Ioo L R) v))
      (-(∫ k,sourceEnergySlope μ Q (H/(n+2 : ℕ)) k
        ∂sourceMaximumRadialLaw n μ Q (Ioo L R) (H/(n+2 : ℕ)))) H
  energy_lower : ∀ n : ℕ,∀ H : ℝ,(n+2 : ℕ)*(markE μ β x Q-δ) ≤ H →
    β*x/2 ≤ -sourceMaximumEnergyLogSlope n μ Q (Ioo L R) H
  energy_upper : ∀ n : ℕ,∀ H : ℝ,|H-(n+2 : ℕ)*markE μ β x Q| ≤ (n+2 : ℕ)*δ →
    -sourceMaximumEnergyLogSlope n μ Q (Ioo L R) H ≤ (β*x+β)/2
  micro_slope : ∀ D : ℝ,0 ≤ D → ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ H : ℝ,
    |H-(n+2 : ℕ)*markE μ β x Q| ≤ D*Real.log (n+2 : ℕ) →
    |sourceMaximumEnergyLogSlope n μ Q (Ioo L R) H+β*x| ≤ C/Real.sqrt (n+2 : ℕ)

/-- Full manuscript Lemma10.5. The raw source hypotheses supply the actual
model geometry; all probability, normalization, smoothness and slope facts
are proved from the original finite Gaussian field and Hessian law. -/
theorem sourceMarked_radial_all_conclusions (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hScore : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k ∈ Icc L R,
      β*x/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2)
    (hA4 : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      sourceRadialClearance μ β Q (Ioo L R)/2 ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ) :
    SourceMarkedRadialConclusions μ β x Q L R δ := by
  refine ⟨sourceRadialSaddle_contDiffOn_band μ h hnp hL hm hA4,
    sourceSaddleComplexity_contDiffOn_band μ h hnp hL hm hA4,
    sourceSaddleComplexity_at_contact μ h hnp,sourceSaddleComplexity_contact_hasDerivAt μ h hnp,
    sourceSaddleComplexity_contact_taylor μ h hnp,
    sourceSaddle_radial_normalization μ h hnp hL hm hA4,
    fun n e => sourceMaximumEnergyDensity_eq_raw n μ h.overlap_range.1 hnp (Ioo L R) e,
    sourceRawRadialNormalization_band_bounds μ h hnp hL hm hA4,
    fun n e => sourceMaximumRadialLaw_probability_all_dimensions n μ h hnp hL hm e,
    sourceMaximumRadialLaw_gaussian_concentration μ h hnp hL hm hA4,
    fun n H => sourceMaximumEnergyLogDensity_hasDerivAt_all_dimensions n μ h hnp hL hm H,
    fun n _ hH => sourceMaximumEnergyLogSlope_lower_all_dimensions n μ h hnp hL hm hδ.le hScore hH,
    ?_,fun _ hD => sourceMaximumEnergyLogSlope_log_window μ h hnp hL hm hD⟩
  intro n H hH
  apply sourceMaximumEnergyLogSlope_upper_all_dimensions n μ h hnp hL hm hScore
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hAbs := abs_le.mp hH
  constructor
  · apply (le_div_iff₀ hN).mpr
    nlinarith [hAbs.1]
  · apply (div_le_iff₀ hN).mpr
    nlinarith [hAbs.2]
end SlowEquilibration.SphericalMarkedWindows
