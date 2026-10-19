-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumAllDimensionRegularity
public import SlowEquilibration.GaussianRadialTiltDifferential
public import SlowEquilibration.NormalizedRadialLaplace

/-! The literal energy derivative and radial probability law of local maxima,
for every dimension and every physical energy. No finite-prefix regularity or
normalization is assumed. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity
open GaussianRadialEnergyTilt
open scoped Topology ENNReal
set_option maxHeartbeats 400000

def sourceMaximumRadialLaw (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) (e : ℝ) : Measure ℝ :=
  NormalizedRadialMeasure.law (sourceRawRadialWeight n μ Q e) U

theorem sourceMaximumRadialLaw_eq_physical (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (U : Set ℝ) (e : ℝ) :
    sourceMaximumRadialLaw n μ Q U e=NormalizedRadialMeasure.law (sourceEnergyRadialDensity n μ Q e) U := by
  have he : sourceEnergyRadialDensity n μ Q e=
      fun k => sourcePhysicalRadialFactor n μ Q*sourceRawRadialWeight n μ Q e k :=
    funext (sourceEnergyRadialDensity_eq_raw n μ hQ hnp e)
  rw [he,NormalizedRadialMeasure.law_const_mul (sourcePhysicalRadialFactor_pos n μ hQ hnp).ne']
  rfl

theorem sourceMaximumRadialLaw_probability_all_dimensions (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (e : ℝ) :
    IsProbabilityMeasure (sourceMaximumRadialLaw n μ Q (Ioo L R) e) := by
  rw [sourceMaximumRadialLaw_eq_physical n μ h.overlap_range.1 hnp]
  exact NormalizedRadialMeasure.law_probability
    (sourceMaximumRadialDensity_integrable_all_dimensions n μ h hnp hL hm ((n+2 : ℕ)*e))
    (fun _ => ENNReal.toReal_nonneg)
    (sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm ((n+2 : ℕ)*e))

theorem sourceMaximumRadialLaw_expectation (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (e : ℝ) (g : ℝ → ℝ) :
    (∫ k,g k ∂sourceMaximumRadialLaw n μ Q (Ioo L R) e)=
      (∫ k in Ioo L R,g k*sourceEnergyRadialDensity n μ Q e k)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*e) := by
  rw [sourceMaximumRadialLaw_eq_physical n μ h.overlap_range.1 hnp]
  exact NormalizedRadialMeasure.law_integral (sourceEnergyRadialDensity_measurable n μ Q e)
    (fun _ => ENNReal.toReal_nonneg)
    (sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm ((n+2 : ℕ)*e)) g

theorem sourceEnergySlope_physical_affine (n : ℕ) (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) (H k : ℝ) :
    sourceEnergySlope μ Q (H/(n+2 : ℕ)) k=
      energyScore (n+2 : ℕ) (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q)
        (β*x) (markK μ β Q) (H-(n+2 : ℕ)*markE μ β x Q) k := by
  have he := sourceEnergySlope_baseline_affine μ h hnp k
  unfold sourceEnergySlope sourceEnergyRadialCross at he
  unfold sourceEnergySlope energyScore sourceEnergyRadialCross
  field_simp
  nlinarith

/-- Actual physical score integrability and the exact derivative of the
original Kac--Rice radial integral, at every physical energy in every N. -/
theorem sourceMaximumEnergyDensity_hasDerivAt_all_dimensions (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (H : ℝ) :
    IntegrableOn (fun k => sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*
      (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal) (Ioo L R) ∧
    HasDerivAt (sourceMaximumEnergyDensity n μ Q (Ioo L R))
      (-(∫ k in Ioo L R,sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*
        (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal)) H := by
  let m := markK μ β Q
  let M := max (m-L) (R-m)
  have hM : 0 ≤ M := (sub_pos.mpr hm.1).le.trans (le_max_left _ _)
  have hRadius : ∀ k ∈ Ioo L R,|k-m| ≤ M := by
    intro k hk
    have hl := le_max_left (m-L) (R-m)
    have hr := le_max_right (m-L) (R-m)
    exact abs_le.mpr (by constructor <;> linarith [hk.1,hk.2])
  let center := (n+2 : ℕ)*markE μ β x Q
  have hd := energyDensity_hasDerivAt (B := sourceEnergyRadialCross μ Q) (c₀ := β*x) measurableSet_Ioo
    (sourceBaselineDensity_integrable_all_dimensions n μ h hnp hL hm)
    (fun _ _ => ENNReal.toReal_nonneg) (sourceEnergyCurvature_pos μ h.overlap_range.1 hnp).le
    (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hM hRadius (H-center)
  have hEq (k : ℝ) : -energyScore (n+2 : ℕ) (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q)
      (β*x) m (H-center) k*tiltedDensity (sourceBaselineDensity n μ β x Q) (n+2 : ℕ)
      (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) m (H-center) k=
      -(sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*(mixedLocalMaxPhysicalIntensity n μ Q H k).toReal) := by
    have hTilt := physicalMaximumDensity_eq_tilt n μ h hnp (H-center) k
    rw [show (n+2 : ℕ)*markE μ β x Q+(H-center)=H by dsimp [center];ring] at hTilt
    rw [←hTilt,←sourceEnergySlope_physical_affine n μ h hnp]
    ring
  have hI : IntegrableOn (fun k => -(sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*
      (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal)) (Ioo L R) :=
    hd.1.congr (ae_of_all _ hEq)
  refine ⟨hI.neg.congr (ae_of_all _ (fun _ => neg_neg _)),?_⟩
  have hComp := hd.2.comp H ((hasDerivAt_id H).sub_const center)
  simp only [mul_one] at hComp
  have hFunction : (fun v : ℝ => energyDensity (sourceBaselineDensity n μ β x Q) (Ioo L R) (n+2 : ℕ)
      (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) m (v-center))=
      sourceMaximumEnergyDensity n μ Q (Ioo L R) := by
    funext v
    have ht := sourceMaximumEnergyDensity_eq_tilt_integral n μ h hnp (Ioo L R) (v-center)
    rw [show (n+2 : ℕ)*markE μ β x Q+(v-center)=v by dsimp [center];ring] at ht
    exact ht.symm
  change HasDerivAt (fun v : ℝ => energyDensity (sourceBaselineDensity n μ β x Q) (Ioo L R) (n+2 : ℕ)
    (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) m (v-center)) _ H at hComp
  rw [hFunction,integral_congr_ae (ae_of_all _ hEq),integral_neg] at hComp
  exact hComp

/-- Source10.5(e), literally for all physical energies and all dimensions. -/
theorem sourceMaximumEnergyLogDensity_hasDerivAt_all_dimensions (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (H : ℝ) :
    HasDerivAt (fun v => Real.log (sourceMaximumEnergyDensity n μ Q (Ioo L R) v))
      (-(∫ k,sourceEnergySlope μ Q (H/(n+2 : ℕ)) k
        ∂sourceMaximumRadialLaw n μ Q (Ioo L R) (H/(n+2 : ℕ)))) H := by
  have hPos := sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm H
  have hd := (sourceMaximumEnergyDensity_hasDerivAt_all_dimensions n μ h hnp hL hm H).2.log hPos.ne'
  rw [sourceMaximumRadialLaw_expectation n μ h hnp hL hm]
  simp only [sourceEnergyRadialDensity,mul_div_cancel₀ _ (by positivity : ((n+2 : ℕ) : ℝ) ≠ 0),neg_div] at hd ⊢
  exact hd
end SlowEquilibration.SphericalMarkedWindows
