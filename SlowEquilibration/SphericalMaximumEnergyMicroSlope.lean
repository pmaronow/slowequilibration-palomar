-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumEnergyDifferential
public import SlowEquilibration.SphericalMaximumRadialMoment
public import SlowEquilibration.NormalizedRadialAffineScore

/-! The literal logarithmic derivative of the actual maximum energy density
has the manuscript's uniform N^{-1/2} error on every fixed logarithmic window. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity
open scoped Topology
set_option maxHeartbeats 400000

def sourceMaximumEnergyLogSlope (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) (H : ℝ) : ℝ :=
  deriv (fun v => Real.log (sourceMaximumEnergyDensity n μ Q U v)) H

theorem sourceMaximumEnergyLogSlope_eq_score (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (H : ℝ) :
    sourceMaximumEnergyLogSlope n μ Q (Ioo L R) H=
      -(∫ k in Ioo L R,sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*
        (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal)/
      sourceMaximumEnergyDensity n μ Q (Ioo L R) H :=
  ((sourceMaximumEnergyDensity_hasDerivAt_all_dimensions n μ h hnp hL hm H).2.log
    (sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm H).ne').deriv

theorem sourceMaximumEnergyLogSlope_contact_deviation (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (σ : ℝ) :
    |sourceMaximumEnergyLogSlope n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ)+β*x| ≤
      sourceEnergyCurvature μ Q*|σ|/(n+2 : ℕ)+|sourceEnergyRadialCross μ Q| *
        sourceMaximumRadialMoment n μ β Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ) := by
  let H := (n+2 : ℕ)*markE μ β x Q+σ
  let f := fun k => (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal
  let m := markK μ β Q
  let M := max (m-L) (R-m)
  have hf : IntegrableOn f (Ioo L R) := sourceMaximumRadialDensity_integrable_all_dimensions n μ h hnp hL hm H
  have hRadius (k : ℝ) (hk : k ∈ Ioo L R) : |k-m| ≤ M := by
    have hl := le_max_left (m-L) (R-m)
    have hr := le_max_right (m-L) (R-m)
    exact abs_le.mpr (by constructor <;> linarith [hk.1,hk.2])
  have hSigned : IntegrableOn (fun k => (k-m)*f k) (Ioo L R) := by
    apply (hf.const_mul M).mono'
    · exact (by fun_prop : Continuous (fun k : ℝ => k-m)).aestronglyMeasurable.mul hf.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0 ≤ f k from ENNReal.toReal_nonneg)]
      exact mul_le_mul_of_nonneg_right (hRadius k hk) ENNReal.toReal_nonneg
  have hZ : 0 < ∫ k in Ioo L R,f k := sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm H
  have hDev := NormalizedRadialMeasure.affine_score_expectation_deviation hf (fun _ => ENNReal.toReal_nonneg)
    hZ (a := sourceEnergyCurvature μ Q*σ/(n+2 : ℕ)) (B := sourceEnergyRadialCross μ Q) (c₀ := β*x) hSigned
  have hScore (k : ℝ) : sourceEnergySlope μ Q (H/(n+2 : ℕ)) k=
      β*x+sourceEnergyCurvature μ Q*σ/(n+2 : ℕ)+sourceEnergyRadialCross μ Q*(k-m) := by
    rw [sourceEnergySlope_physical_affine n μ h hnp]
    unfold GaussianRadialEnergyTilt.energyScore
    dsimp [H,m]
    ring
  rw [sourceMaximumEnergyLogSlope_eq_score n μ h hnp hL hm]
  have hInt : (∫ k in Ioo L R,sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*f k)=
      ∫ k in Ioo L R,(β*x+sourceEnergyCurvature μ Q*σ/(n+2 : ℕ)+
        sourceEnergyRadialCross μ Q*(k-m))*f k := by
    apply integral_congr_ae
    exact ae_of_all _ (fun k => congrArg (fun z => z*f k) (hScore k))
  change |-(∫ k in Ioo L R,sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*f k)/(∫ k in Ioo L R,f k)+β*x| ≤ _
  rw [hInt,show -(∫ k in Ioo L R,(β*x+sourceEnergyCurvature μ Q*σ/(n+2 : ℕ)+
    sourceEnergyRadialCross μ Q*(k-m))*f k)/(∫ k in Ioo L R,f k)+β*x=
      -((∫ k in Ioo L R,(β*x+sourceEnergyCurvature μ Q*σ/(n+2 : ℕ)+
        sourceEnergyRadialCross μ Q*(k-m))*f k)/(∫ k in Ioo L R,f k)-β*x) by ring,abs_neg]
  simpa only [abs_div,abs_mul,abs_of_pos (sourceEnergyCurvature_pos μ h.overlap_range.1 hnp),
    abs_of_pos (by positivity : 0 < ((n+2 : ℕ) : ℝ)),sourceMaximumRadialMoment,sourceMaximumEnergyDensity,f,H,m] using hDev

/-- Source10.5(e)'s uniform quantitative micro-slope, with the rate constant
fixed before dimension and every energy in the full physical log window. -/
theorem sourceMaximumEnergyLogSlope_log_window (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ H : ℝ,
      |H-(n+2 : ℕ)*markE μ β x Q| ≤ D*Real.log (n+2 : ℕ) →
      |sourceMaximumEnergyLogSlope n μ Q (Ioo L R) H+β*x| ≤ C/Real.sqrt (n+2 : ℕ) := by
  obtain ⟨K,hK,hMoment⟩ := sourceMaximumRadialMoment_log_window μ h hnp hL hm hD
  let A := sourceEnergyCurvature μ Q
  let B := sourceEnergyRadialCross μ Q
  have hA : 0 < A := sourceEnergyCurvature_pos μ h.overlap_range.1 hnp
  refine ⟨A+2*|B| *K,by positivity,?_⟩
  filter_upwards [hMoment,NatLogWindowScales.uniform_log_window_eventually hD (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1) 0] with n hn hSmall
  intro H hH
  let σ := H-(n+2 : ℕ)*markE μ β x Q
  have hσ : |σ| ≤ D*Real.log (n+2 : ℕ) := hH
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hS := Real.sqrt_pos.mpr hN
  have hSq : σ^2 ≤ (n+2 : ℕ) := by
    have hh := (div_le_iff₀ hN).mp (hSmall σ hσ).1
    simpa only [one_mul] using hh
  have hAbs : |σ| ≤ Real.sqrt (n+2 : ℕ) :=
    (sq_le_sq₀ (abs_nonneg _) hS.le).mp (by simpa only [sq_abs,Real.sq_sqrt hN.le] using hSq)
  have hRatio : |σ|/(n+2 : ℕ) ≤ 1/Real.sqrt (n+2 : ℕ) := by
    apply (div_le_iff₀ hN).mpr
    calc
      |σ| ≤ Real.sqrt (n+2 : ℕ) := hAbs
      _=1/Real.sqrt (n+2 : ℕ)*(n+2 : ℕ) := by field_simp;rw [Real.sq_sqrt hN.le]
  have hZ := sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm H
  have hShift : (n+2 : ℕ)*markE μ β x Q+σ=H := by dsimp [σ];ring
  have hMom := hn σ hσ
  rw [hShift] at hMom
  have hMRatio : sourceMaximumRadialMoment n μ β Q (Ioo L R) H/
      sourceMaximumEnergyDensity n μ Q (Ioo L R) H ≤ K*(1/Real.sqrt (n+2 : ℕ)+|σ|/(n+2 : ℕ)) :=
    (div_le_iff₀ hZ).mpr hMom
  have hDev := sourceMaximumEnergyLogSlope_contact_deviation n μ h hnp hL hm σ
  rw [hShift] at hDev
  apply hDev.trans
  change A*|σ|/(n+2 : ℕ)+|B| *sourceMaximumRadialMoment n μ β Q (Ioo L R) H/
    sourceMaximumEnergyDensity n μ Q (Ioo L R) H ≤ _
  have h1 := mul_le_mul_of_nonneg_left hRatio hA.le
  have h2 := mul_le_mul_of_nonneg_left hMRatio (abs_nonneg B)
  have h3 := mul_le_mul_of_nonneg_left hRatio (mul_nonneg (abs_nonneg B) hK.le)
  ring_nf at h1 h2 h3 ⊢
  linarith
end SlowEquilibration.SphericalMarkedWindows
