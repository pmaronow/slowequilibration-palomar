-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumRadialMoment
public import SlowEquilibration.GaussianRadialFixedEnergyLimits

/-! Genuine fixed-energy ratios in the actual original-field maximum
intensity, derived from the true normalized radial moment. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open GaussianRadialEnergyTilt
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximumEnergyDensity_fixed_ratio (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop,|σ n| ≤ D*Real.log (n+2 : ℕ)) (t : ℝ) :
    Tendsto (fun n : ℕ =>
      sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n+t)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  let M := max (markK μ β Q-L) (R-markK μ β Q)
  have hRadius : ∀ k∈Ioo L R,|k-markK μ β Q| ≤ M := by
    intro k hk
    have hl : markK μ β Q-L ≤ M := le_max_left _ _
    have hr : R-markK μ β Q ≤ M := le_max_right _ _
    apply abs_le.mpr
    constructor <;> linarith [hk.1,hk.2]
  have hDensity : ∀ n : ℕ,
      sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n)=
      energyDensity (sourceBaselineDensity n μ β x Q) (Ioo L R) (n+2 : ℕ)
        (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) (markK μ β Q) (σ n) :=
    fun n => sourceMaximumEnergyDensity_eq_tilt_integral n μ h hnp (Ioo L R) (σ n)
  have hPlus : ∀ n : ℕ,
      sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n+t)=
      energyDensity (sourceBaselineDensity n μ β x Q) (Ioo L R) (n+2 : ℕ)
        (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) (markK μ β Q) (σ n+t) := by
    intro n
    rw [add_assoc]
    exact sourceMaximumEnergyDensity_eq_tilt_integral n μ h hnp (Ioo L R) (σ n+t)
  have hRadial : ∀ n : ℕ,
      sourceMaximumRadialMoment n μ β Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n)=
      radialMoment (sourceBaselineDensity n μ β x Q) (Ioo L R) (n+2 : ℕ)
        (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) (markK μ β Q) (σ n) :=
    fun n => sourceMaximumRadialMoment_eq_tilt n μ h hnp (Ioo L R) (σ n)
  have hi : ∀ᶠ n : ℕ in atTop,IntegrableOn
      (tiltedDensity (sourceBaselineDensity n μ β x Q) (n+2 : ℕ) (sourceEnergyCurvature μ Q)
        (sourceEnergyRadialCross μ Q) (β*x) (markK μ β Q) (σ n)) (Ioo L R) := by
    filter_upwards [sourceMaximumRadialDensity_integrable μ h hnp hL hm] with n hn
    apply (hn ((n+2 : ℕ)*markE μ β x Q+σ n)).congr
    exact ae_of_all _ (physicalMaximumDensity_eq_tilt n μ h hnp (σ n))
  have hMass : ∀ᶠ n : ℕ in atTop,0 < energyDensity (sourceBaselineDensity n μ β x Q) (Ioo L R)
      (n+2 : ℕ) (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) (markK μ β Q) (σ n) := by
    filter_upwards [sourceMaximumEnergyDensity_regular μ h hnp hL hm] with n hn
    rw [←hDensity n]
    exact hn.2.2 _
  have hMoment := sourceMaximumRadialMoment_normalized_tendsto_zero μ h hnp hL hm hD σ hσ
  simp_rw [hRadial,hDensity] at hMoment
  have ht := fixed_energy_ratio_tendsto measurableSet_Ioo (fun n => sourceBaselineDensity n μ β x Q)
    hD σ hσ hi (fun _ _ _ => ENNReal.toReal_nonneg) hRadius hMass hMoment t
  simpa only [hPlus,hDensity] using ht

end SlowEquilibration.SphericalMarkedWindows
