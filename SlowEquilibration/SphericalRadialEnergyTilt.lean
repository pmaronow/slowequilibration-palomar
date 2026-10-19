-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRadialBaselineLaplace
public import SlowEquilibration.GaussianRadialEnergyTilt

/-! Exact identification of the genuine physical maximum intensity with
its baseline radial Gaussian energy reweighting. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel SphericalSequentialRegression
open GaussianRadialEnergyTilt
open scoped Topology ENNReal
set_option maxHeartbeats 300000

def sourceEnergyRadialCross (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  (((μ.scoreCovariance Q)⁻¹) 0 1+((μ.scoreCovariance Q)⁻¹) 1 0)/2

theorem mixedMaximumEnergyRadialIntensity_eq_physical (n : ℕ) (μ : FiniteMixture) (Q H k : ℝ) :
    mixedMaximumEnergyRadialIntensity n μ Q H k=mixedLocalMaxPhysicalIntensity n μ Q H k := by
  unfold mixedMaximumEnergyRadialIntensity mixedLocalMaxPhysicalIntensity
  rw [div_eq_mul_inv,ENNReal.ofReal_inv_of_pos (by positivity),scorePairEquiv_apply]
  ac_rfl

/-- The radial dependence of the exact energy score is affine around the
actual source contact, with its actual mixed covariance coefficient. -/
theorem sourceEnergySlope_baseline_affine (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree<μ.maxDegree) (k : ℝ) :
    sourceEnergySlope μ Q (markE μ β x Q) k=
      β*x+sourceEnergyRadialCross μ Q*(k-markK μ β Q) := by
  calc
    _=sourceEnergySlope μ Q (markE μ β x Q) (markK μ β Q)+
      sourceEnergyRadialCross μ Q*(k-markK μ β Q) := by
        unfold sourceEnergySlope sourceEnergyRadialCross
        ring
    _=_ := by rw [sourceEnergySlope_at_contact μ h hnp]

/-- Every physical energy is obtained from the true baseline intensity by
the exact Gaussian scalar tilt. -/
theorem physicalMaximumDensity_eq_tilt (n : ℕ) (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree<μ.maxDegree)
    (σ k : ℝ) :
    (mixedLocalMaxPhysicalIntensity n μ Q ((n+2 : ℕ)*markE μ β x Q+σ) k).toReal=
      tiltedDensity (sourceBaselineDensity n μ β x Q) (n+2 : ℕ)
        (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) (markK μ β Q) σ k := by
  have ht := mixedMaximumEnergyRadialIntensity_energy_tilt n μ Q
    ((n+2 : ℕ)*markE μ β x Q) k σ
  rw [mixedMaximumEnergyRadialIntensity_eq_physical,mixedMaximumEnergyRadialIntensity_eq_physical,
    mul_div_cancel_left₀ _ (by positivity),sourceEnergySlope_baseline_affine μ h hnp] at ht
  have he : -(β*x+sourceEnergyRadialCross μ Q*(k-markK μ β Q))*σ-
      sourceEnergyCurvature μ Q*σ^2/(2*(n+2 : ℕ))=
      -(β*x)*σ-sourceEnergyRadialCross μ Q*(k-markK μ β Q)*σ-
        sourceEnergyCurvature μ Q*σ^2/(2*(n+2 : ℕ)) := by ring
  rw [he] at ht
  have hh := congrArg ENNReal.toReal ht
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hh
  exact hh

/-- The actual source energy density is the radial integral of the
physical Kac--Rice maximum intensity, in unnormalized energy units. -/
def sourceMaximumEnergyDensity (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) (H : ℝ) : ℝ :=
  ∫ k in U,(mixedLocalMaxPhysicalIntensity n μ Q H k).toReal

theorem sourceMaximumEnergyDensity_eq_tilt_integral (n : ℕ) (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree<μ.maxDegree)
    (U : Set ℝ) (σ : ℝ) :
    sourceMaximumEnergyDensity n μ Q U ((n+2 : ℕ)*markE μ β x Q+σ)=
      ∫ k in U,tiltedDensity (sourceBaselineDensity n μ β x Q) (n+2 : ℕ)
        (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) (markK μ β Q) σ k := by
  unfold sourceMaximumEnergyDensity
  apply integral_congr_ae
  exact ae_of_all _ (physicalMaximumDensity_eq_tilt n μ h hnp σ)
end SlowEquilibration.SphericalMarkedWindows
