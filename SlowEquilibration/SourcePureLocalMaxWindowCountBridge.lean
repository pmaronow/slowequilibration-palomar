-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxFullCenterLimits
public import SlowEquilibration.ExpectedCompactWindowLimits
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact proper-pure Kac--Rice conversion from the ordinary count of
negative-Hessian local maxima with a value and radial-mark window to the
mark-truncated physical-energy intensity integral. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalSequentialRegression
open TwoAtomStationarity SphericalTAPCertificate
open scoped ENNReal Topology
set_option maxHeartbeats 400000

def sourcePureTruncatedLocalMaxWindowMean
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q l r L R : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp a ha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let I := Icc L R ∩ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  (∫⁻ J, actualLocalMaxCount (n+1) c
      (physicalEnergyWindow (n+2) I univ) J
    ∂disorderLaw (n+2) μ.maxDegree).toReal

theorem pureLocalMaxPhysicalIntensity_ne_top
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q H : ℝ) :
    pureLocalMaxPhysicalIntensity n p hp a ha Q H ≠ ⊤ := by
  have hs := sphereKRPrefactor_ne_top (n+1) (FiniteMixture.pure p hp a ha) Q
  unfold pureLocalMaxPhysicalIntensity pureNegativeIntensity physicalValuePdf
  finiteness

theorem sourcePureTruncatedLocalMaxWindowMean_eq_integral
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (l r L R : ℝ) :
    sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r L R =
      ∫ H in Icc L R,
        pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) H := by
  let μ := FiniteMixture.pure p hp a ha
  let I := Icc L R ∩ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hI : MeasurableSet I := measurableSet_Icc.inter measurableSet_Ioo
  have hKR := actual_pure_localMax_physical_intensity n p hp a ha hQ I hI
  change (∫⁻ J, actualLocalMaxCount (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+2) I univ) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ H in I, pureLocalMaxPhysicalIntensity n p hp a ha Q H at hKR
  change (∫⁻ J, actualLocalMaxCount (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+2) I univ) J
      ∂disorderLaw (n+2) μ.maxDegree).toReal = _
  rw [hKR]
  rw [←integral_toReal (pureLocalMaxPhysicalIntensity_measurable n p hp a ha Q).aemeasurable
    (ae_of_all _ (fun H => lt_top_iff_ne_top.mpr
      (pureLocalMaxPhysicalIntensity_ne_top n p hp a ha Q H)))]
  rw [show ∫ H in I, (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal =
      ∫ H in Icc L R, pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) H by
      simpa only [pureTruncatedLocalMaxDensity,I] using
        (setIntegral_indicator (μ := volume) (s := Icc L R)
          (t := Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r))
          (f := fun H => (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal)
          measurableSet_Ioo).symm]

end SlowEquilibration.SphericalMarkedWindows
