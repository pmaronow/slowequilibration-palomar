-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePurePCCountsAnalytic

/-! The isolated lowest dimension N=2 in source `prop:pc-counts` has a
finite genuine Kac--Rice count; the main asymptotic theorem uses N=n+3. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate
open scoped ENNReal
set_option autoImplicit false

theorem sourcePure_analytic_N2_critical_mean_finite
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (U : Set ℝ) (hU : MeasurableSet U) (R : ℝ) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let K := physicalEnergyWindow 2
      (Icc (sourcePureAnalyticCenter 2 E (β*x)-R)
        (sourcePureAnalyticCenter 2 E (β*x)+R)) U
    (∫⁻ J, actualScoreWindowCount 1
      (centerCoefficients (mixtureCoefficients μ) Q) K
      (fun _ _ => 1) J ∂disorderLaw 2 μ.maxDegree) < ⊤ := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let K := physicalEnergyWindow 2
    (Icc (sourcePureAnalyticCenter 2 E (β*x)-R)
      (sourcePureAnalyticCenter 2 E (β*x)+R)) U
  have hK : MeasurableSet K :=
    rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul (2 : ℝ))) hU
  rw [actual_pure_count_intensity 0 p hp a ha h.overlap_range.1 K hK]
  exact actual_pure_count_intensity_finite 0 p hp a ha h.overlap_range.1 K hK

end SlowEquilibration.SphericalMarkedWindows
