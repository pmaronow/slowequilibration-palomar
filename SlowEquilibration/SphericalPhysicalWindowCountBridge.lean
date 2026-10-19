-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumCenteredLimits
public import SlowEquilibration.SphericalPhysicalMaximumRatio
public import SlowEquilibration.ENNRadialIntegralBridge

/-! Literal maximum and critical-point expected counts in fixed physical
energy windows, with finite expectations in every dimension. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel SphericalSequentialRegression SphericalGaussianJet SphericalPosteriorMaps
open scoped Topology ENNReal
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

irreducible_def sourceMaximumWindowMass (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) (l r : ℝ) : ℝ≥0∞ :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  ∫⁻ J,actualLocalMaxCount (n+1) c (physicalEnergyWindow (n+2) (Icc l r) U) J
    ∂disorderLaw (n+2) μ.maxDegree

irreducible_def sourceCriticalWindowMass (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) (l r : ℝ) : ℝ≥0∞ :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  ∫⁻ J,actualScoreWindowCount (n+1) c (physicalEnergyWindow (n+2) (Icc l r) U) (fun _ _ => 1) J
    ∂disorderLaw (n+2) μ.maxDegree

def sourceMaximumWindowMean (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) (l r : ℝ) : ℝ :=
  (sourceMaximumWindowMass n μ Q U l r).toReal

def sourceCriticalWindowMean (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) (l r : ℝ) : ℝ :=
  (sourceCriticalWindowMass n μ Q U l r).toReal

theorem sourceMaximumWindowMass_finite (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (U : Set ℝ) (l r : ℝ) : sourceMaximumWindowMass n μ Q U l r < ⊤ := by
  rw [sourceMaximumWindowMass_def]
  rw [lintegral_congr_ae (actualLocalMaxCount_eq_negative_ae (n+1) (by omega) μ hQ _)]
  simp_rw [actualNegativeCriticalCount_eq_mark]
  exact bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ _ _ 1 (by simp)
    (by intro J y;unfold negativeHessianMark;split_ifs <;> simp)

theorem sourceCriticalWindowMass_finite (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (U : Set ℝ) (l r : ℝ) : sourceCriticalWindowMass n μ Q U l r < ⊤ := by
  rw [sourceCriticalWindowMass_def]
  exact bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ _
    (fun _ _ => 1) 1 (by simp) (fun _ _ => le_rfl)

theorem actual_mixed_critical_physical_intensity (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (I U : Set ℝ) (hI : MeasurableSet I) (hU : MeasurableSet U) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J,actualScoreWindowCount (n+1) c (physicalEnergyWindow (n+2) I U) (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree)=
      ∫⁻ H in I,∫⁻ k in U,mixedCriticalPhysicalIntensity n μ Q H k := by
  dsimp only
  rw [physicalEnergyWindow,actual_mixed_rectangular_count n μ hQ hnp _ _
    (hI.preimage (measurable_const_mul ((n+2 : ℕ) : ℝ))) hU]
  rw [setLIntegral_positive_rescale (n+2 : ℕ) (by positivity)]
  apply lintegral_congr
  intro H
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

theorem mixedLocalMaxPhysicalIntensity_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measurable (fun p : ℝ × ℝ => mixedLocalMaxPhysicalIntensity n μ Q p.1 p.2) := by
  have hp : Measurable (fun p : ℝ × ℝ => (p.1/(n+2 : ℕ),p.2)) := by fun_prop
  simpa only [mixedLocalMaxPhysicalIntensity,Function.comp_def,Pi.mul_def,scorePairEquiv_apply] using
    measurable_const.mul ((mixedNegativeIntensity_measurable n μ Q).comp (scorePairEquiv.measurable.comp hp))

theorem mixedLocalMaxPhysicalIntensity_ne_top (n : ℕ) (μ : FiniteMixture) (Q H k : ℝ) :
    mixedLocalMaxPhysicalIntensity n μ Q H k ≠ ⊤ := by
  have hp := sphereKRPrefactor_ne_top (n+1) μ Q
  unfold mixedLocalMaxPhysicalIntensity mixedNegativeIntensity physicalScorePdf
  finiteness

theorem sourceMaximumWindowMean_eq_integral (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) :
    ∀ᶠ n : ℕ in atTop,∀ l r : ℝ,
      sourceMaximumWindowMean n μ Q (Ioo L R) l r=
        ∫ H in Icc l r,sourceMaximumEnergyDensity n μ Q (Ioo L R) H := by
  filter_upwards [sourceMaximumRadialDensity_integrable μ h hnp hL hm] with n hn
  intro l r
  unfold sourceMaximumWindowMean
  have hKR : sourceMaximumWindowMass n μ Q (Ioo L R) l r=
      ∫⁻ H in Icc l r,∫⁻ k in Ioo L R,mixedLocalMaxPhysicalIntensity n μ Q H k := by
    rw [sourceMaximumWindowMass_def]
    exact actual_mixed_localMax_physical_intensity n μ h.overlap_range.1 hnp _ _ measurableSet_Icc measurableSet_Ioo
  rw [hKR]
  exact ENNRadialIntegralBridge.iterated_toReal_eq (mixedLocalMaxPhysicalIntensity n μ Q) (Ioo L R) (Icc l r)
    (mixedLocalMaxPhysicalIntensity_measurable n μ Q) (mixedLocalMaxPhysicalIntensity_ne_top n μ Q) hn

theorem sourceMaximumWindowMean_eq_tail_difference (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) :
    ∀ᶠ n : ℕ in atTop,∀ l r : ℝ,l ≤ r →
      sourceMaximumWindowMean n μ Q (Ioo L R) l r=
        sourceMaximumEnergyTail n μ Q (Ioo L R) l-sourceMaximumEnergyTail n μ Q (Ioo L R) r := by
  filter_upwards [sourceMaximumWindowMean_eq_integral μ h hnp hL hm,
    sourceMaximumEnergyDensity_regular μ h hnp hL hm] with n hn hregular
  intro l r hlr
  rw [hn l r]
  have he := intervalIntegral.integral_Ici_sub_Ici' (hregular.2.1.integrableOn (s := Ici l))
    (hregular.2.1.integrableOn (s := Ici r))
  rw [intervalIntegral.integral_of_le hlr,←integral_Icc_eq_integral_Ioc] at he
  exact he.symm

end SlowEquilibration.SphericalMarkedWindows
