-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumEnergyMicroSlope

/-! The exact all-dimension physical logarithmic energy slope satisfies the
source score inequalities, including every energy above the lower cutoff. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory TwoAtomStationarity
set_option maxHeartbeats 400000

theorem sourceEnergySlope_monotone_energy (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (k : ℝ) : Monotone (fun e => sourceEnergySlope μ Q e k) := by
  intro a b hab
  unfold sourceEnergySlope
  have hA := sourceEnergyCurvature_pos μ hQ hnp
  nlinarith

/-- The lower source score bound extends to every energy above the physical
lower cutoff, with no asymptotic exception. -/
theorem sourceMaximumEnergyLogSlope_lower_all_dimensions (n : ℕ) (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 ≤ δ)
    (hScore : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k ∈ Icc L R,
      β*x/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2)
    {H : ℝ} (hH : (n+2 : ℕ)*(markE μ β x Q-δ) ≤ H) :
    β*x/2 ≤ -sourceMaximumEnergyLogSlope n μ Q (Ioo L R) H := by
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hE : markE μ β x Q-δ ≤ H/(n+2 : ℕ) := (le_div_iff₀ hN).mpr (by nlinarith)
  have hPoint (k : ℝ) (hk : k ∈ Ioo L R) : β*x/2 ≤ sourceEnergySlope μ Q (H/(n+2 : ℕ)) k :=
    ((hScore (markE μ β x Q-δ) (by constructor <;> linarith) k ⟨hk.1.le,hk.2.le⟩).1).trans
      (sourceEnergySlope_monotone_energy μ h.overlap_range.1 hnp k hE)
  let f := fun k => (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal
  have hf : IntegrableOn f (Ioo L R) := sourceMaximumRadialDensity_integrable_all_dimensions n μ h hnp hL hm H
  have hScoreInt := (sourceMaximumEnergyDensity_hasDerivAt_all_dimensions n μ h hnp hL hm H).1
  have hInt : β*x/2*sourceMaximumEnergyDensity n μ Q (Ioo L R) H ≤
      ∫ k in Ioo L R,sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*f k := by
    rw [sourceMaximumEnergyDensity,←integral_const_mul]
    exact setIntegral_mono_on (hf.const_mul _) hScoreInt measurableSet_Ioo
      (fun k hk => mul_le_mul_of_nonneg_right (hPoint k hk) ENNReal.toReal_nonneg)
  rw [sourceMaximumEnergyLogSlope_eq_score n μ h hnp hL hm,neg_div,neg_neg]
  apply (le_div_iff₀ (sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm H)).mpr
  exact hInt

theorem sourceMaximumEnergyLogSlope_upper_all_dimensions (n : ℕ) (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hScore : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k ∈ Icc L R,
      β*x/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2)
    {H : ℝ} (hH : H/(n+2 : ℕ) ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ)) :
    -sourceMaximumEnergyLogSlope n μ Q (Ioo L R) H ≤ (β*x+β)/2 := by
  let f := fun k => (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal
  have hf : IntegrableOn f (Ioo L R) := sourceMaximumRadialDensity_integrable_all_dimensions n μ h hnp hL hm H
  have hScoreInt := (sourceMaximumEnergyDensity_hasDerivAt_all_dimensions n μ h hnp hL hm H).1
  have hInt : (∫ k in Ioo L R,sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*f k) ≤
      (β*x+β)/2*sourceMaximumEnergyDensity n μ Q (Ioo L R) H := by
    rw [sourceMaximumEnergyDensity,←integral_const_mul]
    exact setIntegral_mono_on hScoreInt (hf.const_mul _) measurableSet_Ioo
      (fun k hk => mul_le_mul_of_nonneg_right (hScore _ hH k ⟨hk.1.le,hk.2.le⟩).2 ENNReal.toReal_nonneg)
  rw [sourceMaximumEnergyLogSlope_eq_score n μ h hnp hL hm,neg_div,neg_neg]
  apply (div_le_iff₀ (sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm H)).mpr
  exact hInt
end SlowEquilibration.SphericalMarkedWindows
