-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRadialEnergyTilt
public import SlowEquilibration.GaussianRadialTiltIntegrability
public import SlowEquilibration.ExpectedTailCentering

/-! Regularity of the actual physical-energy maximum density. The
original Kac--Rice radial intensity and actual covariance supply all
integrability and positivity premises internally. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open RadialGaussianBounds GaussianRadialEnergyTilt
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximumRadialDensity_integrable (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) :
    ∀ᶠ n : ℕ in atTop,∀ H : ℝ,
      IntegrableOn (fun k => (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal) (Ioo L R) := by
  obtain ⟨c,C,_hc,_hC,hGauss⟩ := sourceBaseline_density_gaussian_bounds μ h hnp hL hm
  let m := markK μ β Q
  let M := max (m-L) (R-m)
  have hRadius : ∀ k∈Ioo L R,|k-m| ≤ M := by
    intro k hk
    have hl : m-L ≤ M := le_max_left _ _
    have hr : R-m ≤ M := le_max_right _ _
    apply abs_le.mpr
    constructor <;> linarith [hk.1,hk.2]
  have hA := sourceEnergyCurvature_pos μ h.overlap_range.1 hnp
  have ha : 0 < sourceRadialCurvature μ Q/2 :=
    half_pos (sourceRadialCurvature_pos μ h.overlap_range.1 hnp)
  filter_upwards [hGauss] with n hGn
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hw : IntegrableOn (sourceBaselineDensity n μ β x Q) (Ioo L R) := by
    apply (((gaussian_integrable (mul_pos ha hN) m).const_mul C).restrict).mono'
    · exact (sourceBaselineDensity_measurable n μ β x Q).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      rw [Real.norm_of_nonneg (show 0 ≤ sourceBaselineDensity n μ β x Q k from ENNReal.toReal_nonneg)]
      exact (hGn k hk).2
  intro H
  have ht := tiltedDensity_integrableOn (B := sourceEnergyRadialCross μ Q) (c₀ := β*x) measurableSet_Ioo hw
    (fun _ _ => ENNReal.toReal_nonneg) hA.le hN hRadius (H-(n+2 : ℕ)*markE μ β x Q)
  apply ht.congr
  apply ae_of_all
  intro k
  have he := physicalMaximumDensity_eq_tilt n μ h hnp (H-(n+2 : ℕ)*markE μ β x Q) k
  have hcancel : (n+2 : ℕ)*markE μ β x Q+(H-(n+2 : ℕ)*markE μ β x Q)=H := by ring
  rw [hcancel] at he
  exact he.symm

/-- These are actual upper tails in physical (unnormalized) energy. -/
def sourceMaximumEnergyTail (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) : ℝ → ℝ :=
  ExpectedTailCentering.tail (sourceMaximumEnergyDensity n μ Q U)

theorem sourceMaximumEnergyDensity_regular (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) :
    ∀ᶠ n : ℕ in atTop,
      Continuous (sourceMaximumEnergyDensity n μ Q (Ioo L R)) ∧
      Integrable (sourceMaximumEnergyDensity n μ Q (Ioo L R)) ∧
      ∀ H : ℝ,0 < sourceMaximumEnergyDensity n μ Q (Ioo L R) H := by
  obtain ⟨c,C,_hc,_hC,hGauss⟩ := sourceBaseline_density_gaussian_bounds μ h hnp hL hm
  obtain ⟨c',C',hc',_hC',hMass⟩ := sourceBaseline_radial_normalization μ h hnp hL hm
  let m := markK μ β Q
  let M := max (m-L) (R-m)
  have hM : 0 ≤ M := (sub_pos.mpr hm.1).le.trans (le_max_left _ _)
  have hRadius : ∀ k∈Ioo L R,|k-m| ≤ M := by
    intro k hk
    have hl : m-L ≤ M := le_max_left _ _
    have hr : R-m ≤ M := le_max_right _ _
    apply abs_le.mpr
    constructor <;> linarith [hk.1,hk.2]
  have hA := sourceEnergyCurvature_pos μ h.overlap_range.1 hnp
  have ha : 0 < sourceRadialCurvature μ Q/2 :=
    half_pos (sourceRadialCurvature_pos μ h.overlap_range.1 hnp)
  filter_upwards [hGauss,hMass] with n hGn hMn
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hw : IntegrableOn (sourceBaselineDensity n μ β x Q) (Ioo L R) := by
    apply (((gaussian_integrable (mul_pos ha hN) m).const_mul C).restrict).mono'
    · exact (sourceBaselineDensity_measurable n μ β x Q).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      rw [Real.norm_of_nonneg (show 0 ≤ sourceBaselineDensity n μ β x Q k from ENNReal.toReal_nonneg)]
      exact (hGn k hk).2
  have hMassPos : 0 < ∫ k in Ioo L R,sourceBaselineDensity n μ β x Q k :=
    (div_pos hc' (Real.sqrt_pos.mpr hN)).trans_le hMn.1
  have he : sourceMaximumEnergyDensity n μ Q (Ioo L R)=fun H =>
      energyDensity (sourceBaselineDensity n μ β x Q) (Ioo L R) (n+2 : ℕ)
        (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q) (β*x) m
        (H-(n+2 : ℕ)*markE μ β x Q) := by
    funext H
    have ht := sourceMaximumEnergyDensity_eq_tilt_integral n μ h hnp (Ioo L R)
      (H-(n+2 : ℕ)*markE μ β x Q)
    have hcancel : (n+2 : ℕ)*markE μ β x Q+(H-(n+2 : ℕ)*markE μ β x Q)=H := by ring
    rw [hcancel] at ht
    exact ht
  rw [he]
  have h0 : ∀ k∈Ioo L R,0 ≤ sourceBaselineDensity n μ β x Q k :=
    fun _ _ => ENNReal.toReal_nonneg
  refine ⟨?_,?_,?_⟩
  · exact (energyDensity_continuous measurableSet_Ioo hw h0 hA.le hN hM hRadius).comp
      (continuous_id.sub continuous_const)
  · exact (energyDensity_integrable measurableSet_Ioo hw h0 hA hN hM hRadius).comp_sub_right _
  · intro H
    exact energyDensity_pos measurableSet_Ioo hw h0 hMassPos hA.le hN hRadius _

/-- The true physical-energy upper tail has the actual density as its
negative derivative and is globally strictly decreasing. -/
theorem sourceMaximumEnergyTail_regular (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) :
    ∀ᶠ n : ℕ in atTop,
      Continuous (sourceMaximumEnergyTail n μ Q (Ioo L R)) ∧
      StrictAnti (sourceMaximumEnergyTail n μ Q (Ioo L R)) ∧
      ∀ H : ℝ,HasDerivAt (sourceMaximumEnergyTail n μ Q (Ioo L R))
        (-sourceMaximumEnergyDensity n μ Q (Ioo L R) H) H := by
  filter_upwards [sourceMaximumEnergyDensity_regular μ h hnp hL hm] with n hn
  exact ⟨ExpectedTailCentering.tail_continuous hn.2.1 hn.1,
    ExpectedTailCentering.tail_strictAnti hn.2.1 hn.1 hn.2.2,
    ExpectedTailCentering.tail_hasDerivAt hn.2.1 hn.1⟩

end SlowEquilibration.SphericalMarkedWindows
