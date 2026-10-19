-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumCenteringEnvelopes
public import SlowEquilibration.GaussianRadialTiltMoment

/-! The actual radial first moment tends to zero uniformly in fixed
logarithmic physical-energy windows. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open RadialGaussianBounds RadialLaplaceBounds GaussianRadialEnergyTilt
open scoped Topology
set_option maxHeartbeats 300000

def sourceMaximumRadialMoment (n : ℕ) (μ : FiniteMixture) (β Q : ℝ) (U : Set ℝ) (H : ℝ) : ℝ :=
  ∫ k in U,|k-markK μ β Q| * (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal

theorem sourceMaximumRadialMoment_eq_tilt (n : ℕ) (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (U : Set ℝ) (σ : ℝ) :
    sourceMaximumRadialMoment n μ β Q U ((n+2 : ℕ)*markE μ β x Q+σ)=
      radialMoment (sourceBaselineDensity n μ β x Q) U (n+2 : ℕ) (sourceEnergyCurvature μ Q)
        (sourceEnergyRadialCross μ Q) (β*x) (markK μ β Q) σ := by
  unfold sourceMaximumRadialMoment radialMoment
  apply integral_congr_ae
  exact ae_of_all _ (fun k => congrArg (fun z : ℝ => |k-markK μ β Q| * z)
    (physicalMaximumDensity_eq_tilt n μ h hnp σ k))

theorem sourceMaximumRadialMoment_log_window (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ,0 < K ∧ ∀ᶠ n : ℕ in atTop,∀ σ : ℝ,|σ| ≤ D*Real.log (n+2 : ℕ) →
      sourceMaximumRadialMoment n μ β Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ) ≤
        K*(1/Real.sqrt (n+2 : ℕ)+|σ|/(n+2 : ℕ))*
          sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ) := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := sourceBaseline_density_gaussian_bounds μ h hnp hL hm
  let a := sourceRadialCurvature μ Q/2
  let b := sourceBaselineLowerCurvature μ Q L/2
  let A := sourceEnergyCurvature μ Q
  let B := sourceEnergyRadialCross μ Q
  let m := markK μ β Q
  let u := min (m-L) (R-m)
  let M := max (m-L) (R-m)
  have hκ := sourceRadialCurvature_pos μ h.overlap_range.1 hnp
  have ha : 0 < a := half_pos hκ
  have hb : 0 < b := by dsimp [b,sourceBaselineLowerCurvature];positivity
  have hA : 0 ≤ A := (sourceEnergyCurvature_pos μ h.overlap_range.1 hnp).le
  have hu : 0 < u := lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  have hRadius : ∀ k∈Ioo L R,|k-m| ≤ M := by
    intro k hk
    have hl : m-L ≤ M := le_max_left _ _
    have hr : R-m ≤ M := le_max_right _ _
    apply abs_le.mpr
    constructor <;> linarith [hk.1,hk.2]
  refine ⟨normalizedMomentConstant c C a b A B,?_,?_⟩
  · unfold normalizedMomentConstant gaussianMomentConstant gaussianShiftMomentConstant lowerConstant
    positivity
  filter_upwards [hbounds,NatLogWindowScales.uniform_log_window_eventually hD hb hu B]
    with n hn hsmall
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hw : IntegrableOn (sourceBaselineDensity n μ β x Q) (Ioo L R) := by
    apply (((gaussian_integrable (mul_pos ha hN) m).const_mul C).restrict).mono'
    · exact (sourceBaselineDensity_measurable n μ β x Q).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      rw [Real.norm_of_nonneg (show 0 ≤ sourceBaselineDensity n μ β x Q k from ENNReal.toReal_nonneg)]
      exact (hn k hk).2
  intro σ hσ
  have hs := hsmall σ hσ
  have hInside : Icc (shiftedCenter b (n+2 : ℕ) B m σ-1/Real.sqrt (n+2 : ℕ))
      (shiftedCenter b (n+2 : ℕ) B m σ+1/Real.sqrt (n+2 : ℕ))⊆Ioo L R := by
    intro k hk
    have hul : u ≤ m-L := min_le_left _ _
    have hur : u ≤ R-m := min_le_right _ _
    have hdlo := neg_le_abs (B*σ/(2*b*(n+2 : ℕ)))
    have hdhi := le_abs_self (B*σ/(2*b*(n+2 : ℕ)))
    dsimp only [shiftedCenter] at hk
    constructor <;> linarith [hk.1,hk.2,hs.2]
  rw [sourceMaximumRadialMoment_eq_tilt n μ h hnp,
    sourceMaximumEnergyDensity_eq_tilt_integral n μ h hnp]
  exact radialMoment_le_density_scale measurableSet_Ioo hc hC.le ha hb hN
    (tiltedDensity_integrableOn measurableSet_Ioo hw (fun _ _ => ENNReal.toReal_nonneg)
      hA hN hRadius σ)
    (fun _ _ => ENNReal.toReal_nonneg) (fun k hk => (hn k hk).1) (fun k hk => (hn k hk).2)
    hInside hs.1

theorem sourceMaximumRadialMoment_normalized_tendsto_zero (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop,|σ n| ≤ D*Real.log (n+2 : ℕ)) :
    Tendsto (fun n : ℕ =>
      sourceMaximumRadialMoment n μ β Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n))
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := sourceMaximumRadialMoment_log_window μ h hnp hL hm hD
  have ht : Tendsto (fun n : ℕ => K*(1/Real.sqrt (n+2 : ℕ)+D*Real.log (n+2 : ℕ)/(n+2 : ℕ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one,mul_zero,zero_add,mul_div_assoc] using
      (NatLogWindowScales.inverse_sqrt_dimension_tendsto_zero.add
        ((NatLogWindowScales.log_power_div_dimension_tendsto_zero 1).const_mul D)).const_mul K
  have hnonn : ∀ᶠ n : ℕ in atTop,0 ≤
      sourceMaximumRadialMoment n μ β Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n) := by
    filter_upwards [sourceMaximumEnergyDensity_regular μ h hnp hL hm] with n hn
    apply div_nonneg _ (hn.2.2 _).le
    exact integral_nonneg_of_ae (ae_of_all _ (fun k => mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg))
  have hup : ∀ᶠ n : ℕ in atTop,
      sourceMaximumRadialMoment n μ β Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ n) ≤
      K*(1/Real.sqrt (n+2 : ℕ)+D*Real.log (n+2 : ℕ)/(n+2 : ℕ)) := by
    filter_upwards [hσ,hbound,sourceMaximumEnergyDensity_regular μ h hnp hL hm] with n hσn hn hreg
    apply (div_le_iff₀ (hreg.2.2 _)).mpr
    refine (hn (σ n) hσn).trans ?_
    have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hd := div_le_div_of_nonneg_right hσn hN.le
    have hscale : 1/Real.sqrt (n+2 : ℕ)+|σ n|/(n+2 : ℕ) ≤
        1/Real.sqrt (n+2 : ℕ)+D*Real.log (n+2 : ℕ)/(n+2 : ℕ) := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hK.le) (hreg.2.2 _).le
  exact squeeze_zero' hnonn hup ht

end SlowEquilibration.SphericalMarkedWindows
