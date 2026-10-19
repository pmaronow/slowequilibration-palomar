-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRadialEnergyTilt
public import SlowEquilibration.GaussianRadialTiltAnalysis
public import SlowEquilibration.GaussianRadialTiltLogBounds
public import SlowEquilibration.NatLogWindowScales

/-! Actual maximum intensity normalization throughout fixed logarithmic
physical-energy windows, derived from the original contact saddle. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open RadialGaussianBounds RadialLaplaceBounds GaussianRadialEnergyTilt
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximumEnergyDensity_log_window (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ σ : ℝ,
      |σ| ≤ D*Real.log (n+2 : ℕ) →
      c*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) ≤
        sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ) ∧
      sourceMaximumEnergyDensity n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ) ≤
        C*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) := by
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
  refine ⟨lowerConstant c b*Real.exp (-correctionBound b A B),
    upperConstant C a*Real.exp (correctionBound a A B),
    mul_pos (lowerConstant_pos hc) (Real.exp_pos _),
    mul_pos (by unfold upperConstant;exact mul_pos hC (Real.sqrt_pos.mpr (div_pos Real.pi_pos ha)))
      (Real.exp_pos _),?_⟩
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
  rw [sourceMaximumEnergyDensity_eq_tilt_integral n μ h hnp]
  exact tilted_integral_log_bounds measurableSet_Ioo hc.le hC.le ha hb hN
    (tiltedDensity_integrableOn measurableSet_Ioo hw (fun _ _ => ENNReal.toReal_nonneg)
      hA hN hRadius σ)
    (fun _ _ => ENNReal.toReal_nonneg) (fun k hk => (hn k hk).1) (fun k hk => (hn k hk).2)
    hInside hs.1

end SlowEquilibration.SphericalMarkedWindows
