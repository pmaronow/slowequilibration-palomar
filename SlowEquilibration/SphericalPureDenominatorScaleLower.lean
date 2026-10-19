-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureDenominatorEvent
public import SlowEquilibration.SphericalPureDenominatorCenteredData
public import SlowEquilibration.SourcePhysicalPairRetainedWindowGeometry

/-! An unconditional lower tail for the original proper-pure partition
function on the exact critical-band Palm scale. The source manuscript's
annealed scale is related to this deterministic scale by its separate
latitude Laplace proposition. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureDenominatorScaleLower
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalLightBandMark
open SphericalPureDenominatorPalmTransfer SphericalPureDenominatorEvent
open SphericalPureDenominatorCenteredData PairConditionalDeterminantMoments
open TwoAtomStationarity LatitudeGroundTrial
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The physical centered pure window lies in every fixed positive
normalized-energy neighborhood of its contact mark in all large dimensions. -/
theorem pure_centered_window_eventually_in_energy_box
    {E c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (m : ℕ → ℝ)
    (hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-((j+2:ℕ)*E-Real.log (j+2:ℕ)/(2*c))| ≤ M)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (δ L : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      sourcePureCenteredNormalizedWindow n m E δ (-L) L ⊆
        Icc (E-δ0) (E+δ0) := by
  have hBounds := (tendsto_add_atTop_nat 1).eventually
    (source_logarithmic_center_offset_bounds hc hM hδ0 m hcenter (-L) L)
  filter_upwards [hBounds] with n hn
  intro b hb
  have hN : 0 < (((n+3:ℕ):ℝ)) := by positivity
  have hval : ((n+3:ℕ):ℝ)*b ∈
      Icc (m (n+1)-L) (m (n+1)+L) := by
    simpa only [sourcePureCenteredNormalizedWindow, sub_eq_add_neg] using hb.1
  constructor
  · exact (mul_le_mul_iff_right₀ hN).mp (hn.1.trans hval.1)
  · exact (mul_le_mul_iff_right₀ hN).mp (hval.2.trans hn.2)

/-- The literal window's lower physical-energy endpoint is valid in every
dimension, including before its fixed normalized cutoff becomes relevant. -/
theorem pure_centered_window_energy_lower
    (n : ℕ) (m : ℕ → ℝ) (E δ L : ℝ)
    (v : ℝ) (hv : v ∈ sourcePureCenteredNormalizedWindow n m E δ (-L) L) :
    m (n+1)-L ≤ ((n+3:ℕ):ℝ)*v := by
  have hh := hv.1.1
  simpa only [sub_eq_add_neg] using hh

/-- A certificate, the actual pure value-only Palm law, the original
marked Kac--Rice formula, and the retained-center second moment together
give the condensed partition-function denominator lower tail on the exact
physical Palm band scale. All quantifiers are in manuscript order:
target error, fixed window/threshold, then dimension. -/
theorem pure_partition_source_band_scale_lower_tail
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    ∃ m : ℕ → ℝ, ∃ M : ℝ, 0 < M ∧
      (∀ᶠ j : ℕ in atTop,
        |m j-((j+2:ℕ)*E-Real.log (j+2:ℕ)/(2*(β*x)))| ≤ M) ∧
      ∀ ρ : ℝ, 0 < ρ → ∃ L δ b : ℝ,
        0 < L ∧ 0 < δ ∧ 0 < b ∧
        Filter.limsup (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
              δ*Real.exp (-β*L)*
                sourceCriticalBandScale (n+2) μ h.overlap_range β
                  (m (n+1))}) atTop ≤ 2*ρ := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  obtain ⟨m,M,C,cut,η,ε,δ0,hM,hδ0,hcenter,hUnfiltered,hZero⟩ :=
    pure_denominator_center_data p hp alpha halpha h
  obtain ⟨ε0,b,hε0,hb,hbQ,hLightCount⟩ :=
    pure_source_light_count_le_count_eventually p hp alpha halpha h
  refine ⟨m,M,hM,hcenter,?_⟩
  intro ρ hρ
  let k := 1+(1-ε)/(cut^2-ε)
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hPos : Tendsto (fun T : ℝ => Real.exp ((β*x)*T)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc)
  have hNeg : Tendsto (fun T : ℝ => Real.exp (-(β*x)*T)) atTop (𝓝 (0:ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hDen : Tendsto (fun T : ℝ =>
      Real.exp ((β*x)*T)-Real.exp (-(β*x)*T)) atTop atTop := by
    simpa only [sub_eq_add_neg] using hPos.atTop_add hNeg.neg
  have hFrac : Tendsto (fun T : ℝ =>
      k/(Real.exp ((β*x)*T)-Real.exp (-(β*x)*T))) atTop (𝓝 (0:ℝ)) :=
    hDen.const_div_atTop k
  have hSmall : ∀ᶠ T : ℝ in atTop,
      0 < T ∧ k/(Real.exp ((β*x)*T)-Real.exp (-(β*x)*T)) < ρ := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      hFrac.eventually (gt_mem_nhds hρ)] with T ht hs
    exact ⟨ht,hs⟩
  obtain ⟨L,hL,hZeroSmall⟩ := hSmall.exists
  let W (n : ℕ) := sourcePureCenteredNormalizedWindow n m E δ0 (-L) L
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let aN (n : ℕ) := sourceUnfilteredValueWindowMean (n+2) μ Q (W n)
  let A := Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)
  have hA : 0 < A := by
    dsimp [A]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith [hc,hL]))
  have hMean : Tendsto aN atTop (𝓝 A) := by
    simpa only [aN,W,A,neg_mul,mul_neg,neg_neg] using
      (hUnfiltered (-L) L (by linarith))
  let B := A+1
  have hB : 0 < B := by dsimp [B]; linarith
  have hMeanBound : ∀ᶠ n : ℕ in atTop, aN n ≤ B := by
    filter_upwards [hMean.eventually
      (gt_mem_nhds (show A < B by dsimp [B]; linarith))]
      with n hn
    exact hn.le
  let εLight := ρ/B
  have hεLight : 0 < εLight := div_pos hρ hB
  obtain ⟨δ,hδ,hCount⟩ := hLightCount εLight hεLight
  have hWindow : ∀ᶠ n : ℕ in atTop,
      W n ⊆ Icc (E-ε0) (E+ε0) :=
    pure_centered_window_eventually_in_energy_box hc hM.le m hcenter
      ε0 hε0 δ0 L
  have hMassBound : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, actualValueWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q) (W n)
        (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) ≤
          ENNReal.ofReal B := by
    filter_upwards [hMeanBound] with n hn
    have hfinite := sourceUnfilteredValueWindowCount_lintegral_lt_top
      (n+2) (by omega) μ h.overlap_range.1 (W n)
    rw [← ENNReal.ofReal_toReal hfinite.ne]
    exact ENNReal.ofReal_le_ofReal hn
  have hLight : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, actualValueWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q) (W n)
        (sourceLightBandMark (n+1) μ h.overlap_range β (m (n+1)) δ
          (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
          ∂disorderLaw (n+3) μ.maxDegree) ≤ ENNReal.ofReal ρ := by
    filter_upwards [hCount,hWindow,hMassBound] with n hn hw hmass
    have hCountBound := hn (W n)
      (sourcePureCenteredNormalizedWindow_measurable n m E δ0 (-L) L)
      hw (m (n+1))
    calc
      _ ≤ ENNReal.ofReal εLight *
        (∫⁻ J, actualValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) (W n)
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) := hCountBound
      _ ≤ ENNReal.ofReal εLight * ENNReal.ofReal B :=
        by simpa only [mul_comm] using
          (mul_le_mul_left hmass (ENNReal.ofReal εLight))
      _ = ENNReal.ofReal ρ := by
        rw [← ENNReal.ofReal_mul hεLight.le]
        congr 1
        dsimp [εLight]
        field_simp
  have hBound := pure_partition_low_limsup_of_zero_and_light_bounds
    p hp alpha halpha h W
      (fun n => sourcePureCenteredNormalizedWindow_measurable
        n m E δ0 (-L) L)
      m L δ b (g/2) C ε η E G ρ (k/A) hδ.le hρ.le
      (fun n v hv => pure_centered_window_energy_lower n m E δ0 L v hv)
      (by simpa only [W,G,g,k,A,sub_eq_add_neg] using hZero L hL)
      hLight
  refine ⟨L,δ,b,hL,hδ,hb,?_⟩
  exact hBound.trans (by linarith [hZeroSmall])

end
end SlowEquilibration.SphericalPureDenominatorScaleLower
