-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCaptureExpectationBound

/-! Actual pure microscopic capture from precisely the physical coarse
cover. The maximum, denominator, deep-energy, angular, and parameter-order
steps are all discharged for the original Hamiltonian and Gibbs law. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureCaptureFromCoarseCover
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalMarkedWindows
open SphericalTAPCertificate PureStationarity SphericalPureCapSourceScalars
open SourcePureCaptureFixedCapEstimates SourcePureCaptureBandComplementBound
open SourcePureCaptureExpectationBound PureCapturePhysicalDiagonalBridge
open SourceGaussianWindowFraction SourceGaussianLaplaceRatio
open scoped ENNReal Topology
set_option autoImplicit false

/-- Literal expected Gibbs mass outside all original critical-point bands
of microscopic width `w / sqrt N`, in the original energy window `M_N ± L`. -/
def pureMicroscopicUncovered (p : ℕ) (hp : 4 ≤ p)
    (β Q L w : ℝ) (d : ℕ) : ℝ :=
  expectedOriginalBandComplementMass d
    (FiniteMixture.pure p (by omega) 1 (by positivity)) β
    (pureSourceCenter p hp d) L (Real.sqrt Q) (w/Real.sqrt (d+2:ℕ))

theorem pureMicroscopicUncovered_nonneg (p : ℕ) (hp : 4 ≤ p)
    (β Q L w : ℝ) (d : ℕ) : 0 ≤ pureMicroscopicUncovered p hp β Q L w d :=
  expectedOriginalBandComplementMass_nonneg d _ β _ L _ _

theorem pureMicroscopicUncovered_antitone (p : ℕ) (hp : 4 ≤ p)
    (β Q : ℝ) {L L' w w' : ℝ} (hL : L ≤ L') (hw : w ≤ w') (d : ℕ) :
    pureMicroscopicUncovered p hp β Q L' w' d ≤
      pureMicroscopicUncovered p hp β Q L w d :=
  expectedOriginalBandComplementMass_antitone d _ β _ _ L L' _ _ hL
    (div_le_div_of_nonneg_right hw (Real.sqrt_nonneg _))

set_option maxHeartbeats 2000000 in
/-- Source microscopic capture, with the cap chosen by the proved fixed-cap
packet. The sole remaining physical input is the actual fixed-deficit
coarse cover for that cap; in particular no marked-sum or tightness estimate
is supplied. The chosen L,w work for all larger L,w. -/
theorem pure_microscopic_capture_of_coarse_cover
    (p : ℕ) (hp : 4 ≤ p) {β x Q a κ δ : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hEst : FixedCapEstimates p hp β Q a κ δ)
    (hcoarse : ∀ τ : ℝ, 0 < τ → Tendsto
      (fun d => expectedUncoveredGibbsMass d
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β a
        (pureEnergyConstant p (by omega)) τ) atTop (𝓝 (0:ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ L w : ℝ, 0 < L ∧ 0 < w ∧
      ∀ L' w' : ℝ, L ≤ L' → w ≤ w' →
        Filter.limsup (pureMicroscopicUncovered p hp β Q L' w') atTop ≤ ε := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let rate := β*a^p-cp
  have hcp : 0 < cp := SphericalPureCapCenteringIdentity.pureIntensityConstant_pos p (by omega)
  have hrate : 0 < rate := sub_pos.mpr hEst.depth_rate_positive
  obtain ⟨τ,_,_,hτ,hU,_,_⟩ := physical_diagonal_of_coarse_cover μ β a ep cp hcp hcoarse
  obtain ⟨Cdeep,hCdeep,hDeep⟩ := hEst.deep
  obtain ⟨Cmax,hCmax,hMax⟩ := pure_original_source_maximum_upper p hp h
  intro ε hε
  let t := ε/6
  have ht : 0 < t := by dsimp [t]; positivity
  have hDenSmall := hEst.denominator.eventually (gt_mem_nhds ht)
  have hηpos : ∀ᶠ η : ℝ in 𝓝[>] (0:ℝ), 0 < η := self_mem_nhdsWithin
  obtain ⟨η,hη,hDenη⟩ := (hηpos.and hDenSmall).exists
  have hDenBdd : IsBoundedUnder (· ≤ ·) atTop (pureSourceDenominatorFailure p hp β a η) :=
    isBoundedUnder_of ⟨1,fun _ => measureReal_le_one⟩
  have hDenEventually := eventually_lt_of_limsup_lt hDenη hDenBdd
  have hMaxExp : Tendsto (fun L : ℝ => Cmax*Real.exp (-cp*L)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,Function.comp_def,id_eq] using
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hcp))).const_mul Cmax
  have hDeepExp : Tendsto (fun L : ℝ => Cdeep*Real.exp (-rate*L)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,Function.comp_def,id_eq] using
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hrate))).const_mul Cdeep
  obtain ⟨L,hL,hMaxL,hDeepL⟩ :=
    ((eventually_gt_atTop (0:ℝ)).and
      ((hMaxExp.eventually (gt_mem_nhds ht)).and
        (hDeepExp.eventually (gt_mem_nhds (mul_pos hη ht))))).exists
  have hMaxBdd : IsBoundedUnder (· ≤ ·) atTop (pureSourceMaximumFailure p hp L) :=
    isBoundedUnder_of ⟨1,fun _ => measureReal_le_one⟩
  have hMaxEventually := eventually_lt_of_limsup_lt ((hMax L).trans_lt hMaxL) hMaxBdd
  obtain ⟨Cang,hCang,hAngular⟩ := hEst.angular L hL
  have hGamma : Tendsto (fun w : ℝ => Cang*(1-gaussianWindowFraction κ w))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self,mul_zero] using
      ((tendsto_const_nhds (x := (1:ℝ))).sub
        (gaussianWindowFraction_tendsto_one hEst.curvature_positive)).const_mul Cang
  obtain ⟨w,hw,hAngw⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (hGamma.eventually (gt_mem_nhds (half_pos (mul_pos hη ht))))).exists
  let eAng := η*t/(2*Cang)
  have heAng : 0 < eAng := div_pos (mul_pos hη ht) (by positivity)
  have heAngEq : Cang*eAng=η*t/2 := by
    dsimp [eAng]
    field_simp [hCang.ne']
  have hAngularEventually := hAngular w hw eAng heAng
  have hAll : ∀ᶠ d : ℕ in atTop,
      pureMicroscopicUncovered p hp β Q L w d ≤ ε := by
    filter_upwards [hDeep,hAngularEventually,hEst.mean_eventually_positive,
      hτ.eventually (gt_mem_nhds hEst.deficit_positive),
      hU.eventually (gt_mem_nhds ht),hMaxEventually,hDenEventually,eventually_ge_atTop 1]
      with d hdeep hang hA hτd hUd hMd hDd hd
    let A := pureSourceCapMean p hp β a d
    let l := (d+2:ℕ)*(ep-τ d)
    let D := pureSourceDeepSum p hp β a d l L
    let W := pureSourceAngularSum p hp β Q a d L w
    have hfloor : (d+2:ℕ)*(ep-δ) ≤ l :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hD : D ≤ ENNReal.ofReal (Cdeep*A*Real.exp (-rate*L)) :=
      hdeep L hL.le l hfloor
    have hW : W ≤ ENNReal.ofReal (Cang*A*(1-gaussianWindowFraction κ w+eAng)) := hang
    have hDfin : D ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hD ENNReal.ofReal_lt_top)
    have hWfin : W ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hW ENNReal.ofReal_lt_top)
    have hDmean : (∫⁻ J, originalEnergyMarkedCount d μ β
        (Icc l (pureSourceCenter p hp d-L)) (Ico a 1) J
        ∂disorderLaw (d+2) μ.maxDegree) = D := by
      simp only [D,pureSourceDeepSum,μ,originalEnergyMarkedCount_eq_actualScoreWindowCount]
    have hWmean : (∫⁻ J, originalEnergyMarkedCount d μ β
        (Icc (pureSourceCenter p hp d-L) (pureSourceCenter p hp d+L))
        (Ico a 1 \ Icc (Real.sqrt Q-w/Real.sqrt (d+2:ℕ))
          (Real.sqrt Q+w/Real.sqrt (d+2:ℕ))) J
        ∂disorderLaw (d+2) μ.maxDegree) = W := by
      simp only [W,pureSourceAngularSum,μ,originalEnergyMarkedCount_eq_actualScoreWindowCount]
    have hCompare := original_expected_band_complement_le d hd μ β a ep (τ d)
      (pureSourceCenter p hp d) L (Real.sqrt Q) (w/Real.sqrt (d+2:ℕ)) η A hη hA
      (originalBandComplementMass_integrable d μ β (pureSourceCenter p hp d)
        L (Real.sqrt Q) (w/Real.sqrt (d+2:ℕ)))
      (by rwa [hDmean]) (by rwa [hWmean])
    rw [hDmean,hWmean] at hCompare
    have hTail : 0 ≤ 1-gaussianWindowFraction κ w :=
      sub_nonneg.mpr (gaussianWindowFraction_le_one hEst.curvature_positive)
    have hDr : D.toReal ≤ Cdeep*A*Real.exp (-rate*L) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hD
    have hWr : W.toReal ≤ Cang*A*(1-gaussianWindowFraction κ w+eAng) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hW
    have hDn : D.toReal/A ≤ Cdeep*Real.exp (-rate*L) :=
      (div_le_iff₀ hA).mpr (by nlinarith [hDr])
    have hWn : W.toReal/A ≤ Cang*(1-gaussianWindowFraction κ w+eAng) :=
      (div_le_iff₀ hA).mpr (by nlinarith [hWr])
    have hDnSmall : D.toReal/A < η*t := hDn.trans_lt hDeepL
    have hWnSmall : W.toReal/A < η*t := by
      nlinarith [hWn,hAngw,heAngEq]
    have hQuot : (D.toReal+W.toReal)/(η*A) < 2*t := by
      have heq : (D.toReal+W.toReal)/(η*A) = (D.toReal/A+W.toReal/A)/η := by
        field_simp [hη.ne',hA.ne']
      rw [heq]
      apply (div_lt_iff₀ hη).mpr
      nlinarith
    change pureMicroscopicUncovered p hp β Q L w d ≤
      expectedUncoveredGibbsMass d μ β a ep (τ d)+
        pureSourceMaximumFailure p hp L d+pureSourceDenominatorFailure p hp β a η d+
        (D.toReal+W.toReal)/(η*A) at hCompare
    have hBudget : 5*t < ε := by dsimp [t]; linarith
    linarith
  refine ⟨L,w,hL,hw,?_⟩
  intro L' w' hLL hww
  have hCo : IsCoboundedUnder (· ≤ ·) atTop (pureMicroscopicUncovered p hp β Q L' w') :=
    isCoboundedUnder_le_of_le atTop (pureMicroscopicUncovered_nonneg p hp β Q L' w')
  apply limsup_le_of_le hCo
  filter_upwards [hAll] with d hd
  exact (pureMicroscopicUncovered_antitone p hp β Q hLL hww d).trans hd

/-- A certificate supplies one fixed cap and every analytic estimate before
the coarse-cover input is requested. Only that genuine geometric input
remains in the source microscopic-capture theorem. -/
theorem pure_original_capture_reduction_to_coarse_cover
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    ∃ a κ δ : ℝ, FixedCapEstimates p hp β Q a κ δ ∧
      ((∀ τ : ℝ, 0 < τ → Tendsto
        (fun d => expectedUncoveredGibbsMass d
          (FiniteMixture.pure p (by omega) 1 (by positivity)) β a
          (pureEnergyConstant p (by omega)) τ) atTop (𝓝 (0:ℝ))) →
      ∀ ε : ℝ, 0 < ε → ∃ L w : ℝ, 0 < L ∧ 0 < w ∧
        ∀ L' w' : ℝ, L ≤ L' → w ≤ w' →
          Filter.limsup (pureMicroscopicUncovered p hp β Q L' w') atTop ≤ ε) := by
  obtain ⟨a,κ,δ,hEst⟩ := pure_original_capture_fixed_cap_estimates p hp h
  exact ⟨a,κ,δ,hEst,fun hcoarse =>
    pure_microscopic_capture_of_coarse_cover p hp h hEst hcoarse⟩

/-- Expected uncovered Gibbs mass for a genuinely fixed positive width. -/
def pureFixedBandUncovered (p : ℕ) (hp : 4 ≤ p)
    (β Q L b : ℝ) (d : ℕ) : ℝ :=
  expectedOriginalBandComplementMass d
    (FiniteMixture.pure p (by omega) 1 (by positivity)) β
    (pureSourceCenter p hp d) L (Real.sqrt Q) b

private theorem expected_original_band_complement_le_one
    (d : ℕ) (μ : FiniteMixture) (β m L q b : ℝ) :
    expectedOriginalBandComplementMass d μ β m L q b ≤ 1 := by
  have hh := integral_mono
    (originalBandComplementMass_integrable d μ β m L q b)
    (integrable_const (1:ℝ))
    (fun J => (originalBandComplementMass_mem_unit d μ β m L q b J).2)
  simpa only [expectedOriginalBandComplementMass,integral_const,
    probReal_univ,one_smul] using hh

/-- Source fixed-width capture follows from the proved microscopic result,
for every positive width fixed before the energy-window limit. -/
theorem pure_fixed_band_capture_of_coarse_cover
    (p : ℕ) (hp : 4 ≤ p) {β x Q a κ δ : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hEst : FixedCapEstimates p hp β Q a κ δ)
    (hcoarse : ∀ τ : ℝ, 0 < τ → Tendsto
      (fun d => expectedUncoveredGibbsMass d
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β a
        (pureEnergyConstant p (by omega)) τ) atTop (𝓝 (0:ℝ)))
    (b : ℝ) (hb : 0 < b) :
    Tendsto (fun L : ℝ => Filter.limsup
      (pureFixedBandUncovered p hp β Q L b) atTop) atTop (𝓝 (0:ℝ)) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  have hNonneg (L : ℝ) (d : ℕ) : 0 ≤ pureFixedBandUncovered p hp β Q L b d :=
    expectedOriginalBandComplementMass_nonneg d μ β _ L _ b
  have hBdd (L : ℝ) : IsBoundedUnder (· ≤ ·) atTop
      (pureFixedBandUncovered p hp β Q L b) :=
    isBoundedUnder_of ⟨1,fun d => expected_original_band_complement_le_one d μ β _ L _ b⟩
  have hLimNonneg (L : ℝ) : 0 ≤ Filter.limsup
      (pureFixedBandUncovered p hp β Q L b) atTop := by
    have hh := limsup_le_limsup (.of_forall (hNonneg L))
      (isCoboundedUnder_le_of_le atTop (fun _ : ℕ => le_refl (0:ℝ))) (hBdd L)
    simpa only [limsup_const] using hh
  apply tendsto_order.mpr
  constructor
  · intro z hz
    exact .of_forall fun L => hz.trans_le (hLimNonneg L)
  · intro z hz
    obtain ⟨L,w,hL,hw,hCapture⟩ :=
      pure_microscopic_capture_of_coarse_cover p hp h hEst hcoarse (z/2) (half_pos hz)
    have hWidth : Tendsto (fun d : ℕ => w/Real.sqrt (d+2:ℕ)) atTop (𝓝 (0:ℝ)) := by
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_zero] using
        NatLogWindowScales.inverse_sqrt_dimension_tendsto_zero.const_mul w
    filter_upwards [eventually_ge_atTop L] with L' hLL
    have hCompare : ∀ᶠ d : ℕ in atTop,
        pureFixedBandUncovered p hp β Q L' b d ≤
          pureMicroscopicUncovered p hp β Q L' w d := by
      filter_upwards [hWidth.eventually (gt_mem_nhds hb)] with d hd
      exact expectedOriginalBandComplementMass_antitone d μ β _ _ L' L' _ b
        (le_refl L') hd.le
    have hMicroBdd : IsBoundedUnder (· ≤ ·) atTop
        (pureMicroscopicUncovered p hp β Q L' w) :=
      isBoundedUnder_of ⟨1,fun d => expected_original_band_complement_le_one d μ β _ L' _ _⟩
    have hCompareLim := limsup_le_limsup hCompare
      (isCoboundedUnder_le_of_le atTop (hNonneg L')) hMicroBdd
    exact (hCompareLim.trans (hCapture L' w hLL (le_refl w))).trans_lt (by linarith)

/-- Both pure capture formulations throughout the full superstatic regime,
reduced to the one remaining actual coarse-cover statement. -/
theorem pure_original_capture_above_static_reduction
    (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃ x Q a κ δ : ℝ,
      Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q ∧
      FixedCapEstimates p hp β Q a κ δ ∧
      ((∀ τ : ℝ, 0 < τ → Tendsto
        (fun d => expectedUncoveredGibbsMass d
          (FiniteMixture.pure p (by omega) 1 (by positivity)) β a
          (pureEnergyConstant p (by omega)) τ) atTop (𝓝 (0:ℝ))) →
      (∀ ε : ℝ, 0 < ε → ∃ L w : ℝ, 0 < L ∧ 0 < w ∧
        ∀ L' w' : ℝ, L ≤ L' → w ≤ w' →
          Filter.limsup (pureMicroscopicUncovered p hp β Q L' w') atTop ≤ ε) ∧
      ∀ b : ℝ, 0 < b → Tendsto
        (fun L : ℝ => Filter.limsup (pureFixedBandUncovered p hp β Q L b) atTop)
        atTop (𝓝 (0:ℝ))) := by
  obtain ⟨x,Q,h⟩ := pure_certificate_above_static p hp hβ
  obtain ⟨a,κ,δ,hEst⟩ := pure_original_capture_fixed_cap_estimates p hp h
  exact ⟨x,Q,a,κ,δ,h,hEst,fun hcoarse =>
    ⟨pure_microscopic_capture_of_coarse_cover p hp h hEst hcoarse,
      pure_fixed_band_capture_of_coarse_cover p hp h hEst hcoarse⟩⟩

end SlowEquilibration.SourcePureCaptureFromCoarseCover
