-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapDeepEnergyIntegral
public import SlowEquilibration.SourcePhysicalPairRetainedWindowGeometry
public import SlowEquilibration.SphericalPureCapSourceRatiosFixed

/-! Integrate the literal disconnected outside-window cap mark over a fixed
physical critical-energy window.  The Gaussian angular error is uniform in
the critical value and preserves the dependence of the band on its Hessian. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapAngularErrorIntegral
noncomputable section
open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCertificate PureStationarity
open PairConditionalDeterminantMoments
open SourcePureCapDeepEnergyIntegral SourcePureCapBorelMarkedPhysical
open SourcePureCapBorelMarkedValue SourcePureCapRadialOutsideSourceMean
open SourcePureCapBorelRadialFirst SourcePureLatitudeRadialDisintegration
open SourcePureOriginalIntensityEnvelope
open SphericalPureCapSourceScalars SphericalPureCapSourceRatios
open SphericalPureCapOriginalSourceRatios SphericalPureCapOriginalOutside
open SourceGaussianWindowFraction SourceGaussianLaplaceRatio
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem cap_window_lintegral_constant_bound
    (f : ℝ → ℝ≥0∞) (m L B : ℝ) (_hL : 0 ≤ L) (hB : 0 ≤ B)
    (hf : ∀ H ∈ Icc (m-L) (m+L), f H ≤ ENNReal.ofReal B) :
    (∫⁻ H in Icc (m-L) (m+L), f H) ≤ ENNReal.ofReal (2*L*B) := by
  calc
    _ ≤ ∫⁻ H in Icc (m-L) (m+L), ENNReal.ofReal B := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with H hH
      exact hf H hH
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      rw [show m+L-(m-L)=2*L by ring]
      rw [← ENNReal.ofReal_mul hB]
      congr 1
      ring

/-- Uniform Gaussian cap ratios give an eventual original angular mean
bound; the denominator is positive as a consequence of its own ratio. -/
theorem source_cap_outside_mean_eventually_le
    (p : ℕ) (β ep cp a q κ L w : ℝ)
    (hβ : 0 ≤ β) (ha : a ∈ Icc (0:ℝ) 1) (hL : 0 ≤ L)
    (hκ : 0 < κ)
    (hFull : TendstoUniformlyOn
      (fun n t => sourceCapMean p β ep cp a n t/sourceCapMean p β ep cp a n 0)
      (fun t => Real.exp (β*t*q^p)) atTop (Icc (-L) L))
    (hOutside : TendstoUniformlyOn
      (fun n t => (sourceCapMean p β ep cp a n t-sourceWindowMean p β ep cp q w n t)/
        sourceCapMean p β ep cp a n 0)
      (fun t => Real.exp (β*t*q^p)*(1-gaussianWindowFraction κ w))
      atTop (Icc (-L) L)) (hq : 0 ≤ q) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      0 < sourceCapMean p β ep cp a n 0 ∧
      ∀ t ∈ Icc (-L) L,
        sourceCapMean p β ep cp a n t-sourceWindowMean p β ep cp q w n t ≤
          sourceCapMean p β ep cp a n 0*
            (Real.exp (β*L*q^p)*(1-gaussianWindowFraction κ w)+ε) := by
  have hzero : (0:ℝ) ∈ Icc (-L) L := ⟨by linarith,by linarith⟩
  have hSelf : Tendsto (fun n => sourceCapMean p β ep cp a n 0/
      sourceCapMean p β ep cp a n 0) atTop (𝓝 (1:ℝ)) := by
    simpa only [mul_zero,zero_mul,Real.exp_zero] using hFull.tendsto_at hzero
  have hPos : ∀ᶠ n : ℕ in atTop, 0 < sourceCapMean p β ep cp a n 0 := by
    filter_upwards [hSelf.eventually (eventually_gt_nhds (by norm_num : (1/2:ℝ)<1))]
      with n hn
    have hn0 := source_cap_mean_nonneg p n β ep cp a 0 ha.1 ha.2
    have hne : sourceCapMean p β ep cp a n 0 ≠ 0 := by
      intro heq
      simp only [heq,zero_div] at hn
      norm_num at hn
    exact lt_of_le_of_ne hn0 (Ne.symm hne)
  intro ε hε
  have hUniform := (Metric.tendstoUniformlyOn_iff.mp hOutside) ε hε
  filter_upwards [hPos,hUniform] with n hn hclose
  refine ⟨hn,?_⟩
  intro t ht
  have hdist : |(sourceCapMean p β ep cp a n t-sourceWindowMean p β ep cp q w n t)/
      sourceCapMean p β ep cp a n 0-
      Real.exp (β*t*q^p)*(1-gaussianWindowFraction κ w)| < ε := by
    simpa only [Real.dist_eq,abs_sub_comm] using hclose t ht
  have hExp : Real.exp (β*t*q^p) ≤ Real.exp (β*L*q^p) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht.2 hβ) (pow_nonneg hq _)
  have hTail : 0 ≤ 1-gaussianWindowFraction κ w :=
    sub_nonneg.mpr (gaussianWindowFraction_le_one hκ)
  have hRatio : (sourceCapMean p β ep cp a n t-sourceWindowMean p β ep cp q w n t)/
      sourceCapMean p β ep cp a n 0 ≤
      Real.exp (β*L*q^p)*(1-gaussianWindowFraction κ w)+ε := by
    have hh := (abs_lt.mp hdist).2
    have hLimit := mul_le_mul_of_nonneg_right hExp hTail
    linarith
  simpa only [mul_comm] using (div_le_iff₀ hn).mp hRatio

/-- The original all-critical partition-marked angular sum has the source
Gaussian tail bound.  The scalar Laplace hypotheses are discharged jointly
with the deep-energy bound by the fixed-cap assembly theorem. -/
theorem pure_original_angular_error_cap_sum
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {a δ g Z κ : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (haq : a < Real.sqrt Q)
    (hsub : pureResidualCoefficient p β a < 1/2)
    (hδ : 0 < δ) (hg : 0 < g) (hκ : 0 < κ)
    (hLeft : 2*Real.sqrt ((FiniteMixture.pure p (by omega) 1 (by positivity)).xi2 1)+g ≤
      (p:ℝ)*(pureEnergyConstant p (by omega)-δ))
    (hRight : (p:ℝ)*(pureEnergyConstant p (by omega)+δ) ≤ Z)
    (u : ∀ d : ℕ, Vector (d+2)) (hu : ∀ d : ℕ, ‖u d‖^2=(d+2:ℕ))
    (L : ℝ) (hL : 0 < L)
    (hRatios : ∀ w : ℝ, 0 < w →
      TendstoUniformlyOn
        (fun n t => sourceCapMean p β (pureEnergyConstant p (by omega))
          (pureIntensityConstant p (by omega)) a n t /
          sourceCapMean p β (pureEnergyConstant p (by omega))
            (pureIntensityConstant p (by omega)) a n 0)
        (fun t => Real.exp (β*t*(Real.sqrt Q)^p)) atTop (Icc (-L) L) ∧
      TendstoUniformlyOn
        (fun n t => (sourceCapMean p β (pureEnergyConstant p (by omega))
          (pureIntensityConstant p (by omega)) a n t-
          sourceWindowMean p β (pureEnergyConstant p (by omega))
            (pureIntensityConstant p (by omega)) (Real.sqrt Q) w n t) /
          sourceCapMean p β (pureEnergyConstant p (by omega))
            (pureIntensityConstant p (by omega)) a n 0)
        (fun t => Real.exp (β*t*(Real.sqrt Q)^p)*(1-gaussianWindowFraction κ w))
        atTop (Icc (-L) L)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let ep := pureEnergyConstant p (by omega)
    let cp := pureIntensityConstant p (by omega)
    let m d := (d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp)
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 < w → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ d : ℕ in atTop,
        (∫⁻ J, actualScoreWindowCount (d+1)
          (centerCoefficients (mixtureCoefficients μ) 1)
          (physicalEnergyWindow (d+2) (Icc (m d-L) (m d+L)) univ)
          (originalBorelBandMark d μ β
            (Ico a 1 \ Icc (Real.sqrt Q-w/Real.sqrt (d+2:ℕ))
              (Real.sqrt Q+w/Real.sqrt (d+2:ℕ)))) J
          ∂disorderLaw (d+2) μ.maxDegree) ≤
        ENNReal.ofReal (C*sourceCapMean p β ep cp a d 0*
          (1-gaussianWindowFraction κ w+ε)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let m (d : ℕ) : ℝ := (d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp)
  have hcp : 0 < cp := SphericalPureCapCenteringIdentity.pureIntensityConstant_pos p (by omega)
  have hcenter : ∀ᶠ d : ℕ in atTop,
      |m d-((d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp))| ≤ (0:ℝ) :=
    .of_forall fun d => by simp only [m,sub_self,abs_zero,le_refl]
  obtain ⟨Cmark,hCmark,hMark⟩ :=
    pure_original_borel_band_marked_physical_bound p (by omega) β ha hsub hg
  obtain ⟨Cenv,hCenv,hEnv⟩ :=
    pure_original_criticalPhysicalIntensity_centered_envelope p hp h hδ hg
      hLeft hRight m (M := 0) (by norm_num) hcenter
  let B := Real.exp (β*L*(Real.sqrt Q)^p)
  let C := 2*L*Cenv*Real.exp (cp*L)*Cmark*B
  have hB : 0 < B := Real.exp_pos _
  have hB1 : 1 ≤ B := Real.one_le_exp_iff.mpr
    (mul_nonneg (mul_nonneg h.beta_pos.le hL.le)
      (pow_nonneg (Real.sqrt_nonneg Q) _))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro w hw ε hε
  obtain ⟨hFull,hOutside⟩ := hRatios w hw
  have hMeans := source_cap_outside_mean_eventually_le p β ep cp a (Real.sqrt Q)
    κ L w h.beta_pos.le ⟨ha.1.le,ha.2.le⟩ hL.le hκ hFull hOutside
    (Real.sqrt_nonneg Q) ε hε
  have hOffsets := source_logarithmic_center_offset_bounds hcp (le_refl (0:ℝ))
    hδ m hcenter (-L) L
  have hInterior := original_source_window_eventually_interior
    h.overlap_range.1 h.overlap_range.2 hw.le
  have hInside := original_source_window_eventually_inside_cap
    h.overlap_range.1 h.overlap_range.2 haq hw.le
  filter_upwards [hMark,hEnv,hMeans,hOffsets,hInterior,hInside] with
    d hmark henv hmean hoff hint hins
  let N : ℝ := (d+2:ℕ)
  let A := sourceCapMean p β ep cp a d 0
  let T := 1-gaussianWindowFraction κ w
  let I := Ico a 1 \ Icc (Real.sqrt Q-w/Real.sqrt (d+2:ℕ))
    (Real.sqrt Q+w/Real.sqrt (d+2:ℕ))
  let W := Icc (m d-L) (m d+L)
  have hN : 0 < N := by dsimp [N]; positivity
  have hA : 0 < A := hmean.1
  have hT : 0 ≤ T := sub_nonneg.mpr (gaussianWindowFraction_le_one hκ)
  have hBox (H : ℝ) (hH : H ∈ W) : H ∈ Icc (N*(ep-δ)) (N*(ep+δ)) :=
    ⟨by linarith [hoff.1,hH.1],hH.2.trans hoff.2⟩
  have hEdge (H : ℝ) (hH : H ∈ W) :
      2*Real.sqrt (μ.xi2 1)+g ≤ (p:ℝ)*(H/(d+2:ℕ)) := by
    have hlow : ep-δ ≤ H/N := (le_div_iff₀ hN).mpr (by
      simpa only [mul_comm] using (hBox H hH).1)
    exact hLeft.trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  have hKR := hmark W measurableSet_Icc hEdge I
    (measurableSet_Ico.diff measurableSet_Icc) sdiff_subset
  have hMean (H : ℝ) (hH : H ∈ W) :
      (∫⁻ s : Ioi (0:ℝ), radialMeanWeight (d+1) p β H I s ∂radialLaw (d+1)) ≤
        ENNReal.ofReal (A*B*(T+ε)) := by
    have ht : H-m d ∈ Icc (-L) L := ⟨by linarith [hH.1],by linarith [hH.2]⟩
    have hrad := pure_original_radial_outside_mean_eq_source d p hint.1 hp
      β ep cp a (Real.sqrt Q) w (H-m d) ha.1 ha.2 hint.2.1 hint.2.2
      hw.le hins.2 (u d) (hu d)
    have hEnergy : (d+2:ℕ)*ep+(H-m d)-Real.log (d+2:ℕ)/(2*cp)=H := by
      dsimp [m]
      ring
    rw [hEnergy] at hrad
    rw [hrad]
    apply ENNReal.ofReal_le_ofReal
    have hh := hmean.2 (H-m d) ht
    have hεB : ε ≤ B*ε := by nlinarith [hB1,hε]
    calc
      _ ≤ A*(B*T+ε) := hh
      _ ≤ A*(B*T+B*ε) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl (B*T)) hεB) hA.le
      _ = A*B*(T+ε) := by ring
  have hTail := cap_window_lintegral_constant_bound
    (fun H => pureCriticalPhysicalIntensity d p (by omega) 1 (by positivity) 1 H *
      (ENNReal.ofReal Cmark*
        ∫⁻ s : Ioi (0:ℝ), radialMeanWeight (d+1) p β H I s ∂radialLaw (d+1)))
    (m d) L (Cenv*Real.exp (cp*L)*Cmark*(A*B*(T+ε))) hL.le (by positivity) (by
      intro H hH
      have hDensReal := henv H (hBox H hH)
      have hExponent : cp*(m d-H) ≤ cp*L := by nlinarith [hH.1,hcp]
      have hDens : pureCriticalPhysicalIntensity d p (by omega) 1 (by positivity) 1 H ≤
          ENNReal.ofReal (Cenv*Real.exp (cp*L)) := by
        rw [← ENNReal.ofReal_toReal
          (pureCriticalPhysicalIntensity_ne_top d p (by omega) 1 (by positivity) 1 H)]
        apply ENNReal.ofReal_le_ofReal
        exact hDensReal.trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hExponent) hCenv.le)
      calc
        _ ≤ ENNReal.ofReal (Cenv*Real.exp (cp*L))*
            (ENNReal.ofReal Cmark*ENNReal.ofReal (A*B*(T+ε))) :=
          mul_le_mul' hDens (mul_le_mul_right (hMean H hH) _)
        _ = _ := by
          rw [← ENNReal.ofReal_mul hCmark.le,
            ← ENNReal.ofReal_mul (mul_nonneg hCenv.le (Real.exp_pos _).le)]
          congr 1
          ring)
  have hFinal : 2*L*(Cenv*Real.exp (cp*L)*Cmark*(A*B*(T+ε))) = C*A*(T+ε) := by
    dsimp [C]
    ring
  exact hKR.trans (hTail.trans_eq (congrArg ENNReal.ofReal hFinal))

end
end SlowEquilibration.SourcePureCapAngularErrorIntegral
