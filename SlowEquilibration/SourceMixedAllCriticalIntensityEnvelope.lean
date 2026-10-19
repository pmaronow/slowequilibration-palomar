-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalEnergyPalmIntensity
public import SlowEquilibration.SphericalOnePointEnergyTilt
public import SlowEquilibration.SphericalMaximumFirstMoments
public import SlowEquilibration.SphericalTAPCriticalFewLightBands

/-! The all-critical physical energy density has an exact midpoint score
tilt. Its source upper-score bound and a centered expected-count bound give
the manuscript's exponential lower-energy envelope. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedAllCriticalIntensityEnvelope

open Set MeasureTheory
open SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.SphericalTAPCriticalEnergyPalmAverage
open SlowEquilibration.SphericalTAPCriticalEnergyPalmIntensity
open SlowEquilibration.GOEPhysicalPotential
open SlowEquilibration.SphericalSequentialRegression
open SlowEquilibration.ENNRadialIntegralBridge
open SlowEquilibration.SphericalTAPCriticalFewLightBands
open SlowEquilibration.TwoAtomStationarity
open Filter
open scoped Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

def sourceAllCriticalPhysicalEnergyDensity
    (d : ℕ) (μ : FiniteMixture) (Q L R H : ℝ) : ℝ :=
  sourcePhysicalRadialFactor d μ Q *
    ∫ k in Ioo L R,
      sourceAllCriticalRadialWeight d μ Q (H/(d+2 : ℕ)) k

theorem sourceAllCriticalPhysicalEnergyDensity_eq_actual
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (L R H : ℝ) :
    sourceAllCriticalPhysicalEnergyDensity d μ Q L R H =
      ∫ k in Ioo L R,
        (mixedCriticalPhysicalIntensity d μ Q H k).toReal := by
  unfold sourceAllCriticalPhysicalEnergyDensity
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ (fun k => ?_)
  have hN : ((d+2:ℕ):ℝ) ≠ 0 := by positivity
  have h := mixedCriticalPhysicalIntensity_eq_sourceAllCriticalRadialWeight
    d μ hQ hnp (H/(d+2 : ℕ)) k
  simpa only [mul_div_cancel₀ _ hN] using h.symm

theorem mixedCriticalPhysicalIntensity_measurable_pair
    (d : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measurable (fun p : ℝ × ℝ => mixedCriticalPhysicalIntensity d μ Q p.1 p.2) := by
  have hCrit : Measurable (mixedCriticalIntensity d μ Q) := by
    exact (measurable_const.mul (physicalScorePdf_measurable (d+2) μ Q)).mul
      (((physicalMean_measurable d (d+2) (Q^2*μ.xi2 Q)).comp
        ((EuclideanSpace.proj (1 : Fin 2)).continuous.measurable)).ennreal_ofReal)
  have hp : Measurable (fun p : ℝ × ℝ => scorePairEquiv (p.1/(d+2 : ℕ),p.2)) := by
    fun_prop
  simpa only [mixedCriticalPhysicalIntensity, Function.comp_def, Pi.mul_def,
    scorePairEquiv_apply] using measurable_const.mul (hCrit.comp hp)

theorem mixedCriticalPhysicalIntensity_ne_top
    (d : ℕ) (μ : FiniteMixture) (Q H k : ℝ) :
    mixedCriticalPhysicalIntensity d μ Q H k ≠ ⊤ := by
  have hp := sphereKRPrefactor_ne_top (d+1) μ Q
  unfold mixedCriticalPhysicalIntensity mixedCriticalIntensity physicalScorePdf
  finiteness

theorem sourceCriticalWindowMean_eq_allcritical_energy_integral
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    {L R : ℝ} (hLR : L < R) (a b : ℝ) :
    sourceCriticalWindowMean d μ Q (Ioo L R) a b =
      ∫ H in Icc a b, sourceAllCriticalPhysicalEnergyDensity d μ Q L R H := by
  have hi (H : ℝ) : IntegrableOn
      (fun k => (mixedCriticalPhysicalIntensity d μ Q H k).toReal) (Ioo L R) := by
    have hW := sourceAllCriticalRadialWeight_integrableOn_Ioo d μ hQ
      (H/(d+2 : ℕ)) hLR
    have hF := hW.const_mul (sourcePhysicalRadialFactor d μ Q)
    exact hF.congr (ae_of_all _ (fun k => by
      have h := mixedCriticalPhysicalIntensity_eq_sourceAllCriticalRadialWeight
        d μ hQ hnp (H/(d+2 : ℕ)) k
      have hN : ((d+2:ℕ):ℝ) ≠ 0 := by positivity
      have hE : ((d+2:ℕ):ℝ)*(H/(d+2 : ℕ)) = H := by
        field_simp
      rw [hE] at h
      exact h.symm))
  unfold sourceCriticalWindowMean
  rw [sourceCriticalWindowMass_def]
  rw [actual_mixed_critical_physical_intensity d μ hQ hnp
    (Icc a b) (Ioo L R) measurableSet_Icc measurableSet_Ioo]
  rw [iterated_toReal_eq (mixedCriticalPhysicalIntensity d μ Q)
    (Ioo L R) (Icc a b)
    (mixedCriticalPhysicalIntensity_measurable_pair d μ Q)
    (mixedCriticalPhysicalIntensity_ne_top d μ Q) hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun H =>
    (sourceAllCriticalPhysicalEnergyDensity_eq_actual d μ hQ hnp L R H).symm)

theorem sourceAllCriticalPhysicalEnergyDensity_integrableOn
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    {L R : ℝ} (hLR : L < R) (a b : ℝ) :
    IntegrableOn (sourceAllCriticalPhysicalEnergyDensity d μ Q L R) (Icc a b) := by
  let F := mixedCriticalPhysicalIntensity d μ Q
  let G : ℝ → ℝ≥0∞ := fun H => ∫⁻ k in Ioo L R, F H k
  have hFmeas : Measurable (fun p : ℝ × ℝ => F p.1 p.2) :=
    mixedCriticalPhysicalIntensity_measurable_pair d μ Q
  have hGmeas : Measurable G :=
    hFmeas.lintegral_prod_right' (ν := volume.restrict (Ioo L R))
  have hi (H : ℝ) : IntegrableOn (fun k => (F H k).toReal) (Ioo L R) := by
    have hW := sourceAllCriticalRadialWeight_integrableOn_Ioo d μ hQ
      (H/(d+2 : ℕ)) hLR
    have hF := hW.const_mul (sourcePhysicalRadialFactor d μ Q)
    exact hF.congr (ae_of_all _ (fun k => by
      have h := mixedCriticalPhysicalIntensity_eq_sourceAllCriticalRadialWeight
        d μ hQ hnp (H/(d+2 : ℕ)) k
      have hN : ((d+2:ℕ):ℝ) ≠ 0 := by positivity
      have hE : ((d+2:ℕ):ℝ)*(H/(d+2 : ℕ)) = H := by field_simp
      rw [hE] at h
      exact h.symm))
  have hGfinite (H : ℝ) : G H ≠ ⊤ := by
    apply (integrable_toReal_iff
      ((hFmeas.comp (by fun_prop : Measurable (fun k : ℝ => (H,k)))).aemeasurable)
      (ae_of_all _ (fun k => mixedCriticalPhysicalIntensity_ne_top d μ Q H k))).mp
    exact hi H
  have hKR : sourceCriticalWindowMass d μ Q (Ioo L R) a b =
      ∫⁻ H in Icc a b, G H := by
    rw [sourceCriticalWindowMass_def]
    exact actual_mixed_critical_physical_intensity d μ hQ hnp
      (Icc a b) (Ioo L R) measurableSet_Icc measurableSet_Ioo
  have hOuter : (∫⁻ H in Icc a b, G H) ≠ ⊤ := by
    rw [←hKR]
    exact (sourceCriticalWindowMass_finite d μ hQ (Ioo L R) a b).ne
  have hIntegrable : IntegrableOn (fun H => (G H).toReal) (Icc a b) :=
    (integrable_toReal_iff hGmeas.aemeasurable
      (ae_of_all _ (fun H => hGfinite H))).mpr hOuter
  apply hIntegrable.congr
  exact ae_of_all _ (fun H => by
    calc
      (G H).toReal = ∫ k in Ioo L R, (F H k).toReal :=
        (integral_toReal (μ := volume.restrict (Ioo L R))
          ((hFmeas.comp (by fun_prop : Measurable (fun k : ℝ => (H,k)))).aemeasurable)
          (ae_of_all _ (fun k => lt_top_iff_ne_top.mpr
            (mixedCriticalPhysicalIntensity_ne_top d μ Q H k)))).symm
      _ = sourceAllCriticalPhysicalEnergyDensity d μ Q L R H :=
        (sourceAllCriticalPhysicalEnergyDensity_eq_actual d μ hQ hnp L R H).symm)

theorem sourceAllCriticalRadialWeight_midpoint_tilt
    (d : ℕ) (μ : FiniteMixture) (Q H t k : ℝ) :
    sourceAllCriticalRadialWeight d μ Q ((H+t)/(d+2 : ℕ)) k =
      sourceAllCriticalRadialWeight d μ Q (H/(d+2 : ℕ)) k *
        Real.exp (-sourceEnergySlope μ Q ((H+t/2)/(d+2 : ℕ)) k*t) := by
  have hN : ((d+2:ℕ):ℝ) ≠ 0 := by positivity
  have he : (H+t)/(d+2 : ℕ) = H/(d+2 : ℕ)+t/(d+2 : ℕ) := by ring
  rw [he]
  unfold sourceAllCriticalRadialWeight
  rw [source_scoreQuadratic_energy_expansion]
  have hs : sourceEnergySlope μ Q ((H+t/2)/(d+2 : ℕ)) k =
      sourceEnergySlope μ Q (H/(d+2 : ℕ)) k+
        sourceEnergyCurvature μ Q*t/(2*(d+2 : ℕ)) := by
    unfold sourceEnergySlope
    field_simp
    ring
  rw [hs]
  have hExp : -((d+2:ℕ):ℝ) *
      (scoreQuadratic μ Q (scorePairEquiv (H/(d+2 : ℕ),k)) +
        2*sourceEnergySlope μ Q (H/(d+2 : ℕ)) k*(t/(d+2 : ℕ))+
        sourceEnergyCurvature μ Q*(t/(d+2 : ℕ))^2) / 2 =
      -((d+2:ℕ):ℝ) *
        scoreQuadratic μ Q (scorePairEquiv (H/(d+2 : ℕ),k)) / 2+
      -(sourceEnergySlope μ Q (H/(d+2 : ℕ)) k+
        sourceEnergyCurvature μ Q*t/(2*(d+2 : ℕ)))*t := by
    field_simp
    ring
  rw [hExp, Real.exp_add]
  ring

theorem sourceAllCriticalRadialWeight_below_bound
    (d : ℕ) (μ : FiniteMixture) (Q : ℝ)
    {E m c : ℝ} (hE : E ≤ m) (k : ℝ)
    (hs : sourceEnergySlope μ Q ((E+m)/2/(d+2 : ℕ)) k ≤ c) :
    sourceAllCriticalRadialWeight d μ Q (E/(d+2 : ℕ)) k ≤
      sourceAllCriticalRadialWeight d μ Q (m/(d+2 : ℕ)) k *
        Real.exp (c*(m-E)) := by
  have ht := sourceAllCriticalRadialWeight_midpoint_tilt d μ Q m (E-m) k
  have he : m+(E-m)=E := by ring
  have hm : (m+(E-m)/2)/(d+2 : ℕ)=(E+m)/2/(d+2 : ℕ) := by ring
  rw [he,hm] at ht
  rw [ht]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (sourceAllCriticalRadialWeight_nonneg d μ Q (m/(d+2 : ℕ)) k)
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hE)]

theorem sourceAllCriticalRadialWeight_above_bound
    (d : ℕ) (μ : FiniteMixture) (Q : ℝ)
    {m v c : ℝ} (hv : 0 ≤ v) (k : ℝ)
    (hs : sourceEnergySlope μ Q ((m+v/2)/(d+2 : ℕ)) k ≤ c) :
    sourceAllCriticalRadialWeight d μ Q (m/(d+2 : ℕ)) k *
        Real.exp (-c*v) ≤
      sourceAllCriticalRadialWeight d μ Q ((m+v)/(d+2 : ℕ)) k := by
  rw [sourceAllCriticalRadialWeight_midpoint_tilt]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (sourceAllCriticalRadialWeight_nonneg d μ Q (m/(d+2 : ℕ)) k)
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hv]

theorem sourceAllCriticalPhysicalEnergyDensity_nonneg
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (L R H : ℝ) :
    0 ≤ sourceAllCriticalPhysicalEnergyDensity d μ Q L R H := by
  unfold sourceAllCriticalPhysicalEnergyDensity
  exact mul_nonneg (sourcePhysicalRadialFactor_pos d μ hQ hnp).le
    (integral_nonneg (fun k => sourceAllCriticalRadialWeight_nonneg d μ Q _ k))

theorem sourceAllCriticalPhysicalEnergyDensity_below_bound
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    {L R E m c : ℝ} (hLR : L < R) (hE : E ≤ m)
    (hs : ∀ k ∈ Ioo L R,
      sourceEnergySlope μ Q ((E+m)/2/(d+2 : ℕ)) k ≤ c) :
    sourceAllCriticalPhysicalEnergyDensity d μ Q L R E ≤
      sourceAllCriticalPhysicalEnergyDensity d μ Q L R m *
        Real.exp (c*(m-E)) := by
  have hF := (sourcePhysicalRadialFactor_pos d μ hQ hnp).le
  have hWE := sourceAllCriticalRadialWeight_integrableOn_Ioo d μ hQ
    (E/(d+2 : ℕ)) hLR
  have hWM := sourceAllCriticalRadialWeight_integrableOn_Ioo d μ hQ
    (m/(d+2 : ℕ)) hLR
  have hInt :
      (∫ k in Ioo L R, sourceAllCriticalRadialWeight d μ Q (E/(d+2 : ℕ)) k) ≤
      (∫ k in Ioo L R, sourceAllCriticalRadialWeight d μ Q (m/(d+2 : ℕ)) k) *
        Real.exp (c*(m-E)) := by
    rw [← integral_mul_const]
    exact setIntegral_mono_on hWE (hWM.mul_const _) measurableSet_Ioo
      (fun k hk => sourceAllCriticalRadialWeight_below_bound d μ Q hE k (hs k hk))
  unfold sourceAllCriticalPhysicalEnergyDensity
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hInt hF

theorem sourceAllCriticalPhysicalEnergyDensity_above_bound
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    {L R m v c : ℝ} (hLR : L < R) (hv : 0 ≤ v)
    (hs : ∀ k ∈ Ioo L R,
      sourceEnergySlope μ Q ((m+v/2)/(d+2 : ℕ)) k ≤ c) :
    sourceAllCriticalPhysicalEnergyDensity d μ Q L R m *
        Real.exp (-c*v) ≤
      sourceAllCriticalPhysicalEnergyDensity d μ Q L R (m+v) := by
  have hF := (sourcePhysicalRadialFactor_pos d μ hQ hnp).le
  have hWM := sourceAllCriticalRadialWeight_integrableOn_Ioo d μ hQ
    (m/(d+2 : ℕ)) hLR
  have hWV := sourceAllCriticalRadialWeight_integrableOn_Ioo d μ hQ
    ((m+v)/(d+2 : ℕ)) hLR
  have hInt :
      (∫ k in Ioo L R, sourceAllCriticalRadialWeight d μ Q (m/(d+2 : ℕ)) k) *
        Real.exp (-c*v) ≤
      (∫ k in Ioo L R, sourceAllCriticalRadialWeight d μ Q ((m+v)/(d+2 : ℕ)) k) := by
    rw [← integral_mul_const]
    exact setIntegral_mono_on (hWM.mul_const _) hWV measurableSet_Ioo
      (fun k hk => sourceAllCriticalRadialWeight_above_bound d μ Q hv k (hs k hk))
  unfold sourceAllCriticalPhysicalEnergyDensity
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hInt hF

/-- Source Lemma 12.16 for the literal all-critical physical Kac--Rice
intensity. The named centered-strip count premise is precisely the first
claim of source Lemma 12.2, inherited there from source Theorem 11.14. -/
theorem source_mixed_allcritical_intensity_envelope
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    {L R l m cPlus Ccount : ℝ}
    (hLR : L < R) (hlm : l ≤ m) (hc : 0 ≤ cPlus)
    (hScore : ∀ H ∈ Icc l (m+1), ∀ k ∈ Ioo L R,
      sourceEnergySlope μ Q (H/(d+2 : ℕ)) k ≤ cPlus)
    (hCenteredCountIntegrable : IntegrableOn
      (sourceAllCriticalPhysicalEnergyDensity d μ Q L R) (Icc m (m+1)))
    (hCenteredCount :
      (∫ H in Icc m (m+1),
        sourceAllCriticalPhysicalEnergyDensity d μ Q L R H) ≤ Ccount) :
    ∀ u ∈ Icc (0 : ℝ) (m-l),
      sourceAllCriticalPhysicalEnergyDensity d μ Q L R (m-u) ≤
        (Ccount*Real.exp cPlus)*Real.exp (cPlus*u) := by
  let f := sourceAllCriticalPhysicalEnergyDensity d μ Q L R
  have hfm : 0 ≤ f m :=
    sourceAllCriticalPhysicalEnergyDensity_nonneg d μ hQ hnp L R m
  have hPoint (H : ℝ) (hH : H ∈ Icc m (m+1)) :
      f m*Real.exp (-cPlus) ≤ f H := by
    let v := H-m
    have hv : v ∈ Icc (0 : ℝ) 1 := by dsimp [v]; constructor <;> linarith [hH.1,hH.2]
    have hMid : m+v/2 ∈ Icc l (m+1) := by
      constructor <;> dsimp [v] <;> linarith [hv.1,hv.2]
    have hAbove := sourceAllCriticalPhysicalEnergyDensity_above_bound
      d μ hQ hnp hLR hv.1 (fun k hk => hScore (m+v/2) hMid k hk)
    have hExp : Real.exp (-cPlus) ≤ Real.exp (-cPlus*v) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc (sub_nonneg.mpr hv.2)])
    have hEval : m+v=H := by dsimp [v]; ring
    rw [hEval] at hAbove
    exact (mul_le_mul_of_nonneg_left hExp hfm).trans hAbove
  have hConst : IntegrableOn (fun _ : ℝ => f m*Real.exp (-cPlus))
      (Icc m (m+1)) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hCenterLower : f m*Real.exp (-cPlus) ≤
      ∫ H in Icc m (m+1), f H := by
    have hh := setIntegral_mono_on hConst hCenteredCountIntegrable
      measurableSet_Icc hPoint
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : m ≤ m+1)] at hh
    simpa only [add_sub_cancel_left, one_smul] using hh
  have hfmBound : f m ≤ Ccount*Real.exp cPlus := by
    have hh := hCenterLower.trans hCenteredCount
    calc
      f m = Real.exp cPlus*(f m*Real.exp (-cPlus)) := by
        rw [show Real.exp cPlus*(f m*Real.exp (-cPlus)) =
          f m*(Real.exp cPlus*Real.exp (-cPlus)) by ring,
          ←Real.exp_add]
        simp
      _ ≤ Real.exp cPlus*Ccount := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      _ = Ccount*Real.exp cPlus := mul_comm _ _
  intro u hu
  have hE : m-u ≤ m := by linarith [hu.1]
  have hMid : (m-u+m)/2 ∈ Icc l (m+1) := by
    constructor <;> linarith [hu.1, hu.2]
  have hBelow := sourceAllCriticalPhysicalEnergyDensity_below_bound
    d μ hQ hnp hLR hE (fun k hk => hScore ((m-u+m)/2) hMid k hk)
  have hGap : m-(m-u)=u := by ring
  rw [hGap] at hBelow
  exact hBelow.trans (mul_le_mul_of_nonneg_right hfmBound (Real.exp_pos _).le)

/-- The actual first-moment conclusion supplies the centered count premise;
the certificate score band supplies the exponent. No additional count or
intensity assumption remains. -/
theorem source_mixed_allcritical_intensity_envelope_from_firstMoments
    (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hLR : L < R) (hδ : 0 < δ)
    (hBand : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      ∀ k ∈ Icc L R,
      β*x/2 ≤ sourceEnergySlope μ Q e k ∧
        sourceEnergySlope μ Q e k ≤ (β*x+β)/2)
    (data : SourceMaximumFirstMomentConclusions μ β x Q L R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ u ∈ Icc (0 : ℝ)
        (data.center d-((d+2:ℕ):ℝ)*(markE μ β x Q-δ)),
      sourceAllCriticalPhysicalEnergyDensity d μ Q L R (data.center d-u) ≤
        C*Real.exp (((β*x+β)/2)*u) := by
  obtain ⟨Ccount,hCcount,hCount⟩ := data.uniform_window_bound 0 1 (by norm_num)
  let cPlus := (β*x+β)/2
  have hcPlus : 0 ≤ cPlus := by
    dsimp [cPlus]
    have hβ : 0 < β := h.beta_pos
    have hx : 0 < x := h.weight_range.1
    positivity
  refine ⟨Ccount*Real.exp cPlus, mul_pos hCcount (Real.exp_pos _), ?_⟩
  have hWindow := centered_physical_window_eventually_in_normalized_interval
    μ h data hδ 1
  filter_upwards [hWindow] with d hd
  let N : ℝ := (d+2:ℕ)
  let m := data.center d
  let e₀ := markE μ β x Q
  have hN : 0 < N := by dsimp [N]; positivity
  have hRangeLo : e₀-δ ≤ (m-1)/N := by
    have hh := hd (a := (m-1)/N) (by
      change N*((m-1)/N) ∈ Icc (m-1) (m+1)
      rw [mul_div_cancel₀ _ hN.ne']
      constructor <;> linarith)
    exact hh.1
  have hRangeHi : (m+1)/N ≤ e₀+δ := by
    have hh := hd (a := (m+1)/N) (by
      change N*((m+1)/N) ∈ Icc (m-1) (m+1)
      rw [mul_div_cancel₀ _ hN.ne']
      constructor <;> linarith)
    exact hh.2
  have hlm : N*(e₀-δ) ≤ m := by
    have hh := (le_div_iff₀ hN).mp hRangeLo
    nlinarith
  have hScore (H : ℝ) (hH : H ∈ Icc (N*(e₀-δ)) (m+1))
      (k : ℝ) (hk : k ∈ Ioo L R) :
      sourceEnergySlope μ Q (H/(d+2 : ℕ)) k ≤ cPlus := by
    have hELo : e₀-δ ≤ H/N :=
      (le_div_iff₀ hN).mpr (by nlinarith [hH.1])
    have hEHi : H/N ≤ e₀+δ := by
      apply (div_le_iff₀ hN).mpr
      nlinarith [(div_le_iff₀ hN).mp hRangeHi, hH.2]
    exact (hBand (H/N) ⟨hELo,hEHi⟩ k ⟨hk.1.le,hk.2.le⟩).2
  have hInt := sourceAllCriticalPhysicalEnergyDensity_integrableOn
    d μ h.overlap_range.1 hnp hLR m (m+1)
  have hCountD :
      (∫ H in Icc m (m+1),
        sourceAllCriticalPhysicalEnergyDensity d μ Q L R H) ≤ Ccount := by
    rw [←sourceCriticalWindowMean_eq_allcritical_energy_integral
      d μ h.overlap_range.1 hnp hLR m (m+1)]
    simpa [m] using (hCount d).2
  exact source_mixed_allcritical_intensity_envelope d μ
    h.overlap_range.1 hnp hLR hlm hcPlus hScore hInt hCountD

/-- Source Lemma 12.16, using the already proved original-field
first-moment theorem to construct the logarithmically corrected center and
bound the true all-critical count in a fixed energy strip. -/
theorem source_mixed_allcritical_intensity_envelope_of_certificate
    (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L)
    (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hBand : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      ∀ k ∈ Icc L R,
      β*x/2 ≤ sourceEnergySlope μ Q e k ∧
        sourceEnergySlope μ Q e k ≤ (β*x+β)/2) :
    ∃ data : SourceMaximumFirstMomentConclusions μ β x Q L R,
      ∃ C : ℝ, 0 < C ∧ (β*x+β)/2 < β ∧
        ∀ᶠ d : ℕ in atTop,
          ∀ u ∈ Icc (0 : ℝ)
            (data.center d-((d+2:ℕ):ℝ)*(markE μ β x Q-δ)),
          sourceAllCriticalPhysicalEnergyDensity d μ Q L R (data.center d-u) ≤
            C*Real.exp (((β*x+β)/2)*u) := by
  obtain ⟨data⟩ := sourceMaximum_first_moments μ h hnp hL hm hδ hBand
  obtain ⟨C,hC,hEnv⟩ :=
    source_mixed_allcritical_intensity_envelope_from_firstMoments
      μ h hnp (lt_trans hm.1 hm.2) hδ hBand data
  exact ⟨data, C, hC, data.lower_density_rate_lt_beta, hEnv⟩

end SlowEquilibration.SourceMixedAllCriticalIntensityEnvelope
