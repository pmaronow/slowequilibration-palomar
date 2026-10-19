-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedNegativeComplexityCounts
public import SlowEquilibration.SphericalMaximumFirstMoments
public import Mathlib.Topology.Order.LiminfLimsup

/-! Actual high-probability global-maximum localization and the centered
global-maximum probability tail under the original disorder law. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel SphericalGaussianJet SphericalForm
open SphericalLatitudeChartKacRice SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped ENNReal Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem sourceHighExcludedCountMass_finite (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (h0 : ℝ) (U : Set ℝ) : sourceHighExcludedCountMass n μ Q h0 U < ⊤ := by
  rw [sourceHighExcludedCountMass_def]
  exact bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ _ _ 1 (by simp)
    (fun _ _ => le_rfl)

/-- The explicit original-disorder Borel set controls every global
maximizer above the stated energy, in every dimension. -/
theorem sourceHighCriticalGoodSet_localizes_maxima (n : ℕ) (μ : FiniteMixture)
    (Q h0 : ℝ) (U : Set ℝ) {J : Disorder (n+2) μ.maxDegree}
    (hJ : J ∈ sourceHighCriticalGoodSet n μ Q h0 U) {y : Vector (n+2)}
    (hy : ‖y‖^2=(n+2 : ℕ))
    (hmax : IsMaxOn (field (centerCoefficients (mixtureCoefficients μ) Q) J)
      {z : Vector (n+2) | ‖z‖^2=(n+2 : ℕ)} y)
    (hhigh : (n+2 : ℕ)*h0 ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J y) :
    IsLocalMaxOn (field (centerCoefficients (mixtureCoefficients μ) Q) J)
      {z : Vector (n+2) | ‖z‖^2=(n+2 : ℕ)} y ∧
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J y 1 ∈ U := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hcrit : surfaceGradient (field c J) y=0 := by
    apply surfaceGradient_eq_zero_of_sphere_maximum (by omega) (field c J) y
      ((onSphere_iff_norm_sq y).mpr hy) ((field_contDiff c J).differentiable (by simp) y)
    intro z hz
    exact hmax ((onSphere_iff_norm_sq z).mp hz)
  refine ⟨hmax.isLocalMaxOn,sourceHighCriticalGoodSet_radial n μ Q h0 U hJ hy hcrit ?_⟩
  rw [actualScore_value_eq]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+2 : ℕ))).mpr
  nlinarith

theorem sourceHighCriticalGoodSet_exponential (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hm : markK μ β Q ∈ Ioo L R)
    (hA3 : δ ≤ sourceMarkedLeastCurvature μ Q*(sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ n : ℕ in atTop,
      disorderLaw (n+2) μ.maxDegree (sourceHighCriticalGoodSet n μ Q (markE μ β x Q-δ) (Ioo L R))ᶜ ≤
        ENNReal.ofReal (Real.exp (-c*(n+2 : ℕ))) := by
  obtain ⟨c,hc,hcount⟩ := sourceHighExcludedCountMass_exponential μ h hnp hm hA3
  refine ⟨c,hc,?_⟩
  filter_upwards [hcount] with n hn
  exact (sourceHighCriticalGoodSet_compl_measure_le_count n μ h.overlap_range.1 _ _ measurableSet_Ioo).trans hn

theorem sourceSphereMaximum_probability_le_tail_and_error (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hA3 : δ ≤ sourceMarkedLeastCurvature μ Q*(sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ n : ℕ in atTop,∀ H : ℝ,(n+2 : ℕ)*(markE μ β x Q-δ) ≤ H →
      (disorderLaw (n+2) μ.maxDegree).real {J | H ≤ sourceSphereMaximum n μ Q J} ≤
        sourceMaximumEnergyTail n μ Q (Ioo L R) H+Real.exp (-c*(n+2 : ℕ)) := by
  obtain ⟨c,hc,hcount⟩ := sourceHighExcludedCountMass_exponential μ h hnp hm hA3
  refine ⟨c,hc,?_⟩
  filter_upwards [hcount,sourceMaximumTailCountMass_toReal_eq μ h hnp hL hm] with n hn hTail
  intro H hH
  have hProb := sourceSphereMaximum_probability_le_counts n μ h.overlap_range.1 hnp
    (markE μ β x Q-δ) H (Ioo L R) measurableSet_Ioo hH
  have hMaxFinite := (sourceMaximumTailCountMass_finite n μ h.overlap_range.1 H (Ioo L R)).ne
  have hExcludedFinite := (sourceHighExcludedCountMass_finite n μ h.overlap_range.1
    (markE μ β x Q-δ) (Ioo L R)).ne
  have hp := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hMaxFinite,hExcludedFinite⟩) hProb
  rw [ENNReal.toReal_add hMaxFinite hExcludedFinite,hTail H] at hp
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  change (disorderLaw (n+2) μ.maxDegree).real {J | H ≤ sourceSphereMaximum n μ Q J} ≤
    sourceMaximumEnergyTail n μ Q (Ioo L R) H+
      (sourceHighExcludedCountMass n μ Q (markE μ β x Q-δ) (Ioo L R)).toReal at hp
  linarith

theorem normalized_source_center_above_lower_energy {E0 c0 M δ : ℝ}
    (hc0 : 0 < c0) (hM : 0 ≤ M) (hδ : 0 < δ) (m : ℕ → ℝ)
    (hcenter : ∀ᶠ n : ℕ in atTop,|m n-((n+2 : ℕ)*E0-Real.log (n+2 : ℕ)/(2*c0))| ≤ M)
    (L : ℝ) : ∀ᶠ n : ℕ in atTop,(n+2 : ℕ)*(E0-δ) ≤ m n+L := by
  have hLog := NatLogWindowScales.normalized_center_log_bounded hc0 hM m hcenter
  have hRatio := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero
    (show 0 ≤ 1/(2*c0)+1 by positivity) (fun n => m n-(n+2 : ℕ)*E0) hLog
  have hConst : Tendsto (fun n : ℕ => L/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using constant_div_dimension_tendsto L
  have hSum : Tendsto (fun n : ℕ => (m n-(n+2 : ℕ)*E0+L)/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [←add_div,zero_add] using hRatio.add hConst
  filter_upwards [hSum.eventually_const_lt (show -δ < 0 by linarith)] with n hn
  have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < (n+2 : ℕ))).mp hn
  nlinarith

/-- The actual centered global-maximum probability has the source limsup
bound, using the genuinely normalized original-field centering sequence. -/
theorem sourceSphereMaximum_centered_probability_limsup (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hA3 : δ ≤ sourceMarkedLeastCurvature μ Q*(sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x)))
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R) (t : ℝ) :
    Filter.limsup (fun n : ℕ => (disorderLaw (n+2) μ.maxDegree).real
      {J | d.center n+t ≤ sourceSphereMaximum n μ Q J}) atTop ≤ Real.exp (-(β*x)*t) := by
  obtain ⟨c,hc,hbound⟩ := sourceSphereMaximum_probability_le_tail_and_error μ h hnp hL hm hA3
  have hAbove := normalized_source_center_above_lower_energy (mul_pos h.beta_pos h.weight_range.1)
    d.log_constant_pos.le hδ d.center d.logarithmic_correction t
  have hDim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hExp : Tendsto (fun n : ℕ => Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp (hDim.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hUpper : Tendsto (fun n : ℕ => sourceMaximumEnergyTail n μ Q (Ioo L R) (d.center n+t)+
      Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    simpa only [add_zero] using (d.tail_limit t).add hExp
  have hProb : ∀ᶠ n : ℕ in atTop,(disorderLaw (n+2) μ.maxDegree).real
      {J | d.center n+t ≤ sourceSphereMaximum n μ Q J} ≤
        sourceMaximumEnergyTail n μ Q (Ioo L R) (d.center n+t)+Real.exp (-c*(n+2 : ℕ)) := by
    filter_upwards [hbound,hAbove] with n hn hhigh
    exact hn _ hhigh
  have hCobounded := isCoboundedUnder_le_of_le atTop
    (fun n : ℕ => measureReal_nonneg (μ := disorderLaw (n+2) μ.maxDegree)
      (s := {J | d.center n+t ≤ sourceSphereMaximum n μ Q J}))
  exact (limsup_le_limsup hProb hCobounded hUpper.isBoundedUnder_le).trans_eq hUpper.limsup_eq

end SlowEquilibration.SphericalMarkedWindows
