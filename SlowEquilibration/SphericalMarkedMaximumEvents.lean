-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPhysicalWindowCountBridge
public import SlowEquilibration.SphericalLatitudeMaximum
public import SlowEquilibration.SphericalGibbs

/-! Literal original-disorder high-critical events, Borel localization sets,
and true global-maximum events bounded by the actual maximum tail count. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter SphericalModel SphericalGaussianJet SphericalForm
open SphericalSequentialRegression WholeFieldRegression SphericalLatitudeChartKacRice
open scoped ENNReal Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceHighExcludedScoreWindow (h0 : ℝ) (U : Set ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangularScoreWindow (Ici h0) Uᶜ

def sourceBadHighCriticalEvent (n : ℕ) (μ : FiniteMixture) (Q h0 : ℝ) (U : Set ℝ) :
    Set (Disorder (n+2) μ.maxDegree) :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  {J | ∃ y : Vector (n+2), ‖y‖^2=(n+2 : ℕ) ∧ surfaceGradient (field c J) y=0 ∧
    actualScore c J y ∈ sourceHighExcludedScoreWindow h0 U}

irreducible_def sourceHighExcludedCountMass (n : ℕ) (μ : FiniteMixture) (Q h0 : ℝ)
    (U : Set ℝ) : ℝ≥0∞ :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  ∫⁻ J,actualScoreWindowCount (n+1) c (sourceHighExcludedScoreWindow h0 U) (fun _ _ => 1) J
    ∂disorderLaw (n+2) μ.maxDegree

theorem sourceBadHighCriticalEvent_measure_le_count (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (h0 : ℝ) (U : Set ℝ) (hU : MeasurableSet U) :
    disorderLaw (n+2) μ.maxDegree (sourceBadHighCriticalEvent n μ Q h0 U) ≤
      sourceHighExcludedCountMass n μ Q h0 U := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K := sourceHighExcludedScoreWindow h0 U
  let C := actualScoreWindowCount (n+1) c K (fun _ _ => 1)
  have hK : MeasurableSet K := rectangularScoreWindow_measurable _ _ measurableSet_Ici hU.compl
  have hC : AEMeasurable C (disorderLaw (n+2) μ.maxDegree) :=
    actualScoreWindowCount_aemeasurable (n+1) (by omega) μ hQ K hK _ measurable_const
  have hsub : sourceBadHighCriticalEvent n μ Q h0 U ⊆ {J | 1 ≤ C J} := by
    rintro J ⟨y,hy,hcrit,hwin⟩
    exact ENNReal.le_tsum (f := fun _z : {z : Vector (n+2) | ‖z‖^2=(n+2 : ℕ) ∧
      surfaceGradient (field c J) z=0 ∧ actualScore c J z ∈ K} => (1 : ℝ≥0∞))
        ⟨y,hy,hcrit,hwin⟩
  rw [sourceHighExcludedCountMass_def]
  apply (measure_mono hsub).trans
  simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hC 1

def sourceHighCriticalGoodSet (n : ℕ) (μ : FiniteMixture) (Q h0 : ℝ) (U : Set ℝ) :
    Set (Disorder (n+2) μ.maxDegree) :=
  (toMeasurable (disorderLaw (n+2) μ.maxDegree) (sourceBadHighCriticalEvent n μ Q h0 U))ᶜ

theorem sourceHighCriticalGoodSet_measurable (n : ℕ) (μ : FiniteMixture)
    (Q h0 : ℝ) (U : Set ℝ) : MeasurableSet (sourceHighCriticalGoodSet n μ Q h0 U) :=
  (measurableSet_toMeasurable _ _).compl

theorem sourceHighCriticalGoodSet_compl_measure_le_count (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (h0 : ℝ) (U : Set ℝ) (hU : MeasurableSet U) :
    disorderLaw (n+2) μ.maxDegree (sourceHighCriticalGoodSet n μ Q h0 U)ᶜ ≤
      sourceHighExcludedCountMass n μ Q h0 U := by
  rw [sourceHighCriticalGoodSet,compl_compl,measure_toMeasurable]
  exact sourceBadHighCriticalEvent_measure_le_count n μ hQ h0 U hU

theorem sourceHighCriticalGoodSet_radial (n : ℕ) (μ : FiniteMixture) (Q h0 : ℝ) (U : Set ℝ)
    {J : Disorder (n+2) μ.maxDegree} (hJ : J ∈ sourceHighCriticalGoodSet n μ Q h0 U)
    {y : Vector (n+2)} (hy : ‖y‖^2=(n+2 : ℕ))
    (hcrit : surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) y=0)
    (hhigh : h0 ≤ actualScore (centerCoefficients (mixtureCoefficients μ) Q) J y 0) :
    actualScore (centerCoefficients (mixtureCoefficients μ) Q) J y 1 ∈ U := by
  by_contra hout
  apply hJ
  apply subset_toMeasurable _ _
  exact ⟨y,hy,hcrit,hhigh,hout⟩

theorem actualScore_value_eq {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) (y : Vector N) :
    actualScore c J y 0=field c J y/(N : ℝ) := by
  simp only [actualScore,PiLp.smul_apply,smul_eq_mul,scoreCLM_apply_zero,unpack_euclideanDisorder,
    jet,iteratedFDeriv_zero_apply]
  ring

def sourceSphereMaximum (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (J : Disorder (n+2) μ.maxDegree) : ℝ :=
  sSup ((field (centerCoefficients (mixtureCoefficients μ) Q) J) ''
    {y : Vector (n+2) | ‖y‖^2=(n+2 : ℕ)})

theorem sourceSphereMaximum_continuous (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Continuous (sourceSphereMaximum n μ Q) :=
  (sphere_norm_sq_compact (n+1)).continuous_sSup (field_jointContinuous _)

theorem sourceSphereMaximum_attained (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder (n+2) μ.maxDegree) :
    ∃ y : Vector (n+2), ‖y‖^2=(n+2 : ℕ) ∧
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) y=0 ∧
      IsMaxOn (field (centerCoefficients (mixtureCoefficients μ) Q) J)
        {z : Vector (n+2) | ‖z‖^2=(n+2 : ℕ)} y ∧
      sourceSphereMaximum n μ Q J=field (centerCoefficients (mixtureCoefficients μ) Q) J y := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  obtain ⟨y,hy,hcrit,hmax⟩ := exists_sphere_maximum_critical (field c J)
    ((field_contDiff c J).of_le (by simp))
  refine ⟨y,hy,hcrit,hmax,?_⟩
  change sSup ((field c J) '' {z : Vector (n+2) | ‖z‖^2=(n+2 : ℕ)})=field c J y
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨field c J y,y,hy,rfl⟩
    · rintro v ⟨z,hz,rfl⟩
      exact hmax z hz
  · apply le_csSup
    · exact ⟨field c J y,by rintro v ⟨z,hz,rfl⟩;exact hmax z hz⟩
    · exact ⟨y,hy,rfl⟩

irreducible_def sourceMaximumTailCountMass (n : ℕ) (μ : FiniteMixture) (Q H : ℝ) (U : Set ℝ) : ℝ≥0∞ :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  ∫⁻ J,actualLocalMaxCount (n+1) c (physicalEnergyWindow (n+2) (Ici H) U) J
    ∂disorderLaw (n+2) μ.maxDegree

theorem sourceMaximumTailCountMass_finite (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (H : ℝ) (U : Set ℝ) : sourceMaximumTailCountMass n μ Q H U < ⊤ := by
  rw [sourceMaximumTailCountMass_def]
  rw [lintegral_congr_ae (actualLocalMaxCount_eq_negative_ae (n+1) (by omega) μ hQ _)]
  simp_rw [actualNegativeCriticalCount_eq_mark]
  exact bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ _ _ 1 (by simp)
    (by intro J y;unfold SphericalPosteriorMaps.negativeHessianMark;split_ifs <;> simp)

theorem sourceMaximumTailCountMass_toReal_eq (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : TwoAtomStationarity.markK μ β Q ∈ Ioo L R) :
    ∀ᶠ n : ℕ in atTop,∀ H : ℝ,
      (sourceMaximumTailCountMass n μ Q H (Ioo L R)).toReal=
        sourceMaximumEnergyTail n μ Q (Ioo L R) H := by
  filter_upwards [sourceMaximumRadialDensity_integrable μ h hnp hL hm] with n hn
  intro H
  have hKR : sourceMaximumTailCountMass n μ Q H (Ioo L R)=
      ∫⁻ v in Ici H,∫⁻ k in Ioo L R,mixedLocalMaxPhysicalIntensity n μ Q v k := by
    rw [sourceMaximumTailCountMass_def]
    exact actual_mixed_localMax_physical_intensity n μ h.overlap_range.1 hnp _ _ measurableSet_Ici measurableSet_Ioo
  rw [hKR]
  exact ENNRadialIntegralBridge.iterated_toReal_eq (mixedLocalMaxPhysicalIntensity n μ Q) (Ioo L R) (Ici H)
    (mixedLocalMaxPhysicalIntensity_measurable n μ Q) (mixedLocalMaxPhysicalIntensity_ne_top n μ Q) hn

/-- A true original-field maximum above the threshold is bounded by the
actual radial maximum tail count and the actual excluded-high-critical event. -/
theorem sourceSphereMaximum_probability_le_counts (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (h0 H : ℝ) (U : Set ℝ) (hU : MeasurableSet U) (hH : (n+2 : ℕ)*h0 ≤ H) :
    disorderLaw (n+2) μ.maxDegree {J | H ≤ sourceSphereMaximum n μ Q J} ≤
      sourceMaximumTailCountMass n μ Q H U+sourceHighExcludedCountMass n μ Q h0 U := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K := physicalEnergyWindow (n+2) (Ici H) U
  let C := actualLocalMaxCount (n+1) c K
  have hK : MeasurableSet K := rectangularScoreWindow_measurable _ _
    (measurableSet_Ici.preimage (measurable_const_mul ((n+2 : ℕ) : ℝ))) hU
  have hC : AEMeasurable C (disorderLaw (n+2) μ.maxDegree) :=
    (actual_mixed_localMax_count_intensity n μ hQ hnp K hK).1
  have hsub : {J | H ≤ sourceSphereMaximum n μ Q J} ⊆
      {J | 1 ≤ C J} ∪ sourceBadHighCriticalEvent n μ Q h0 U := by
    intro J hJ
    change H ≤ sourceSphereMaximum n μ Q J at hJ
    obtain ⟨y,hy,hcrit,hmax,hvalue⟩ := sourceSphereMaximum_attained n μ Q J
    rw [hvalue] at hJ
    have hhigh : h0 ≤ actualScore c J y 0 := by
      rw [actualScore_value_eq]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+2 : ℕ))).mpr
      nlinarith
    by_cases hr : actualScore c J y 1 ∈ U
    · left
      have hwin : actualScore c J y ∈ K := by
        refine ⟨?_,hr⟩
        change H ≤ (n+2 : ℕ)*actualScore c J y 0
        rw [actualScore_value_eq,mul_div_cancel₀ _ (by positivity)]
        exact hJ
      exact ENNReal.le_tsum (f := fun _z : {z : Vector (n+2) | ‖z‖^2=(n+2 : ℕ) ∧
        IsLocalMaxOn (field c J) {w | ‖w‖^2=(n+2 : ℕ)} z ∧ actualScore c J z ∈ K} => (1 : ℝ≥0∞))
        ⟨y,hy,hmax.isLocalMaxOn,hwin⟩
    · exact Or.inr ⟨y,hy,hcrit,hhigh,hr⟩
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply add_le_add
  · rw [sourceMaximumTailCountMass_def]
    simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hC 1
  · exact sourceBadHighCriticalEvent_measure_le_count n μ hQ h0 U hU

end SlowEquilibration.SphericalMarkedWindows
