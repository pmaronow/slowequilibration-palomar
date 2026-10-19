-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalSourceBandLower
public import SlowEquilibration.SphericalTAPCriticalLightBandMark
public import SlowEquilibration.SphericalPureMarkedWindows
public import SlowEquilibration.UnrestrictedConditionalMeans
public import SlowEquilibration.SphericalTAPCriticalSourceGeometry

/-! The source proper-pure Palm lower tail is transferred through the
literal scalar-value marked Kac--Rice formula. The radial coordinate is
deterministic by Euler homogeneity, so the value-only posterior is used. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureDenominatorPalmTransfer
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCriticalLightBandMark SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalSourceBandLower SphericalTAPCertificate
open SphericalTAPCriticalSourceGeometry TwoAtomStationarity
open ConditionedDeterminantMoments UnrestrictedConditionedDeterminants
open GOEPhysicalNormalizedMoments SphereHessian SphericalSequentialRegression
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Under pure value conditioning the literal light-band mark is the
fixed-value Palm lower-tail event. -/
theorem pure_light_band_mark_conditioned_ae
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+3)) (hu : ‖u‖^2=(n+3:ℕ))
    (b β m δ : ℝ) (I : Set ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∀ᵐ J ∂valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu b,
      sourceLightBandMark (n+1) μ hQ β m δ I J u =
        if partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u I) <
          δ*sourceCriticalBandScale (n+2) μ hQ β m *
            Real.exp (β*(((n+3:ℕ):ℝ)*b-m)) then 1 else 0 := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hv := valueConditioned_value_ae μ hQ.1 u hu b
  filter_upwards [hv] with J hJ
  have hN : (((n+3:ℕ):ℝ)) ≠ 0 := by positivity
  have hf : field c J u = (((n+3:ℕ):ℝ))*b := by
    have hh := (div_eq_iff hN).mp hJ
    simpa only [actualValue,mul_comm] using hh
  unfold sourceLightBandMark overlapRestrictedPartition
  rw [hf]
  simp only [overlapRegion, Nat.add_assoc, Nat.reduceAdd]
  rfl

/-- A pure fixed-mark Palm determinant ratio controls the actual
conditional marked intensity of the same original field. -/
theorem pure_light_band_mark_local_intensity_le
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (u : Vector (n+3)) (hu : ‖u‖^2=(n+3:ℕ)) (b β m δ : ℝ)
    (I : Set ℝ) (hI : MeasurableSet I) {ε : ℝ} (hε : 0 ≤ ε)
    (hk : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp alpha halpha).xi2 Q) <
      (p:ℝ)*b)
    (hRatio :
      let μ := FiniteMixture.pure p hp alpha halpha
      let ν := pureLaw p hp alpha halpha Q u hu b
      let D := intrinsicDet μ Q u
      let scale := sourceCriticalBandScale (n+2) μ hQ β m *
        Real.exp (β*(((n+3:ℕ):ℝ)*b-m))
      (∫ J in {J | partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I) < δ*scale}, D J ∂ν) /
        (∫ J, D J ∂ν) ≤ ε) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| *
      sourceLightBandMark (n+1) μ hQ β m δ I J u
        ∂valueConditionedLaw c u hu b) ≤
    ENNReal.ofReal ε *
      (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det|
        ∂valueConditionedLaw c u hu b) := by
  dsimp only at hRatio ⊢
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ν := pureLaw p hp alpha halpha Q u hu b
  let A : Set (Disorder (n+3) μ.maxDegree) :=
    {J | partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u I) <
      δ*sourceCriticalBandScale (n+2) μ hQ β m *
        Real.exp (β*(((n+3:ℕ):ℝ)*b-m))}
  have hA : MeasurableSet A := measurableSet_lt
    (SphericalTAPCriticalBandSectionBridge.sourceBandPartition_measurable
      (n+2) μ u I hI β) measurable_const
  have hD : Integrable (intrinsicDet μ Q u) ν :=
    pure_intrinsicDet_integrable p hp alpha halpha hQ.1 u hu b
  have hb : 0 < Q^2*μ.xi2 Q :=
    mul_pos (sq_pos_of_pos hQ.1) (μ.xi2_pos hQ.1)
  have hMean : 0 < ∫ J, intrinsicDet μ Q u J ∂ν := by
    rw [determinant_mean_eq_of_law
      (pure_intrinsicDet_hasLaw p hp alpha halpha hQ.1 u hu b)]
    exact physicalMean_pos (n+1) 1 hb hk
  have hRatio' : (∫ J in A, intrinsicDet μ Q u J ∂ν) /
      (∫ J, intrinsicDet μ Q u J ∂ν) ≤ ε := by
    simpa only [A, mul_assoc] using hRatio
  have hLocal := palm_ratio_to_lintegral_bound ν (intrinsicDet μ Q u)
    hD (fun _ => abs_nonneg _) A hA hε hMean hRatio'
  have hMark := pure_light_band_mark_conditioned_ae n p hp alpha halpha hQ
    u hu b β m δ I
  have hEq :
      (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
        sourceLightBandMark (n+1) μ hQ β m δ I J u ∂ν) =
      (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
        (if J ∈ A then 1 else 0) ∂ν) := by
    apply lintegral_congr_ae
    filter_upwards [hMark] with J hJ
    rw [hJ]
    rfl
  change (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
    sourceLightBandMark (n+1) μ hQ β m δ I J u ∂ν) ≤
    ENNReal.ofReal ε * (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) ∂ν)
  rw [hEq]
  exact hLocal

/-- Value-only marked Kac--Rice integrates a uniform pure posterior
determinant bound over any Borel scalar-value window. -/
theorem pure_marked_count_le_of_uniform_palm
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (W : Set ℝ) (hW : MeasurableSet W)
    (psi : Disorder (n+3) (FiniteMixture.pure p hp alpha halpha).maxDegree →
      Vector (n+3) → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (n+3)
      (FiniteMixture.pure p hp alpha halpha).maxDegree × Vector (n+3) =>
      psi z.1 z.2) {q : ℝ≥0∞} (hq : q ≠ ⊤)
    (hPalm : ∀ (u : Vector (n+3)) (hu : ‖u‖^2=(n+3:ℕ)), ∀ b ∈ W,
      let μ := FiniteMixture.pure p hp alpha halpha
      let c := centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| *
        psi J u ∂valueConditionedLaw c u hu b) ≤
      q*(∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det|
        ∂valueConditionedLaw c u hu b)) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualValueWindowCount (n+2) c W psi J
      ∂disorderLaw (n+3) μ.maxDegree) ≤
      q*(∫⁻ J, actualValueWindowCount (n+2) c W (fun _ _ => 1) J
        ∂disorderLaw (n+3) μ.maxDegree) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  rw [(actual_value_window_kacRice (n+2) (by omega) μ hQ W hW psi hpsi).2]
  rw [(actual_value_window_kacRice (n+2) (by omega) μ hQ W hW
    (fun _ _ => 1) measurable_const).2]
  have hinner :
      (∫⁻ u, valueWindowIntensity (n+2) μ Q W psi u
        ∂sphereLaw (n+3)) ≤
      q*(∫⁻ u, valueWindowIntensity (n+2) μ Q W (fun _ _ => 1) u
        ∂sphereLaw (n+3)) := by
    rw [← lintegral_const_mul' _ _ hq]
    apply lintegral_mono_ae
    filter_upwards [sphereLaw_support (by omega : 1 ≤ n+3)] with u hu
    rw [valueWindowIntensity, dite_eq_left hu,
      valueWindowIntensity, dite_eq_left hu]
    rw [← lintegral_const_mul' _ _ hq]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hW] with b hb
    simp only [mul_one]
    simpa only [mul_comm,mul_left_comm,mul_assoc] using
      (mul_le_mul_left (hPalm u hu b hb) (physicalValuePdf (n+3) μ Q b))
  calc
    _ ≤ sphereKRPrefactor (n+2) μ Q *
      (q*(∫⁻ u, valueWindowIntensity (n+2) μ Q W (fun _ _ => 1) u
        ∂sphereLaw (n+3))) := by
          simpa only [mul_comm,mul_left_comm,mul_assoc] using
            (mul_le_mul_left hinner (sphereKRPrefactor (n+2) μ Q))
    _ = _ := by ac_rfl

/-- The original pure critical-point count with a light physical band is
uniformly negligible compared with the unweighted count in every Borel
value window inside one certificate-selected neighborhood. -/
theorem pure_source_light_count_le_count_eventually
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    ∃ ε0 b : ℝ, 0 < ε0 ∧ 0 < b ∧ b < Real.sqrt Q ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ᶠ n : ℕ in atTop, ∀ (W : Set ℝ),
          MeasurableSet W → W ⊆ Icc (E-ε0) (E+ε0) → ∀ m : ℝ,
          (∫⁻ J, actualValueWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q) W
            (sourceLightBandMark (n+1) μ h.overlap_range β m δ
              (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
              ∂disorderLaw (n+3) μ.maxDegree) ≤
          ENNReal.ofReal ε *
            (∫⁻ J, actualValueWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) W
              (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  obtain ⟨εPalm,b0,hεPalm,hb0,hb0Q,hPalm⟩ :=
    pure_sourceEnergyPalm_common_band_and_energy_window p hp alpha halpha h
  obtain ⟨εEdge,g,Z,hεEdge,hg,hEdge⟩ :=
    pure_fixedBand_radial_window p hp alpha halpha h
  let ε0 := min εPalm εEdge
  have hε0 : 0 < ε0 := lt_min hεPalm hεEdge
  refine ⟨ε0,b0,hε0,hb0,hb0Q,?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hFixed⟩ := hPalm b0 hb0 le_rfl ε hε
  refine ⟨δ,hδ,?_⟩
  have hFixed' := (tendsto_add_atTop_nat 1).eventually hFixed
  filter_upwards [hFixed'] with n hn
  intro W hW hWBox m
  apply pure_marked_count_le_of_uniform_palm n p hp alpha halpha
    h.overlap_range.1 W hW _
      (sourceLightBandMark_measurable (n+1) μ h.overlap_range β m δ
        (Icc (Real.sqrt Q-b0) (Real.sqrt Q+b0)) measurableSet_Icc)
      ENNReal.ofReal_ne_top
  intro u hu a ha
  have ha0 : |a-E| ≤ ε0 := by
    apply abs_le.mpr
    constructor <;> linarith [(hWBox ha).1, (hWBox ha).2]
  have haPalm : |a-E| ≤ εPalm := ha0.trans (min_le_left _ _)
  have haEdge : |a-E| ≤ εEdge := ha0.trans (min_le_right _ _)
  have hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < (p:ℝ)*a :=
    lt_of_lt_of_le (by linarith [hg]) (hEdge a haEdge).1
  exact pure_light_band_mark_local_intensity_le n p hp alpha halpha
    h.overlap_range u hu a β m δ _ measurableSet_Icc hε.le hk
      (hn u hu a haPalm m)

end
end SlowEquilibration.SphericalPureDenominatorPalmTransfer
