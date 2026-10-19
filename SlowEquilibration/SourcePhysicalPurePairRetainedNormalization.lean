-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPurePairDeterminantSelectionLoss
public import SlowEquilibration.SourcePhysicalPairRetainedCountPartition
public import SlowEquilibration.SphericalSignedCounts

/-! The actual retained proper-pure maximum-count mean is asymptotically
the unfiltered critical-value-window mean. Original marked Kac--Rice
integrates the internally proved posterior own-determinant loss. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open SphericalForm SphereHessian LatitudeGroundTrial TwoAtomStationarity SphericalKacRiceGluing
open SphericalCountIntegrability
open SphericalSequentialRegression
open scoped ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

def sourceUnfilteredValueWindowMean (n:ℕ) (μ:FiniteMixture) (Q:ℝ) (I:Set ℝ):ℝ:=
  (∫⁻ J,actualValueWindowCount n (centerCoefficients (mixtureCoefficients μ) Q) I
    (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree).toReal

def sourceRetainedValueWindowMean (n:ℕ) (μ:FiniteMixture) (Q:ℝ)
    (I:Set ℝ) (κ C ε η E G:ℝ):ℝ:=
  (∫⁻ J,sourceRetainedValueWindowCount n (centerCoefficients (mixtureCoefficients μ) Q) I
    κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree).toReal

theorem sourceRetainedValueWindowCount_le_unfiltered {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (I:Set ℝ) (κ C ε η E G:ℝ) (J:Disorder (n+1) P) :
    sourceRetainedValueWindowCount n c I κ C ε η E G J ≤
      actualValueWindowCount n c I (fun _ _=>1) J:=by
  unfold sourceRetainedValueWindowCount actualValueWindowCount
  exact ENNReal.tsum_le_tsum (fun _=>sourceSelectionMark_le_one c κ C ε η E G J _)

theorem sourceValueWindowCount_le_total {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (I:Set ℝ) (J:Disorder (n+1) P) :
    actualValueWindowCount n c I (fun _ _=>1) J ≤ actualSphereCount n c (fun _ _=>1) J:=by
  rw [actualValueWindowCount_eq_indicator]
  unfold actualSphereCount
  apply ENNReal.tsum_le_tsum
  intro u
  dsimp only
  split_ifs <;> simp only [le_refl,zero_le]

theorem sourceUnfilteredValueWindowCount_lintegral_lt_top (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (I:Set ℝ) :
    (∫⁻ J,actualValueWindowCount n (centerCoefficients (mixtureCoefficients μ) Q) I
      (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree)<⊤:=by
  exact (lintegral_mono (sourceValueWindowCount_le_total n _ I)).trans_lt
    (actual_sphere_total_count_lintegral_lt_top n hn μ hQ)

/-- Literal value-window Kac--Rice transfers a posterior determinant
loss to the original actual count. This is a general integration reduction. -/
theorem source_value_retained_window_mass_lower (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (I:Set ℝ) (hI:MeasurableSet I) (κ C ε η E G t:ℝ)
    (hW:∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),∀ b ∈ I,
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let ν:=valueConditionedLaw c u hu b
      ENNReal.ofReal (1-t)*(∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q u J) ∂ν) ≤
        ∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q u J)*
          sourceSelectionMark c κ C ε η E G J u ∂ν) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ENNReal.ofReal (1-t)*
      (∫⁻ J,actualValueWindowCount n c I (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree) ≤
      ∫⁻ J,sourceRetainedValueWindowCount n c I κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree:=by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  rw [(actual_value_window_kacRice n hn μ hQ I hI (fun _ _=>1) measurable_const).2,
    (sourceRetainedValueWindowCount_kacRice n hn μ hQ I hI κ C ε η E G).2]
  have hpoint:∀ u:Vector (n+1),ENNReal.ofReal (1-t)*valueWindowIntensity n μ Q I (fun _ _=>1) u ≤
      valueWindowIntensity n μ Q I (sourceSelectionMark c κ C ε η E G) u:=by
    intro u
    unfold valueWindowIntensity
    by_cases hu:‖u‖^2=(n+1:ℕ)
    · simp only [dite_eq_left hu,mul_one]
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hI] with b hb
      have H:=mul_le_mul_of_nonneg_left (hW u hu b hb)
        (show (0:ℝ≥0∞) ≤ physicalValuePdf (n+1) μ Q b from bot_le)
      simpa only [ConditionedDeterminantMoments.intrinsicDet,mul_assoc,mul_left_comm,mul_comm] using H
    · simp only [dite_eq_right hu,mul_zero,le_refl]
  calc
    _=sphereKRPrefactor n μ Q*(ENNReal.ofReal (1-t)*
      ∫⁻ u,valueWindowIntensity n μ Q I (fun _ _=>1) u ∂sphereLaw (n+1)):=by ac_rfl
    _ ≤ _:=by
      apply mul_le_mul' le_rfl
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono hpoint

theorem source_value_retained_window_mean_bounds (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (I:Set ℝ) (hI:MeasurableSet I) (κ C ε η E G t:ℝ) (ht:t ≤ 1)
    (hW:∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),∀ b ∈ I,
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let ν:=valueConditionedLaw c u hu b
      ENNReal.ofReal (1-t)*(∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q u J) ∂ν) ≤
        ∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q u J)*
          sourceSelectionMark c κ C ε η E G J u ∂ν) :
    (1-t)*sourceUnfilteredValueWindowMean n μ Q I ≤ sourceRetainedValueWindowMean n μ Q I κ C ε η E G ∧
      sourceRetainedValueWindowMean n μ Q I κ C ε η E G ≤ sourceUnfilteredValueWindowMean n μ Q I:=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hfinite:=sourceUnfilteredValueWindowCount_lintegral_lt_top n hn μ hQ I
  have hup:(∫⁻ J,sourceRetainedValueWindowCount n c I κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree) ≤
      ∫⁻ J,actualValueWindowCount n c I (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree:=
    lintegral_mono (sourceRetainedValueWindowCount_le_unfiltered n c I κ C ε η E G)
  have hlo:=source_value_retained_window_mass_lower n hn μ hQ I hI κ C ε η E G t hW
  have hReal:=ENNReal.toReal_mono (hup.trans_lt hfinite).ne hlo
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr ht)] at hReal
  exact ⟨hReal,ENNReal.toReal_mono hfinite.ne hup⟩

/-- Actual proper-pure retained/unfiltered normalization with a vanishing
error derived internally, uniformly in every Borel window of the fixed
ground-value box. No retained mean or selected loss is a premise. -/
theorem source_pure_actual_retained_normalization
    (p:ℕ) (hp:2 ≤ p) (a:ℝ) (ha:0<a)
    {β x Q ε η δMax:ℝ} (h:Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hε:0<ε) (hη:0<η) (hεη:ε<1-η) (hδMax:0<δMax) :
    let μ:=FiniteMixture.pure p hp a ha
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ δ C C₂:ℝ,0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ 0<C ∧ 0<C₂ ∧
      ∃ grid:ℕ,1 ≤ grid ∧
      Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
      ∀ᶠ n:ℕ in atTop,0 ≤ sourceSelectionWeightError C₂ μ Q G g grid n ∧
        sourceSelectionWeightError C₂ μ Q G g grid n<1 ∧
        ∀ (I:Set ℝ),MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
          (1-sourceSelectionWeightError C₂ μ Q G g grid n)*sourceUnfilteredValueWindowMean (n+1) μ Q I ≤
              sourceRetainedValueWindowMean (n+1) μ Q I (g/2) C ε η E G ∧
            sourceRetainedValueWindowMean (n+1) μ Q I (g/2) C ε η E G ≤
              sourceUnfilteredValueWindowMean (n+1) μ Q I:=by
  dsimp only
  obtain ⟨δ,C,C₂,hδ,hδG,hδMax',hC,hC₂,grid,hgrid,hlm,hloss⟩:=
    source_pure_physical_posterior_determinant_selection_loss p hp a ha h hε hη hεη hδMax
  refine ⟨δ,C,C₂,hδ,hδG,hδMax',hC,hC₂,grid,hgrid,hlm,?_⟩
  filter_upwards [hloss] with n hn
  refine ⟨sourceSelectionWeightError_nonneg _ _ _ _ _ _ _,hn.1,?_⟩
  intro I hI hsub
  apply source_value_retained_window_mean_bounds (n+1) (by omega) _ h.overlap_range.1 I hI
    _ C ε η _ _ _ hn.1.le
  intro u hu b hb
  exact hn.2 u hu b (hsub hb)

end
end SlowEquilibration.PairConditionalDeterminantMoments
