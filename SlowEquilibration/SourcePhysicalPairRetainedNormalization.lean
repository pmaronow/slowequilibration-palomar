-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairDeterminantSelectionLoss
public import SlowEquilibration.SourcePhysicalPairRetainedCountPartition
public import SlowEquilibration.SphericalSignedCounts

/-! The printed retained normalizer is the actual selected maximum-count
mean. Original marked Kac--Rice transfers the internallyproved posterior
determinant loss to every Borel window in the certified mark box. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open SphericalSequentialRegression SphericalForm SphereHessian LatitudeGroundTrial TwoAtomStationarity
open scoped ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] Classical.propDecidable

def sourceUnfilteredScoreWindowMean (n:ℕ) (μ:FiniteMixture) (Q:ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))):ℝ:=
  (∫⁻ J,actualScoreWindowCount n (centerCoefficients (mixtureCoefficients μ) Q) K
    (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree).toReal

def sourceRetainedScoreWindowMean (n:ℕ) (μ:FiniteMixture) (Q:ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G:ℝ):ℝ:=
  (∫⁻ J,sourceRetainedScoreWindowCount n (centerCoefficients (mixtureCoefficients μ) Q) K
    κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree).toReal

lemma sourceRetainedScoreWindowCount_le_unfiltered {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G:ℝ) (J:Disorder (n+1) P) :
    sourceRetainedScoreWindowCount n c K κ C ε η E G J ≤
      actualScoreWindowCount n c K (fun _ _=>1) J:=by
  unfold sourceRetainedScoreWindowCount actualScoreWindowCount
  exact ENNReal.tsum_le_tsum (fun _=>sourceSelectionMark_le_one c κ C ε η E G J _)

theorem source_mixed_retained_window_mass_lower (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (hK:MeasurableSet K) (κ C ε η E G t:ℝ)
    (hW:∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),∀ b ∈ K,
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let ν:=mixedConditionedLaw c u hu b
      ENNReal.ofReal (1-t)*(∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q u J) ∂ν) ≤
        ∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q u J) *
          sourceSelectionMark c κ C ε η E G J u ∂ν) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ENNReal.ofReal (1-t)*
      (∫⁻ J,actualScoreWindowCount n c K (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree) ≤
      ∫⁻ J,sourceRetainedScoreWindowCount n c K κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree:=by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  rw [(actual_mixed_score_window_kacRice n hn μ hQ hnp K hK (fun _ _=>1) measurable_const).2,
    (sourceRetainedScoreWindowCount_kacRice n hn μ hQ hnp K hK κ C ε η E G).2]
  have hpoint:∀ u:Vector (n+1),ENNReal.ofReal (1-t)*mixedWindowIntensity n μ Q K (fun _ _=>1) u ≤
      mixedWindowIntensity n μ Q K (sourceSelectionMark c κ C ε η E G) u:=by
    intro u
    unfold mixedWindowIntensity
    by_cases hu:‖u‖^2=(n+1:ℕ)
    · simp only [dite_eq_left hu,mul_one]
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK] with b hb
      have H:=mul_le_mul_of_nonneg_left (hW u hu b hb) (show (0:ℝ≥0∞) ≤ physicalScorePdf (n+1) μ Q b from zero_le)
      simpa only [ConditionedDeterminantMoments.intrinsicDet,mul_assoc,mul_left_comm,mul_comm] using H
    · simp only [dite_eq_right hu,mul_zero,le_refl]
  calc
    _=sphereKRPrefactor n μ Q*(ENNReal.ofReal (1-t)*
      ∫⁻ u,mixedWindowIntensity n μ Q K (fun _ _=>1) u ∂sphereLaw (n+1)):=by ac_rfl
    _ ≤ _:=by
      apply mul_le_mul_of_nonneg_left _ (show (0:ℝ≥0∞) ≤ sphereKRPrefactor n μ Q from zero_le)
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono hpoint

theorem source_mixed_retained_window_mean_bounds (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (hK:MeasurableSet K) (κ C ε η E G t:ℝ) (ht:t ≤ 1)
    (hW:∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),∀ b ∈ K,
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let ν:=mixedConditionedLaw c u hu b
      ENNReal.ofReal (1-t)*(∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q u J) ∂ν) ≤
        ∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q u J) *
          sourceSelectionMark c κ C ε η E G J u ∂ν) :
    (1-t)*sourceUnfilteredScoreWindowMean n μ Q K ≤ sourceRetainedScoreWindowMean n μ Q K κ C ε η E G ∧
      sourceRetainedScoreWindowMean n μ Q K κ C ε η E G ≤ sourceUnfilteredScoreWindowMean n μ Q K:=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hfinite:=bounded_scoreWindowCount_lintegral_lt_top n hn μ hQ K (fun _ _=>1) 1 (by simp) (by simp)
  have hup:(∫⁻ J,sourceRetainedScoreWindowCount n c K κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree) ≤
      ∫⁻ J,actualScoreWindowCount n c K (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree:=
    lintegral_mono (sourceRetainedScoreWindowCount_le_unfiltered n c K κ C ε η E G)
  have hlo:=source_mixed_retained_window_mass_lower n hn μ hQ hnp K hK κ C ε η E G t hW
  have hReal:=ENNReal.toReal_mono (hup.trans_lt hfinite).ne hlo
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr ht)] at hReal
  exact ⟨hReal,ENNReal.toReal_mono hfinite.ne hup⟩

/-- Actual retained/unfiltered normalization, derived without a supplied
retained mean or selected-event loss premise. All Borel windows in the
fixed source mark box are controlled uniformly. -/
theorem source_mixed_actual_retained_normalization (μ:FiniteMixture)
    {β x Q ε η δMax:ℝ} (h:Certificate μ β x Q)
    (hnp:μ.minDegree<μ.maxDegree) (hε:0<ε) (hη:0<η) (hεη:ε<1-η)
    (hδMax:0<δMax) :
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ L R δ C C₂:ℝ,L < markK μ β Q ∧ markK μ β Q<R ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g<L ∧ 0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ 0<C ∧ 0<C₂ ∧
      ∃ grid:ℕ,1 ≤ grid ∧
      Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
      ∀ᶠ n:ℕ in atTop,0 ≤ sourceSelectionWeightError C₂ μ Q G g grid n ∧
        sourceSelectionWeightError C₂ μ Q G g grid n<1 ∧
        ∀ (K:Set (EuclideanSpace ℝ (Fin 2))),MeasurableSet K →
          K ⊆ {b|b 0 ∈ Icc (E-δ) (E+δ) ∧ b 1 ∈ Icc L R} →
          (1-sourceSelectionWeightError C₂ μ Q G g grid n)*sourceUnfilteredScoreWindowMean (n+1) μ Q K ≤
              sourceRetainedScoreWindowMean (n+1) μ Q K (g/2) C ε η E G ∧
            sourceRetainedScoreWindowMean (n+1) μ Q K (g/2) C ε η E G ≤
              sourceUnfilteredScoreWindowMean (n+1) μ Q K:=by
  dsimp only
  obtain ⟨L,R,δ,C,C₂,hL,hR,hgapL,hδ,hδG,hδMax',hC,hC₂,grid,hgrid,hlm,hloss⟩:=
    source_mixed_physical_posterior_determinant_selection_loss μ h hnp hε hη hεη hδMax
  refine ⟨L,R,δ,C,C₂,hL,hR,hgapL,hδ,hδG,hδMax',hC,hC₂,grid,hgrid,hlm,?_⟩
  filter_upwards [hloss] with n hn
  refine ⟨sourceSelectionWeightError_nonneg _ _ _ _ _ _ _,hn.1,?_⟩
  intro K hK hsub
  apply source_mixed_retained_window_mean_bounds (n+1) (by omega) μ h.overlap_range.1 hnp K hK
    _ C ε η _ _ _ hn.1.le
  intro u hu b hb
  have hmarks:=hsub hb
  have H:=hn.2 u hu (b 0) hmarks.1 (b 1) hmarks.2
  have he:WithLp.toLp 2 ![b 0,b 1]=b:=by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  simpa only [he] using H

end
end SlowEquilibration.PairConditionalDeterminantMoments
