-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairJetBounds
public import SlowEquilibration.SourcePhysicalPairIntensityIdentity

/-! Bounds for the exact physical pair Kac--Rice intensity, after its
true sphere-area normalization. These use the actual one-point critical
count marginals and original pair posterior; no ratio bound is a premise. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity IntrinsicHessianLaw
open SphericalPairMarkedWindows SphericalMarkedWindows SphereChartVolume
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 900000

lemma area_pair_ofReal_le {A:ℝ≥0∞} {P B W1 W2:ℝ}
    (hB:0 ≤ B) (hW1:0 ≤ W1) (hP:P ≤ B*(W1*W2)) :
    A^2*ENNReal.ofReal P ≤ ENNReal.ofReal B*((A*ENNReal.ofReal W1)*(A*ENNReal.ofReal W2)):=by
  have he:=ENNReal.ofReal_le_ofReal hP
  rw [ENNReal.ofReal_mul hB,ENNReal.ofReal_mul hW1] at he
  calc
    _ ≤ A^2*(ENNReal.ofReal B*(ENNReal.ofReal W1*ENNReal.ofReal W2)):=mul_le_mul_right he _
    _ = _:=by ring

theorem source_mixed_central_pair_intensity_bound (μ:FiniteMixture) {Q M gap α:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k2 →
      |overlap x y| ≤ ((n+3:ℕ):ℝ)^(-α) →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let b:ScorePairSpace:=WithLp.toLp 2 (WithLp.toLp 2 ![h1,k1],WithLp.toLp 2 ![h2,k2])
      (manuscriptRoundVolume (n+2) Set.univ)^2*
        (observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
          pairMixedPhysicalPdf c x y hx hy b*
          ∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q x J)*
            ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q y J)
            ∂pairMixedConditionedLaw c x y hx hy b) ≤
        ENNReal.ofReal (1+C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)))*
          (mixedCriticalIntensity (n+1) μ Q (WithLp.toLp 2 ![h1,k1])*mixedCriticalIntensity (n+1) μ Q (WithLp.toLp 2 ![h2,k2])):=by
  obtain ⟨C,hC,hBounds⟩:=source_mixed_central_pair_jet_bounds μ hQ hnp hd hM hgap hα
  obtain ⟨η,hη,hIdentity⟩:=source_mixed_physical_pair_intensity_identity μ hQ hnp hd hM hgap
  have hN:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hCut:∀ᶠ n:ℕ in atTop,((n+3:ℕ):ℝ)^(-α) ≤ η:=
    (((tendsto_rpow_neg_atTop (show 0<α by linarith)).comp hN).eventually (gt_mem_nhds hη)).mono (fun _ h=>h.le)
  refine ⟨C,hC,?_⟩
  filter_upwards [hBounds,hIdentity,hCut] with n hn hi hcut
  intro x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hk1 hk2 hr
  have hUpper:=(hn x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hk1 hk2 hr).2
  have hPos:=source_mixed_one_point_jet_positive μ hQ hnp x hx h1 k1 (by linarith)
  have hId:=hi x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M (hr.trans hcut) hk1 hk2
  have he:=area_pair_ofReal_le (A:=manuscriptRoundVolume (n+2) Set.univ) (by positivity) hPos.le hUpper
  rw [source_mixed_one_point_jet_area_normalization μ hQ hnp,
    source_mixed_one_point_jet_area_normalization μ hQ hnp,←hId] at he
  exact he

theorem source_pure_central_pair_intensity_bound (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap α:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 h2:ℝ),|h1| ≤ M → |h2| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h2 →
      |overlap x y| ≤ ((n+3:ℕ):ℝ)^(-α) →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let b:ValuePairSpace:=WithLp.toLp 2 (h1,h2)
      (manuscriptRoundVolume (n+2) Set.univ)^2*
        (observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
          pairValuePhysicalPdf c x y hx hy b*
          ∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q x J)*
            ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q y J)
            ∂pairValueConditionedLaw c x y hx hy b) ≤
        ENNReal.ofReal (1+C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)))*
          (pureCriticalIntensity (n+1) p (by omega) alpha halpha Q h1*pureCriticalIntensity (n+1) p (by omega) alpha halpha Q h2):=by
  dsimp only
  obtain ⟨C,hC,hBounds⟩:=source_pure_central_pair_jet_bounds p hp alpha halpha hQ hM hgap hα
  obtain ⟨η,hη,hIdentity⟩:=source_pure_physical_pair_intensity_identity p hp alpha halpha hQ hM hgap
  have hN:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hCut:∀ᶠ n:ℕ in atTop,((n+3:ℕ):ℝ)^(-α) ≤ η:=
    (((tendsto_rpow_neg_atTop (show 0<α by linarith)).comp hN).eventually (gt_mem_nhds hη)).mono (fun _ h=>h.le)
  refine ⟨C,hC,?_⟩
  filter_upwards [hBounds,hIdentity,hCut] with n hn hi hcut
  intro x y hx hy h1 h2 hh1 hh2 hk1 hk2 hr
  have hUpper:=(hn x y hx hy h1 h2 hh1 hh2 hk1 hk2 hr).2
  have hPos:=source_pure_one_point_jet_positive p (by omega) alpha halpha hQ x hx h1 (by linarith)
  have hId:=hi x y hx hy h1 h2 hh1 hh2 (hr.trans hcut) hk1 hk2
  have he:=area_pair_ofReal_le (A:=manuscriptRoundVolume (n+2) Set.univ) (by positivity) hPos.le hUpper
  rw [source_pure_one_point_jet_area_normalization p (by omega) alpha halpha hQ,
    source_pure_one_point_jet_area_normalization p (by omega) alpha halpha hQ,←hId] at he
  exact he

end
end SlowEquilibration.PairConditionalDeterminantMoments
