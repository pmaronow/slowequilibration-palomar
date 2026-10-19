-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairWindowDisintegration
public import SlowEquilibration.SourcePhysicalPairIntensityEnvelope
public import SlowEquilibration.PhysicalPairWindowIntegralTransfer

/-! The proved literal physical pair estimates integrated over every Borel
mark window in a fixed compact spectral-gap region. The normalizer remains
the square of the actual expected critical-window count. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open NormalizedPairObservations SphericalMarkedWindows SphericalPairMarkedWindows
open SphericalSequentialRegression SphereChartVolume IntrinsicGradientRegression IntrinsicHessianLaw
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 900000

lemma source_intrinsicPairDetWeight_eq {N:ℕ} (μ:FiniteMixture) (Q:ℝ) (x y:Vector N) :
    intrinsicPairDetWeight (centerCoefficients (mixtureCoefficients μ) Q) x y=
      fun J=>ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q x J)*
        ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q y J):=by
  rfl

lemma physical_score_fin_two (b:EuclideanSpace ℝ (Fin 2)) :
    WithLp.toLp 2 ![b 0,b 1]=b:=by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;> rfl

lemma physical_score_pair_coordinates (b:ScorePairSpace) :
    WithLp.toLp 2 (WithLp.toLp 2 ![b.fst 0,b.fst 1],WithLp.toLp 2 ![b.snd 0,b.snd 1])=b:=by
  rw [physical_score_fin_two,physical_score_fin_two]
  rfl

lemma physical_score_pair_reconstruction (b:ScorePairSpace) :
    WithLp.toLp 2 (b.fst,b.snd)=b:=by rfl

lemma physical_value_pair_coordinates (b:ValuePairSpace) :
    WithLp.toLp 2 (b.fst,b.snd)=b:=by rfl

theorem source_mixed_central_pair_window_bound (μ:FiniteMixture) {Q M gap α:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree)
    (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ)),
      |overlap x y| ≤ ((n+3:ℕ):ℝ)^(-α) →
      ∀ (K:Set (EuclideanSpace ℝ (Fin 2))),MeasurableSet K →
      (∀ b∈K,|b 0| ≤ M ∧ |b 1| ≤ M ∧ 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ b 1) →
      (manuscriptRoundVolume (n+2) univ)^2*
        intrinsicMixedPairWindowIntensity (centerCoefficients (mixtureCoefficients μ) Q) x y K (fun _=>1) ≤
      ENNReal.ofReal (1+C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)))*
        (∫⁻ J,actualScoreWindowCount (n+2) (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _=>1) J ∂disorderLaw (n+3) μ.maxDegree)^2:=by
  obtain ⟨C,hC,hBounds⟩:=source_mixed_central_pair_intensity_bound μ hQ hnp hd hM hgap hα
  obtain ⟨η,hη,hDis⟩:=source_mixed_physical_pair_window_disintegration μ hQ hnp hd
  have hN:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hCut:∀ᶠ n:ℕ in atTop,((n+3:ℕ):ℝ)^(-α) ≤ η:=
    (((tendsto_rpow_neg_atTop (show 0<α by linarith)).comp hN).eventually (gt_mem_nhds hη)).mono (fun _ h=>h.le)
  refine ⟨C,hC,?_⟩
  filter_upwards [hBounds,hCut] with n hn hcut
  intro x y hx hy hr K hK hmarks
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hEq:=hDis n x y hx hy (hr.trans hcut) K hK (fun _=>1) measurable_const
  dsimp only at hEq
  simp only [mul_one] at hEq
  rw [hEq]
  have hPoint:∀ b:ScorePairSpace,b.fst∈K → b.snd∈K →
      (manuscriptRoundVolume (n+2) univ)^2*
        (observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
          pairMixedPhysicalPdf c x y hx hy b*∫⁻ J,intrinsicPairDetWeight c x y J ∂pairMixedConditionedLaw c x y hx hy b) ≤
        ENNReal.ofReal (1+C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)))*
          (mixedCriticalIntensity (n+1) μ Q b.fst*mixedCriticalIntensity (n+1) μ Q b.snd):=by
    intro b hb1 hb2
    have h1:=hmarks b.fst hb1
    have h2:=hmarks b.snd hb2
    have hh:=hn x y hx hy (b.fst 0) (b.fst 1) (b.snd 0) (b.snd 1) h1.1 h1.2.1 h2.1 h2.2.1 h1.2.2 h2.2.2 hr
    simpa only [physical_score_fin_two,physical_score_pair_reconstruction,←source_intrinsicPairDetWeight_eq] using hh
  have hTrans:=physical_pair_window_integral_transfer K hK (mixedCriticalIntensity (n+1) μ Q)
    (mixedCriticalIntensity_measurable _ μ Q) (pairMixedConditionedLaw c x y hx hy)
    (intrinsicPairDetWeight c x y) (pairMixedPhysicalPdf c x y hx hy)
    (manuscriptRoundVolume_mass_ne_top (n+2)) (by unfold observationPdf;exact ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top hPoint
  rw [←physical_mark_pair_window_product_integral K hK _ (mixedCriticalIntensity_measurable _ μ Q),
    source_mixed_mark_pair_count_normalizer n μ hQ hnp K hK] at hTrans
  exact hTrans

theorem source_mixed_subcritical_pair_window_bound (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree)
    (hM:0 ≤ M) (hgap:0<gap) :
    ∃ δ C:ℝ,0<δ ∧ δ ≤ 1 ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (_hx:‖x‖^2=(n+3:ℕ)) (_hy:‖y‖^2=(n+3:ℕ)),
      |overlap x y| ≤ δ →
      ∀ (K:Set (EuclideanSpace ℝ (Fin 2))),MeasurableSet K →
      (∀ b∈K,|b 0| ≤ M ∧ |b 1| ≤ M ∧ 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ b 1) →
      (manuscriptRoundVolume (n+2) univ)^2*
        intrinsicMixedPairWindowIntensity (centerCoefficients (mixtureCoefficients μ) Q) x y K (fun _=>1) ≤
      ENNReal.ofReal (C*Real.exp (((n+3:ℕ):ℝ)*(overlap x y)^2/8))*
        (∫⁻ J,actualScoreWindowCount (n+2) (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _=>1) J ∂disorderLaw (n+3) μ.maxDegree)^2:=by
  obtain ⟨δ0,C,hδ0,hδOne,hC,hBounds⟩:=source_mixed_subcritical_pair_intensity_bound μ hQ hnp hd hM hgap
  obtain ⟨η,hη,hDis⟩:=source_mixed_physical_pair_window_disintegration μ hQ hnp hd
  refine ⟨min δ0 η,C,lt_min hδ0 hη,(min_le_left _ _).trans hδOne,hC,?_⟩
  filter_upwards [hBounds] with n hn
  intro x y hx hy hr K hK hmarks
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hEq:=hDis n x y hx hy (hr.trans (min_le_right _ _)) K hK (fun _=>1) measurable_const
  dsimp only at hEq
  simp only [mul_one] at hEq
  rw [hEq]
  have hPoint:∀ b:ScorePairSpace,b.fst∈K → b.snd∈K →
      (manuscriptRoundVolume (n+2) univ)^2*
        (observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
          pairMixedPhysicalPdf c x y hx hy b*∫⁻ J,intrinsicPairDetWeight c x y J ∂pairMixedConditionedLaw c x y hx hy b) ≤
        ENNReal.ofReal (C*Real.exp (((n+3:ℕ):ℝ)*(overlap x y)^2/8))*
          (mixedCriticalIntensity (n+1) μ Q b.fst*mixedCriticalIntensity (n+1) μ Q b.snd):=by
    intro b hb1 hb2
    have h1:=hmarks b.fst hb1
    have h2:=hmarks b.snd hb2
    have hh:=hn x y hx hy (b.fst 0) (b.fst 1) (b.snd 0) (b.snd 1) h1.1 h1.2.1 h2.1 h2.2.1 h1.2.2 h2.2.2 (hr.trans (min_le_left _ _))
    simpa only [physical_score_fin_two,physical_score_pair_reconstruction,←source_intrinsicPairDetWeight_eq] using hh
  have hTrans:=physical_pair_window_integral_transfer K hK (mixedCriticalIntensity (n+1) μ Q)
    (mixedCriticalIntensity_measurable _ μ Q) (pairMixedConditionedLaw c x y hx hy)
    (intrinsicPairDetWeight c x y) (pairMixedPhysicalPdf c x y hx hy)
    (manuscriptRoundVolume_mass_ne_top (n+2)) (by unfold observationPdf;exact ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top hPoint
  rw [←physical_mark_pair_window_product_integral K hK _ (mixedCriticalIntensity_measurable _ μ Q),
    source_mixed_mark_pair_count_normalizer n μ hQ hnp K hK] at hTrans
  exact hTrans

end
end SlowEquilibration.PairConditionalDeterminantMoments
