-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairDensityIdentity

/-! Exact equality of the actual physical Kac--Rice pair integrand and
the ordinary pair jet intensity used in the proved source ratio bounds. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity IntrinsicHessianLaw PairObservationTargets
open SphericalPairMarkedWindows
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

lemma intrinsic_product_lintegral_eq {n:ℕ} (μ:FiniteMixture) (Q:ℝ)
    (x y:Vector (n+3)) (P:Measure (Disorder (n+3) μ.maxDegree))
    (hI:Integrable (fun J=>ConditionedDeterminantMoments.intrinsicDet μ Q x J*
      ConditionedDeterminantMoments.intrinsicDet μ Q y J) P) :
    (∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q x J)*
      ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q y J) ∂P)=
      ENNReal.ofReal (∫ J,ConditionedDeterminantMoments.intrinsicDet μ Q x J*
        ConditionedDeterminantMoments.intrinsicDet μ Q y J ∂P):=by
  have he:=ofReal_integral_eq_lintegral_ofReal hI
    (.of_forall (fun J=>mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hpos (J):0 ≤ ConditionedDeterminantMoments.intrinsicDet μ Q x J:=abs_nonneg _
  simp_rw [←ENNReal.ofReal_mul (hpos _)]
  exact he.symm

theorem source_mixed_physical_pair_intensity_identity (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) :
    ∃ η:ℝ,0<η ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k2 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let b:ScorePairSpace:=WithLp.toLp 2 (WithLp.toLp 2 ![h1,k1],WithLp.toLp 2 ![h2,k2])
      observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
        pairMixedPhysicalPdf c x y hx hy b*
        (∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q x J)*
          ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q y J)
          ∂pairMixedConditionedLaw c x y hx hy b)=
        ENNReal.ofReal (sourceMixedPairJetIntensity μ Q x y hx hy h1 k1 h2 k2):=by
  obtain ⟨η1,C,hη1,_hC,hLit⟩:=source_mixed_literal_determinant_ratio μ hQ hnp hd hM hgap
  obtain ⟨η2,hη2,hGroup⟩:=source_mixed_physical_posterior_grouping μ hQ hnp hd
  refine ⟨min η1 η2,lt_min hη1 hη2,?_⟩
  filter_upwards [hLit] with n hn
  intro x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hr hk1 hk2
  dsimp only
  have hL:=hn x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M (hr.trans (min_le_left _ _)) hk1 hk2
  have hG:=hGroup n x y hx hy (hr.trans (min_le_right _ _)) h1 k1 h2 k2
  rw [hG,source_pair_mixed_physical_pdf_eq,
    intrinsic_product_lintegral_eq μ Q x y _ hL.1]
  unfold sourceMixedPairJetIntensity
  dsimp only
  change ENNReal.ofReal (realObservationDensity _ 0)*ENNReal.ofReal _*ENNReal.ofReal _=_
  have hv:0 ≤ physicalPairScoreDensity (n+3)
      (residualPairScore (centerCoefficients (mixtureCoefficients μ) Q) x y (tangentFrame x hx) (tangentFrame y hy)) h1 k1 h2 k2:=by
    unfold physicalPairScoreDensity
    exact mul_nonneg (sq_nonneg _) (realObservationDensity_nonnegative _ _)
  rw [←ENNReal.ofReal_mul (realObservationDensity_nonnegative _ _),
    ←ENNReal.ofReal_mul (mul_nonneg (realObservationDensity_nonnegative _ _) hv)]
  rfl

theorem source_pure_physical_pair_intensity_identity (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) (hgap:0<gap) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ η:ℝ,0<η ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 h2:ℝ),|h1| ≤ M → |h2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h2 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let b:ValuePairSpace:=WithLp.toLp 2 (h1,h2)
      observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
        pairValuePhysicalPdf c x y hx hy b*
        (∫⁻ J,ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q x J)*
          ENNReal.ofReal (ConditionedDeterminantMoments.intrinsicDet μ Q y J)
          ∂pairValueConditionedLaw c x y hx hy b)=
        ENNReal.ofReal (sourcePurePairJetIntensity p (by omega) alpha halpha Q x y hx hy h1 h2):=by
  dsimp only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hdegree:μ.minDegree=p:=by simp [μ,FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p halpha.ne']
  have hd:4 ≤ μ.minDegree:=by rw [hdegree];exact hp
  obtain ⟨η1,C,hη1,_hC,hLit⟩:=source_pure_literal_determinant_ratio p hp alpha halpha hQ hM hgap
  obtain ⟨η2,hη2,hGroup⟩:=source_value_physical_posterior_grouping μ hQ hd
  refine ⟨min η1 η2,lt_min hη1 hη2,?_⟩
  filter_upwards [hLit] with n hn
  intro x y hx hy h1 h2 hh1 hh2 hr hk1 hk2
  have hL:=hn x y hx hy h1 h2 hh1 hh2 (hr.trans (min_le_left _ _)) hk1 hk2
  have hG:=hGroup n x y hx hy (hr.trans (min_le_right _ _)) h1 h2
  rw [hG,source_pair_value_physical_pdf_eq,
    intrinsic_product_lintegral_eq μ Q x y _ hL.1]
  unfold sourcePurePairJetIntensity
  dsimp only
  change ENNReal.ofReal (realObservationDensity _ 0)*ENNReal.ofReal _*ENNReal.ofReal _=_
  have hv:0 ≤ physicalPairValueDensity (n+3)
      (residualPairValue (centerCoefficients (mixtureCoefficients μ) Q) x y (tangentFrame x hx) (tangentFrame y hy)) h1 h2:=by
    unfold physicalPairValueDensity
    exact mul_nonneg (Nat.cast_nonneg _) (realObservationDensity_nonnegative _ _)
  rw [←ENNReal.ofReal_mul (realObservationDensity_nonnegative _ _),
    ←ENNReal.ofReal_mul (mul_nonneg (realObservationDensity_nonnegative _ _) hv)]
  rfl

end
end SlowEquilibration.PairConditionalDeterminantMoments
