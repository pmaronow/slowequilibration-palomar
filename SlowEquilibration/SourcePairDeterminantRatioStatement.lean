-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePairIntrinsicDeterminantFactorization
public import SlowEquilibration.SourcePurePairIntrinsicDeterminantFactorization
public import SlowEquilibration.SourcePairIntrinsicDeterminantProductMoments
public import SlowEquilibration.SourcePurePairIntrinsicDeterminantProductMoments

/-! All assertions of source Lemma11.7 for the two original intrinsic
Hessians, on their actual physical mixed or proper-pure posterior and with
the literal adjacent one-point GOE expectations in the denominator. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open PairObservationTargets GOEPhysicalPotential
open GaussianObservationCoercivity GOEClippedResolvent IntrinsicHessianLaw
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem source_mixed_determinant_ratio_statement (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) :
    ∃ η C:ℝ,0<η ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k2 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x (tangentFrame x hx))
        (singleMixedObservation c y (tangentFrame y hy))
      let w:=mixedPairTarget (n+3) (n+2) h1 k1 h2 k2
      let m1:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k1
      let m2:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k2
      let F:=fun J=>(ConditionedDeterminantMoments.intrinsicDet μ Q x J/m1)*
        (ConditionedDeterminantMoments.intrinsicDet μ Q y J/m2)
      Integrable F (coefficientKernel A w) ∧ Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
        |(∫ J,F J ∂coefficientKernel A w)-1| ≤ C*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)) ∧
        (∫ J,F J^2 ∂coefficientKernel A w) ≤ C:=by
  obtain ⟨ηf,Cf,hηf,hCf,hFactor⟩:=source_mixed_intrinsicDet_product_ratio μ hQ hnp hd hM hgap
  obtain ⟨ηm,Cm,hηm,hCm,hMoment⟩:=source_mixed_intrinsicDet_product_second_moment μ hQ hnp hd hM hgap
  refine ⟨min ηf ηm,max Cf Cm,lt_min hηf hηm,lt_of_lt_of_le hCf (le_max_left _ _),?_⟩
  filter_upwards [hFactor,hMoment] with n hf hm
  intro x y hx hy h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr hgap1 hgap2
  have hF:=hf x y hx hy h1 k1 h2 k2 hh1 hk1 hh2 hk2 (hr.trans (min_le_left _ _)) hgap1 hgap2
  have hM:=hm x y hx hy h1 k1 h2 k2 hh1 hk1 hh2 hk2 (hr.trans (min_le_right _ _)) hgap1 hgap2
  exact ⟨hF.1,hM.1,hF.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),hM.2.trans (le_max_right _ _)⟩


theorem source_pure_determinant_ratio_statement (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) (hgap:0<gap) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ η C:ℝ,0<η ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 h2:ℝ),|h1| ≤ M → |h2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h2 →
      let k1:=(p:ℝ)*h1
      let k2:=(p:ℝ)*h2
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleValueObservation c x (tangentFrame x hx))
        (singleValueObservation c y (tangentFrame y hy))
      let w:=valuePairTarget (n+3) (n+2) h1 h2
      let m1:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k1
      let m2:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k2
      let F:=fun J=>(ConditionedDeterminantMoments.intrinsicDet μ Q x J/m1)*
        (ConditionedDeterminantMoments.intrinsicDet μ Q y J/m2)
      Integrable F (coefficientKernel A w) ∧ Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
        |(∫ J,F J ∂coefficientKernel A w)-1| ≤ C*(|overlap x y|^(p-2)+1/Real.sqrt (n+3:ℕ)) ∧
        (∫ J,F J^2 ∂coefficientKernel A w) ≤ C:=by
  dsimp (config := { failIfUnchanged := false }) only
  obtain ⟨ηf,Cf,hηf,hCf,hFactor⟩:=source_pure_intrinsicDet_product_ratio p hp alpha halpha hQ hM hgap
  obtain ⟨ηm,Cm,hηm,hCm,hMoment⟩:=source_pure_intrinsicDet_product_second_moment p hp alpha halpha hQ hM hgap
  refine ⟨min ηf ηm,max Cf Cm,lt_min hηf hηm,lt_of_lt_of_le hCf (le_max_left _ _),?_⟩
  filter_upwards [hFactor,hMoment] with n hf hm
  intro x y hx hy h1 h2 hh1 hh2 hr hgap1 hgap2
  have hF:=hf x y hx hy h1 h2 hh1 hh2 (hr.trans (min_le_left _ _)) hgap1 hgap2
  have hM:=hm x y hx hy h1 h2 hh1 hh2 (hr.trans (min_le_right _ _)) hgap1 hgap2
  exact ⟨hF.1,hM.1,hF.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),hM.2.trans (le_max_right _ _)⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
