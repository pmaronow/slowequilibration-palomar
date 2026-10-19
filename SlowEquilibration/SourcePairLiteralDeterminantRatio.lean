-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePairDeterminantRatioStatement
public import SlowEquilibration.PairLiteralProductIntegral

/-! Literal source11.7 quotients: the original product determinant remains
inside the numerator expectation, and both exact one-point GOE means remain
in its denominator. All source model estimates are discharged internally. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianObservationCoercivity IntrinsicHessianLaw PairObservationTargets GOEPhysicalPotential PairSchurExpectation
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

theorem source_mixed_literal_determinant_ratio (μ:FiniteMixture) {Q M gap:ℝ}
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
      let D:=fun J=>ConditionedDeterminantMoments.intrinsicDet μ Q x J*
        ConditionedDeterminantMoments.intrinsicDet μ Q y J
      Integrable D (coefficientKernel A w) ∧ Integrable (fun J=>(D J/(m1*m2))^2) (coefficientKernel A w) ∧
        |(∫ J,D J ∂coefficientKernel A w)/(m1*m2)-1| ≤ C*(|overlap x y|^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)) ∧
        (∫ J,(D J/(m1*m2))^2 ∂coefficientKernel A w) ≤ C:=by
  obtain ⟨η,C,hη,hC,hRatio⟩:=source_mixed_determinant_ratio_statement μ hQ hnp hd hM hgap
  refine ⟨η,C,hη,hC,?_⟩
  filter_upwards [hRatio,source_adjacent_physicalMean_lower_eventually (Z:=M) μ hQ (by omega) hgap] with n hn hMean
  intro x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hr hk1 hk2
  dsimp only
  have hR:=hn x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hr hk1 hk2
  have hM1:=hMean k1 hk1 ((le_abs_self _).trans hk1M)
  have hM2:=hMean k2 hk2 ((le_abs_self _).trans hk2M)
  have hQint:=literal_product_integral_quotient _ (ConditionedDeterminantMoments.intrinsicDet μ Q x)
    (ConditionedDeterminantMoments.intrinsicDet μ Q y) hM1.2.1.ne' hM2.2.1.ne' hR.1
  refine ⟨hQint.1,?_,?_,?_⟩
  · simpa only [div_mul_div_comm] using hR.2.1
  · have hh:=hR.2.2.1
    rw [hQint.2] at hh
    exact hh
  · simpa only [div_mul_div_comm] using hR.2.2.2


theorem source_pure_literal_determinant_ratio (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap:ℝ}
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
      let D:=fun J=>ConditionedDeterminantMoments.intrinsicDet μ Q x J*
        ConditionedDeterminantMoments.intrinsicDet μ Q y J
      Integrable D (coefficientKernel A w) ∧ Integrable (fun J=>(D J/(m1*m2))^2) (coefficientKernel A w) ∧
        |(∫ J,D J ∂coefficientKernel A w)/(m1*m2)-1| ≤ C*(|overlap x y|^(p-2)+1/Real.sqrt (n+3:ℕ)) ∧
        (∫ J,(D J/(m1*m2))^2 ∂coefficientKernel A w) ≤ C:=by
  dsimp only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hdegree:μ.minDegree=p:=by simp [μ,FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p halpha.ne']
  have hd:3 ≤ μ.minDegree:=by rw [hdegree];omega
  let Mbig:=((p:ℝ)+1)*M
  obtain ⟨η,C,hη,hC,hRatio⟩:=source_pure_determinant_ratio_statement p hp alpha halpha hQ hM hgap
  refine ⟨η,C,hη,hC,?_⟩
  filter_upwards [hRatio,source_adjacent_physicalMean_lower_eventually (Z:=Mbig) μ hQ hd hgap] with n hn hMean
  intro x y hx hy h1 h2 hh1 hh2 hr hk1 hk2
  let k1:=(p:ℝ)*h1
  let k2:=(p:ℝ)*h2
  have hk1Z:k1 ≤ Mbig:=by
    exact (mul_le_mul_of_nonneg_left ((le_abs_self h1).trans hh1) (Nat.cast_nonneg (α:=ℝ) p)).trans (by dsimp only [Mbig];nlinarith)
  have hk2Z:k2 ≤ Mbig:=by
    exact (mul_le_mul_of_nonneg_left ((le_abs_self h2).trans hh2) (Nat.cast_nonneg (α:=ℝ) p)).trans (by dsimp only [Mbig];nlinarith)
  have hR:=hn x y hx hy h1 h2 hh1 hh2 hr hk1 hk2
  have hM1:=hMean k1 hk1 hk1Z
  have hM2:=hMean k2 hk2 hk2Z
  have hQint:=literal_product_integral_quotient _ (ConditionedDeterminantMoments.intrinsicDet μ Q x)
    (ConditionedDeterminantMoments.intrinsicDet μ Q y) hM1.2.1.ne' hM2.2.1.ne' hR.1
  refine ⟨hQint.1,?_,?_,?_⟩
  · simpa only [div_mul_div_comm] using hR.2.1
  · have hh:=hR.2.2.1
    rw [hQint.2] at hh
    exact hh
  · simpa only [div_mul_div_comm] using hR.2.2.2

end
end SlowEquilibration.PairConditionalDeterminantMoments
