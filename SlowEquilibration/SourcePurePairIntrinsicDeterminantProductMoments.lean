-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePairIntrinsicDeterminantProductMoments
public import SlowEquilibration.SourcePurePairIntrinsicDeterminantMoments
public import SlowEquilibration.PairPosteriorSymmetry
public import SlowEquilibration.PairDependentProductComparison
public import SlowEquilibration.SphericalWindowGeometry

/-! The second moment assertion in source Lemma11.7 is derived from the
two actual fourth moments on their shared original posterior. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open PairObservationSmallOverlap PairObservationTargets GOEPhysicalPotential PairSchurExpectation
open GaussianObservationCoercivity GOEClippedResolvent IntrinsicHessianLaw SphericalTwoPointCovariance
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem source_pure_intrinsicDet_product_second_moment (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap:ℝ}
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
      Integrable (fun J=>F J^2) (coefficientKernel A w) ∧
        (∫ J,F J^2 ∂coefficientKernel A w) ≤ C:=by
  dsimp (config := { failIfUnchanged := false }) only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hdegree:μ.minDegree=p:=by simp [μ,FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p halpha.ne']
  have hd:4 ≤ μ.minDegree:=by rw [hdegree];exact hp
  let Mbig:=((p:ℝ)+1)*M
  obtain ⟨ηm,C,hηm,hC,hMom⟩:=source_pure_pair_intrinsicDet_q_moments (Z:=Mbig) p hp alpha halpha hQ hgap hM (4:ℝ) (by norm_num)
  obtain ⟨η0,δ,hη0,hδ,hCoercive⟩:=uniform_value_pair_nondegenerate μ hQ hd
  refine ⟨min ηm η0,C,lt_min hηm hη0,hC,?_⟩
  filter_upwards [hMom] with n hn
  intro x y hx hy h1 h2 hh1 hh2 hr hk1 hk2
  let k1:=(p:ℝ)*h1
  let k2:=(p:ℝ)*h2
  have hk1M:|k1| ≤ Mbig:=by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg p)];exact (mul_le_mul_of_nonneg_left hh1 (Nat.cast_nonneg p)).trans (by dsimp only [Mbig];nlinarith)
  have hk2M:|k2| ≤ Mbig:=by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg p)];exact (mul_le_mul_of_nonneg_left hh2 (Nat.cast_nonneg p)).trans (by dsimp only [Mbig];nlinarith)
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let f:=tangentFrame x hx
  let g:=tangentFrame y hy
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let w:=valuePairTarget (n+3) (n+2) h1 h2
  let P:=coefficientKernel A w
  let m1:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k1
  let m2:=physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k2
  let F1:=fun J=>ConditionedDeterminantMoments.intrinsicDet μ Q x J/m1
  let F2:=fun J=>ConditionedDeterminantMoments.intrinsicDet μ Q y J/m2
  have hObs:=hCoercive (n+3) (n+2) (by omega) x y hx hy f g
    (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
    (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) (hr.trans (min_le_right _ _))
  have hSwap:=coefficientKernel_pair_swap _ _ hObs.2.1 w
  change coefficientKernel (pairHilbert (singleValueObservation c y g) (singleValueObservation c x f))
    (valuePairTarget (n+3) (n+2) h2 h1)=P at hSwap
  have hMom1:=hn x y hx hy h1 h2 hh1 hh2 (hr.trans (min_le_left _ _)) hk1 ((le_abs_self _).trans hk1M)
  have hMom2:=hn y x hy hx h2 h1 hh2 hh1
    (by simpa only [overlap_comm] using hr.trans (min_le_left _ _)) hk2 ((le_abs_self _).trans hk2M)
  dsimp only at hMom2
  rw [hSwap] at hMom2
  have hF14:Integrable (fun J=>F1 J^4) P:=by simpa only [Real.rpow_ofNat] using hMom1.1
  have hF24:Integrable (fun J=>F2 J^4) P:=by simpa only [Real.rpow_ofNat] using hMom2.1
  have hM14:(∫ J,F1 J^4 ∂P) ≤ C:=by simpa only [Real.rpow_ofNat] using hMom1.2
  have hM24:(∫ J,F2 J^4 ∂P) ≤ C:=by simpa only [Real.rpow_ofNat] using hMom2.2
  have hProduct:=dependent_product_second_moment P F1 F2
    ((source_intrinsicDet_real_measurable μ Q x hx).div_const m1)
    ((source_intrinsicDet_real_measurable μ Q y hy).div_const m2) hF14 hF24
  refine ⟨hProduct.1,hProduct.2.trans ?_⟩
  calc
    _ ≤ Real.sqrt C*Real.sqrt C:=mul_le_mul (Real.sqrt_le_sqrt hM14) (Real.sqrt_le_sqrt hM24) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _=C:=Real.mul_self_sqrt hC.le

end
end SlowEquilibration.PairConditionalDeterminantMoments
