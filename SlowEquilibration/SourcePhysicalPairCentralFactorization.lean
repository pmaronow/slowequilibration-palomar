-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedPhysicalPairRatio
public import SlowEquilibration.SourcePurePhysicalPairRatio
public import SlowEquilibration.PairCentralOverlapRates

/-! Physical pair factorization on the literal source shrinking overlap
window. Gradient, physical mark, posterior determinant, and normalization
estimates are all derived from the original finite-mixture model. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open PairSchurExpectation
open GaussianObservationCoercivity GOEClippedResolvent IntrinsicHessianLaw
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

theorem source_mixed_physical_pair_central_factorization (μ:FiniteMixture) {Q M gap α:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k2 →
      |overlap x y| ≤ ((n+3:ℕ):ℝ)^(-α) →
      |sourceMixedPhysicalPairRatio μ Q x y hx hy h1 k1 h2 k2-1| ≤
        C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)):=by
  obtain ⟨η,Klog,Kdet,hη,hKlog,hKdet,hBounds⟩:=source_mixed_physical_pair_ratio_bounds μ hQ hnp hd hM hgap
  have hNlim:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hCut:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)^(-α)) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop (show 0<α by linarith)).comp hNlim
  have hRadius:∀ᶠ n:ℕ in atTop,((n+3:ℕ):ℝ)^(-α) ≤ η:=(hCut.eventually (gt_mem_nhds hη)).mono (fun _ h=>h.le)
  have hSmall1:∀ᶠ n:ℕ in atTop,3*Klog*((n+3:ℕ):ℝ)^(1-4*α) ≤ 1:=by
    have hh:=(ambient_central_rate_tendsto hα).const_mul (3*Klog)
    simp only [mul_zero] at hh
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hSmall2:∀ᶠ n:ℕ in atTop,2*Kdet/Real.sqrt (n+3:ℕ) ≤ 1:=by
    have hh:=ambient_inverse_sqrt_tendsto.const_mul (2*Kdet)
    simp only [mul_zero,mul_one_div] at hh
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  refine ⟨12*Klog+2*Kdet,by positivity,?_⟩
  filter_upwards [hBounds,hRadius,hSmall1,hSmall2] with n hn hRadiusN hSmallN1 hSmallN2
  intro x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hk1 hk2 hCore
  let r:=|overlap x y|
  let T:=(n+3:ℕ)*r^μ.minDegree+(n+3:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2))
  let E:=r^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hScalar:=central_overlap_scalar_rates (N:=((n+3:ℕ):ℝ)) (r:=r) (by norm_cast;omega)
    (abs_nonneg _) hd hα.le hCore
  have hB:=hn x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M (hCore.trans hRadiusN) hk1 hk2
  have hST:Klog*T ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left hScalar.1 hKlog.le
    exact hh.trans (by nlinarith)
  have hSE:Kdet*E ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left hScalar.2 hKdet.le
    exact hh.trans (by convert hSmallN2 using 1; ring)
  have hErr:=hB.2 hST hSE
  refine hErr.trans ?_
  have hT:=mul_le_mul_of_nonneg_left hScalar.1 (show 0 ≤ 4*Klog by positivity)
  have hE:=mul_le_mul_of_nonneg_left hScalar.2 hKdet.le
  rw [show 2/Real.sqrt (n+3:ℕ)=2*(1/Real.sqrt (n+3:ℕ)) by ring] at hE
  nlinarith [Real.rpow_nonneg (show 0 ≤ ((n+3:ℕ):ℝ) by positivity) (1-4*α),
    show 0 ≤ 1/Real.sqrt (n+3:ℕ) by positivity]


theorem source_pure_physical_pair_central_factorization (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap α:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 h2:ℝ),|h1| ≤ M → |h2| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h2 →
      |overlap x y| ≤ ((n+3:ℕ):ℝ)^(-α) →
      |sourcePurePhysicalPairRatio p (by omega) alpha halpha Q x y hx hy h1 h2-1| ≤
        C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)):=by
  dsimp (config := { failIfUnchanged := false }) only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hdegree:μ.minDegree=p:=by simp [μ,FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p halpha.ne']
  have hd:4 ≤ μ.minDegree:=by rw [hdegree];exact hp
  obtain ⟨η,Klog,Kdet,hη,hKlog,hKdet,hBounds⟩:=source_pure_physical_pair_ratio_bounds p hp alpha halpha hQ hM hgap
  have hNlim:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hCut:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)^(-α)) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop (show 0<α by linarith)).comp hNlim
  have hRadius:∀ᶠ n:ℕ in atTop,((n+3:ℕ):ℝ)^(-α) ≤ η:=(hCut.eventually (gt_mem_nhds hη)).mono (fun _ h=>h.le)
  have hSmall1:∀ᶠ n:ℕ in atTop,3*Klog*((n+3:ℕ):ℝ)^(1-4*α) ≤ 1:=by
    have hh:=(ambient_central_rate_tendsto hα).const_mul (3*Klog)
    simp only [mul_zero] at hh
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hSmall2:∀ᶠ n:ℕ in atTop,2*Kdet/Real.sqrt (n+3:ℕ) ≤ 1:=by
    have hh:=ambient_inverse_sqrt_tendsto.const_mul (2*Kdet)
    simp only [mul_zero,mul_one_div] at hh
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  refine ⟨12*Klog+2*Kdet,by positivity,?_⟩
  filter_upwards [hBounds,hRadius,hSmall1,hSmall2] with n hn hRadiusN hSmallN1 hSmallN2
  intro x y hx hy h1 h2 hh1 hh2 hk1 hk2 hCore
  let r:=|overlap x y|
  let T:=(n+3:ℕ)*r^μ.minDegree+(n+3:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2))
  let E:=r^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hScalar:=central_overlap_scalar_rates (N:=((n+3:ℕ):ℝ)) (r:=r) (by norm_cast;omega)
    (abs_nonneg _) hd hα.le hCore
  have hB:=hn x y hx hy h1 h2 hh1 hh2 (hCore.trans hRadiusN) hk1 hk2
  have hST:Klog*T ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left hScalar.1 hKlog.le
    exact hh.trans (by nlinarith)
  have hSE:Kdet*E ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left hScalar.2 hKdet.le
    exact hh.trans (by convert hSmallN2 using 1; ring)
  have hErr:=hB.2 hST hSE
  refine hErr.trans ?_
  have hT:=mul_le_mul_of_nonneg_left hScalar.1 (show 0 ≤ 4*Klog by positivity)
  have hE:=mul_le_mul_of_nonneg_left hScalar.2 hKdet.le
  rw [show 2/Real.sqrt (n+3:ℕ)=2*(1/Real.sqrt (n+3:ℕ)) by ring] at hE
  nlinarith [Real.rpow_nonneg (show 0 ≤ ((n+3:ℕ):ℝ) by positivity) (1-4*α),
    show 0 ≤ 1/Real.sqrt (n+3:ℕ) by positivity]

end
end SlowEquilibration.PairConditionalDeterminantMoments
