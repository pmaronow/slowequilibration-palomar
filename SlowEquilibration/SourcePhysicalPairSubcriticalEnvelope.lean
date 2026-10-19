-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedPhysicalPairRatio
public import SlowEquilibration.SourcePurePhysicalPairRatio
public import SlowEquilibration.PairCentralOverlapRates

/-! A genuine uniform subcritical annulus envelope for the original
physical pair ratio, derived from all actual density and determinant
factors. It has the source N*r²/8 exponent before the sphere-overlap law. -/
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
set_option maxHeartbeats 1200000

theorem source_mixed_physical_pair_subcritical_envelope (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) :
    ∃ δ C:ℝ,0<δ ∧ δ ≤ 1 ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k2 →
      |overlap x y| ≤ δ →
      sourceMixedPhysicalPairRatio μ Q x y hx hy h1 k1 h2 k2 ≤
        C*Real.exp (((n+3:ℕ):ℝ)*(overlap x y)^2/8):=by
  obtain ⟨η,Klog,Kdet,hη,hKlog,hKdet,hBounds⟩:=source_mixed_physical_pair_ratio_bounds μ hQ hnp hd hM hgap
  let δ:=min η (min 1 (Real.sqrt (1/(24*Klog))))
  have hδ:0<δ:=lt_min hη (lt_min (by norm_num) (by positivity))
  have hδOne:δ ≤ 1:=(min_le_right _ _).trans (min_le_left _ _)
  have hδRoot:δ ≤ Real.sqrt (1/(24*Klog)):=(min_le_right _ _).trans (min_le_right _ _)
  have hδSq:δ^2 ≤ 1/(24*Klog):=by
    have hh:=pow_le_pow_left₀ hδ.le hδRoot 2
    rwa [Real.sq_sqrt (by positivity)] at hh
  have hδRate:3*Klog*δ^2 ≤ (1/8:ℝ):=by
    have hh:=(le_div_iff₀ (by positivity : 0<24*Klog)).mp hδSq
    nlinarith
  refine ⟨δ,1+2*Kdet,hδ,hδOne,by positivity,?_⟩
  filter_upwards [hBounds] with n hn
  intro x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hk1 hk2 hr
  let r:=|overlap x y|
  let T:=(n+3:ℕ)*r^μ.minDegree+(n+3:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2))
  let E:=r^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hScalar:=local_overlap_scalar_envelope (N:=((n+3:ℕ):ℝ)) (r:=r) (by norm_cast;omega)
    (abs_nonneg _) hd hr hδOne
  have hB:=hn x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M (hr.trans (min_le_left _ _)) hk1 hk2
  have hCoeff:1+Kdet*E ≤ 1+2*Kdet:=by
    have hh:=mul_le_mul_of_nonneg_left hScalar.2 hKdet.le
    linarith
  have hExponent:Klog*T ≤ ((n+3:ℕ):ℝ)*(overlap x y)^2/8:=by
    have hST:=mul_le_mul_of_nonneg_left hScalar.1 hKlog.le
    have hSR:=mul_le_mul_of_nonneg_right hδRate (show 0 ≤ ((n+3:ℕ):ℝ)*r^2 by positivity)
    dsimp only [r] at hST hSR
    rw [sq_abs] at hST hSR
    nlinarith
  refine hB.1.trans ?_
  exact mul_le_mul hCoeff (Real.exp_le_exp.mpr hExponent) (Real.exp_pos _).le (by positivity)


theorem source_pure_physical_pair_subcritical_envelope (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) (hgap:0<gap) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ δ C:ℝ,0<δ ∧ δ ≤ 1 ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 h2:ℝ),|h1| ≤ M → |h2| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h2 →
      |overlap x y| ≤ δ →
      sourcePurePhysicalPairRatio p (by omega) alpha halpha Q x y hx hy h1 h2 ≤
        C*Real.exp (((n+3:ℕ):ℝ)*(overlap x y)^2/8):=by
  dsimp (config := { failIfUnchanged := false }) only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hdegree:μ.minDegree=p:=by simp [μ,FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p halpha.ne']
  have hd:4 ≤ μ.minDegree:=by rw [hdegree];exact hp
  obtain ⟨η,Klog,Kdet,hη,hKlog,hKdet,hBounds⟩:=source_pure_physical_pair_ratio_bounds p hp alpha halpha hQ hM hgap
  let δ:=min η (min 1 (Real.sqrt (1/(24*Klog))))
  have hδ:0<δ:=lt_min hη (lt_min (by norm_num) (by positivity))
  have hδOne:δ ≤ 1:=(min_le_right _ _).trans (min_le_left _ _)
  have hδRoot:δ ≤ Real.sqrt (1/(24*Klog)):=(min_le_right _ _).trans (min_le_right _ _)
  have hδSq:δ^2 ≤ 1/(24*Klog):=by
    have hh:=pow_le_pow_left₀ hδ.le hδRoot 2
    rwa [Real.sq_sqrt (by positivity)] at hh
  have hδRate:3*Klog*δ^2 ≤ (1/8:ℝ):=by
    have hh:=(le_div_iff₀ (by positivity : 0<24*Klog)).mp hδSq
    nlinarith
  refine ⟨δ,1+2*Kdet,hδ,hδOne,by positivity,?_⟩
  filter_upwards [hBounds] with n hn
  intro x y hx hy h1 h2 hh1 hh2 hk1 hk2 hr
  let r:=|overlap x y|
  let T:=(n+3:ℕ)*r^μ.minDegree+(n+3:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2))
  let E:=r^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hScalar:=local_overlap_scalar_envelope (N:=((n+3:ℕ):ℝ)) (r:=r) (by norm_cast;omega)
    (abs_nonneg _) hd hr hδOne
  have hB:=hn x y hx hy h1 h2 hh1 hh2 (hr.trans (min_le_left _ _)) hk1 hk2
  have hCoeff:1+Kdet*E ≤ 1+2*Kdet:=by
    have hh:=mul_le_mul_of_nonneg_left hScalar.2 hKdet.le
    linarith
  have hExponent:Klog*T ≤ ((n+3:ℕ):ℝ)*(overlap x y)^2/8:=by
    have hST:=mul_le_mul_of_nonneg_left hScalar.1 hKlog.le
    have hSR:=mul_le_mul_of_nonneg_right hδRate (show 0 ≤ ((n+3:ℕ):ℝ)*r^2 by positivity)
    dsimp only [r] at hST hSR
    rw [sq_abs] at hST hSR
    nlinarith
  refine hB.1.trans ?_
  exact mul_le_mul hCoeff (Real.exp_le_exp.mpr hExponent) (Real.exp_pos _).le (by positivity)

end
end SlowEquilibration.PairConditionalDeterminantMoments
