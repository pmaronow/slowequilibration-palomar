-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePurePairIntrinsicDeterminantFactorization
public import SlowEquilibration.PhysicalPairRatioAlgebra

/-! The source physical proper-pure pair ratio, retaining the literal tangent
zero density, physical two-height density and original intrinsic product.
All three model factors and positivity are proved internally. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations GaussianRegression
open GaussianObservationCoercivity NormalizedObservationCoercivity PairObservationSmallOverlap
open PairObservationTargets GOEPhysicalPotential PairSchurExpectation
open SphericalSequentialRegression
open GaussianObservationCoercivity GOEClippedResolvent IntrinsicHessianLaw
open SphericalTwoPointCovariance
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def sourcePurePhysicalPairRatio {n:ℕ} (p:ℕ) (hp:2 ≤ p) (alpha:ℝ) (halpha:0<alpha) (Q:ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 h2:ℝ):ℝ:=
  let μ:=FiniteMixture.pure p hp alpha halpha
  let k1:=(p:ℝ)*h1
  let k2:=(p:ℝ)*h2
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let f:=tangentFrame x hx
  let g:=tangentFrame y hy
  let G:=realObservationDensity (pairHilbert (gradientCLM c x f) (gradientCLM c y g)) 0/
    (realObservationDensity (gradientCLM c x f) 0*realObservationDensity (gradientCLM c y g) 0)
  let V:=physicalPairValueDensity (n+3) (residualPairValue c x y f g) h1 h2/
    ((normalizedValuePdf c x h1).toReal*
      (normalizedValuePdf c y h2).toReal)
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let w:=valuePairTarget (n+3) (n+2) h1 h2
  let b:=Q^2*μ.xi2 Q
  let D:=∫ J,(ConditionedDeterminantMoments.intrinsicDet μ Q x J/physicalMean (n+1) (n+3) b k1)*
    (ConditionedDeterminantMoments.intrinsicDet μ Q y J/physicalMean (n+1) (n+3) b k2) ∂coefficientKernel A w
  G*V*D

theorem source_pure_physical_pair_ratio_bounds (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) (hgap:0<gap) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ η Klog Kdet:ℝ,0<η ∧ 0<Klog ∧ 0<Kdet ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 h2:ℝ),|h1| ≤ M → |h2| ≤ M → |overlap x y| ≤ η →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h2 →
      let r:=|overlap x y|
      let T:=(n+3:ℕ)*r^μ.minDegree+(n+3:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2))
      let E:=r^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
      let R:=sourcePurePhysicalPairRatio p (by omega) alpha halpha Q x y hx hy h1 h2
      R ≤ (1+Kdet*E)*Real.exp (Klog*T) ∧
        (Klog*T ≤ 1 → Kdet*E ≤ 1 → |R-1| ≤ 4*Klog*T+Kdet*E):=by
  dsimp (config := { failIfUnchanged := false }) only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hdegree:μ.minDegree=p:=by simp [μ,FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p halpha.ne']
  have hd:4 ≤ μ.minDegree:=by rw [hdegree];exact hp
  obtain ⟨ηg,Kg,hηg,hKg,hGradient⟩:=uniform_pair_gradient_density_sharp μ hQ hd
  obtain ⟨ηv,Kv,hηv,hKv,hValue⟩:=uniform_source_pair_value_density_ratio μ hQ hd M hM
  obtain ⟨ηr,δ,hηr,hδ,hResidual⟩:=uniform_residual_pair_value_coercivity μ hQ hd
  obtain ⟨ηd,Kd,hηd,hKd,hDeterminant⟩:=source_pure_intrinsicDet_product_ratio p hp alpha halpha hQ hM hgap
  refine ⟨min ηg (min ηv (min ηr ηd)),Kg+Kv,Kd,
    lt_min hηg (lt_min hηv (lt_min hηr hηd)),by positivity,hKd,?_⟩
  filter_upwards [hDeterminant] with n hn
  intro x y hx hy h1 h2 hh1 hh2 hr hk1 hk2
  let k1:=(p:ℝ)*h1
  let k2:=(p:ℝ)*h2
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let f:=tangentFrame x hx
  let g:=tangentFrame y hy
  let r:=|overlap x y|
  let G:=realObservationDensity (pairHilbert (gradientCLM c x f) (gradientCLM c y g)) 0/
    (realObservationDensity (gradientCLM c x f) 0*realObservationDensity (gradientCLM c y g) 0)
  let V:=physicalPairValueDensity (n+3) (residualPairValue c x y f g) h1 h2/
    ((normalizedValuePdf c x h1).toReal*
      (normalizedValuePdf c y h2).toReal)
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let w:=valuePairTarget (n+3) (n+2) h1 h2
  let b:=Q^2*μ.xi2 Q
  let D:=∫ J,(ConditionedDeterminantMoments.intrinsicDet μ Q x J/physicalMean (n+1) (n+3) b k1)*
    (ConditionedDeterminantMoments.intrinsicDet μ Q y J/physicalMean (n+1) (n+3) b k2) ∂coefficientKernel A w
  let U:=Kg*((n+2:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2)))
  let W:=Kv*(n+3:ℕ)*r^μ.minDegree
  let T:=(n+3:ℕ)*r^μ.minDegree+(n+3:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2))
  let E:=r^(μ.minDegree-2)+1/Real.sqrt (n+3:ℕ)
  have hN:0<n+3:=by omega
  have hf:=tangentFrame_orthonormal x hx
  have hg:=tangentFrame_orthonormal y hy
  have hft:=tangentFrame_tangent x hx
  have hgt:=tangentFrame_tangent y hy
  have hGrad:=hGradient (n+3) (n+2) hN x y hx hy f g hf hg hft hgt (hr.trans (min_le_left _ _))
  have hVal:=hValue (n+3) (n+2) hN x y hx hy f g hf hg hft hgt
    (hr.trans ((min_le_right _ _).trans (min_le_left _ _))) h1 h2 hh1 hh2
  have hRes:=hResidual (n+3) (n+2) hN x y hx hy f g hf hg hft hgt
    (hr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hDet:=hn x y hx hy h1 h2 hh1 hh2
    (hr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) hk1 hk2
  let a:=Q*μ.xi1 Q
  have ha:0<a:=mul_pos hQ (mixture_xi1_pos μ hQ)
  have hAx:Surjective (gradientCLM c x f):=observation_surjective _ ha (gradient_coercivity hN μ hQ x hx f hf hft)
  have hBy:Surjective (gradientCLM c y g):=observation_surjective _ ha (gradient_coercivity hN μ hQ y hy g hg hgt)
  have hG:0<G:=div_pos (realObservationDensity_pos _ hGrad.1 _)
    (mul_pos (realObservationDensity_pos _ hAx _) (realObservationDensity_pos _ hBy _))
  have hSx:Surjective (normalizedValue c x):=div_smul_observation_surjective _
    (SphericalSequentialRegression.center_value_surjective μ hQ x hx) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  have hSy:Surjective (normalizedValue c y):=div_smul_observation_surjective _
    (SphericalSequentialRegression.center_value_surjective μ hQ y hy) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  have hV:0<V:=by
    dsimp only [V]
    rw [←physicalValueDensity_eq_normalizedValuePdf hN μ hQ x hx h1,
      ←physicalValueDensity_eq_normalizedValuePdf hN μ hQ y hy h2]
    unfold physicalPairValueDensity physicalValueDensity
    exact div_pos (mul_pos (Nat.cast_pos.mpr hN) (realObservationDensity_pos _ hRes.2.2.2.2.1 _))
      (mul_pos (mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)) (realObservationDensity_pos _ hSx _))
        (mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)) (realObservationDensity_pos _ hSy _)))
  have hGW:|Real.log G| ≤ U:=hGrad.2
  have hVW:|Real.log V| ≤ W:=hVal
  have hDE:|D-1| ≤ Kd*E:=by
    dsimp only [E]
    rw [hdegree]
    exact hDet.2
  have hUW:U+W ≤ (Kg+Kv)*T:=by
    have hp1:0 ≤ r^μ.minDegree:=by positivity
    have hp2:0 ≤ r^(2*(μ.minDegree-1)):=by positivity
    have hp3:0 ≤ r^(2*(μ.minDegree-2)):=by positivity
    have hN0:0 ≤ ((n+3:ℕ):ℝ) := by positivity
    have hDiff:((n+2:ℕ):ℝ) ≤ ((n+3:ℕ):ℝ):=by norm_cast;omega
    have hPart:=mul_le_mul_of_nonneg_right hDiff hp2
    have hLeft:(n+3:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2)) ≤ T:=by
      dsimp only [T]
      nlinarith [mul_nonneg hN0 hp1]
    have hRight:(n+3:ℕ)*r^μ.minDegree ≤ T:=by
      dsimp only [T]
      nlinarith [mul_nonneg hN0 hp2]
    calc
      U+W ≤ Kg*((n+3:ℕ)*r^(2*(μ.minDegree-1))+r^(2*(μ.minDegree-2)))+Kv*((n+3:ℕ)*r^μ.minDegree):=by
        dsimp only [U,W]
        nlinarith [mul_le_mul_of_nonneg_left hPart hKg.le]
      _ ≤ Kg*T+Kv*T:=add_le_add (mul_le_mul_of_nonneg_left hLeft hKg.le) (mul_le_mul_of_nonneg_left hRight hKv.le)
      _=_:=by ring
  change G*V*D ≤ (1+Kd*E)*Real.exp ((Kg+Kv)*T) ∧ _
  refine ⟨(pair_ratio_upper_of_log_bounds hG hV (by positivity) hGW hVW hDE).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hUW) (by positivity)),?_⟩
  intro hSmall hESmall
  exact (pair_ratio_error_of_log_bounds hG hV (by positivity) (by positivity) (by positivity) hGW hVW hDE
    (hUW.trans hSmall) hESmall).trans (by nlinarith)

end
end SlowEquilibration.PairConditionalDeterminantMoments
