-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairRatioNonnegative
public import SlowEquilibration.SourcePairLiteralDeterminantRatio

/-! Exact physical one-point and two-point jet intensities underlying the
source Kac--Rice ratio. The pair numerator is the expectation of the product
of the two original intrinsic determinants on one literal physical posterior. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations GaussianRegression
open GaussianObservationCoercivity IntrinsicHessianLaw SphericalSequentialRegression PairObservationTargets GOEPhysicalPotential
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

lemma normalized_product_integral_eq {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (D1 D2:Ω→ℝ) (m1 m2:ℝ) :
    (∫ x,(D1 x/m1)*(D2 x/m2) ∂P)=(∫ x,D1 x*D2 x ∂P)/(m1*m2):=by
  simp_rw [div_mul_div_comm]
  rw [integral_div]

def sourceMixedOnePointJetIntensity {n:ℕ} (μ:FiniteMixture) (Q:ℝ)
    (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (h k:ℝ):ℝ:=
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  realObservationDensity (gradientCLM c x (tangentFrame x hx)) 0*
    (normalizedScorePdf c x (WithLp.toLp 2 ![h,k])).toReal*
      physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k

def sourceMixedPairJetIntensity {n:ℕ} (μ:FiniteMixture) (Q:ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 k1 h2 k2:ℝ):ℝ:=
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let f:=tangentFrame x hx
  let g:=tangentFrame y hy
  let A:=pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
  let w:=mixedPairTarget (n+3) (n+2) h1 k1 h2 k2
  realObservationDensity (pairHilbert (gradientCLM c x f) (gradientCLM c y g)) 0*
    physicalPairScoreDensity (n+3) (residualPairScore c x y f g) h1 k1 h2 k2*
      (∫ J,ConditionedDeterminantMoments.intrinsicDet μ Q x J*
        ConditionedDeterminantMoments.intrinsicDet μ Q y J ∂coefficientKernel A w)

theorem source_mixed_physical_pair_ratio_eq_jetIntensity_quotient {n:ℕ} (μ:FiniteMixture) (Q:ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 k1 h2 k2:ℝ) :
    sourceMixedPhysicalPairRatio μ Q x y hx hy h1 k1 h2 k2=
      sourceMixedPairJetIntensity μ Q x y hx hy h1 k1 h2 k2/
        (sourceMixedOnePointJetIntensity μ Q x hx h1 k1*sourceMixedOnePointJetIntensity μ Q y hy h2 k2):=by
  unfold sourceMixedPhysicalPairRatio sourceMixedPairJetIntensity sourceMixedOnePointJetIntensity
  dsimp only
  rw [normalized_product_integral_eq]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

def sourcePureOnePointJetIntensity {n:ℕ} (p:ℕ) (hp:2 ≤ p) (alpha:ℝ) (halpha:0<alpha) (Q:ℝ)
    (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (h:ℝ):ℝ:=
  let μ:=FiniteMixture.pure p hp alpha halpha
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  realObservationDensity (gradientCLM c x (tangentFrame x hx)) 0*
    (normalizedValuePdf c x h).toReal*
      physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) ((p:ℝ)*h)

def sourcePurePairJetIntensity {n:ℕ} (p:ℕ) (hp:2 ≤ p) (alpha:ℝ) (halpha:0<alpha) (Q:ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 h2:ℝ):ℝ:=
  let μ:=FiniteMixture.pure p hp alpha halpha
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let f:=tangentFrame x hx
  let g:=tangentFrame y hy
  let A:=pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
  let w:=valuePairTarget (n+3) (n+2) h1 h2
  realObservationDensity (pairHilbert (gradientCLM c x f) (gradientCLM c y g)) 0*
    physicalPairValueDensity (n+3) (residualPairValue c x y f g) h1 h2*
      (∫ J,ConditionedDeterminantMoments.intrinsicDet μ Q x J*
        ConditionedDeterminantMoments.intrinsicDet μ Q y J ∂coefficientKernel A w)

theorem source_pure_physical_pair_ratio_eq_jetIntensity_quotient {n:ℕ} (p:ℕ) (hp:2 ≤ p)
    (alpha:ℝ) (halpha:0<alpha) (Q:ℝ)
    (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)) (h1 h2:ℝ) :
    sourcePurePhysicalPairRatio p hp alpha halpha Q x y hx hy h1 h2=
      sourcePurePairJetIntensity p hp alpha halpha Q x y hx hy h1 h2/
        (sourcePureOnePointJetIntensity p hp alpha halpha Q x hx h1*sourcePureOnePointJetIntensity p hp alpha halpha Q y hy h2):=by
  unfold sourcePurePhysicalPairRatio sourcePurePairJetIntensity sourcePureOnePointJetIntensity
  dsimp only
  rw [normalized_product_integral_eq]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

end
end SlowEquilibration.PairConditionalDeterminantMoments
