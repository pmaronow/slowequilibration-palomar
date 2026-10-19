-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationGrouping
public import SlowEquilibration.ObservationCrossBlockOrders
public import SlowEquilibration.GaussianPairBlockBounds
public import SlowEquilibration.GaussianRegressionSchur

/-! Actual score covariance after conditioning on both tangent gradients.
The genuine Schur error has order |overlap|^d with no dimension factor. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity PairObservationCrossCovariance
open NormalizedObservationCoercivity PairObservationNormBounds SphericalTwoPointCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

def referenceScore (μ : FiniteMixture) (Q : ℝ) :
    EuclideanDisorder 1 μ.maxDegree →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) referencePoint

def referenceScorePair (μ : FiniteMixture) (Q : ℝ) :
    WithLp 2 (EuclideanDisorder 1 μ.maxDegree×EuclideanDisorder 1 μ.maxDegree) →L[ℝ] ScorePairSpace :=
  independentPair (referenceScore μ Q) (referenceScore μ Q)

def residualPairScore {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ] ScorePairSpace :=
  (scorePair c x y).comp (GaussianRegression.residual (pairGradient c x y e f))

lemma center_degree_min (μ : FiniteMixture) (Q : ℝ) :
    ∀ p,centerCoefficients (mixtureCoefficients μ) Q p≠0 → μ.minDegree ≤ p.val.val := by
  intro p hp
  have hcoeff : μ.coeff p.val.val≠0 := by
    intro hz
    apply hp
    simp [centerCoefficients,mixtureCoefficients,hz]
  exact (μ.degree_bounds (Finsupp.mem_support_iff.mpr hcoeff)).1

/-- Actual extensive pair scores differ from the independent one-point
reference only through cross covariances of order d. -/
theorem scorePair_gram_reference_bound {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (hdeg : 2 ≤ μ.minDegree)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hr : |overlap x y| ≤ 1) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ‖gram (scorePair c x y)-gram (referenceScorePair μ Q)‖ ≤
      10*profileBound c*|overlap x y|^μ.minDegree := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hxgram : gram (normalizedScore c x)=gram (referenceScore μ Q) :=
    sqrtNormalized_score_gram_eq_reference hN μ hQ x hx
  have hygram : gram (normalizedScore c y)=gram (referenceScore μ Q) :=
    sqrtNormalized_score_gram_eq_reference hN μ hQ y hy
  have h:=pair_gram_difference_independent (normalizedScore c x) (normalizedScore c y)
    (referenceScore μ Q) (referenceScore μ Q) hxgram hygram
  have ho:=score_cross_order hN c (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ)
    hdeg (center_degree_min μ Q) x y hr
  apply h.trans
  nlinarith

/-- Same-point score/gradient blocks vanish literally. Only the two
opposite-point blocks remain, each of order d−1. -/
theorem scorePair_gradient_cross_bound {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (hdeg : 2 ≤ μ.minDegree)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (f i) y=0)
    (hr : |overlap x y| ≤ 1) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ‖(scorePair c x y).comp (pairGradient c x y e f).adjoint‖ ≤
      6*profileBound c*|overlap x y|^(μ.minDegree-1) := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hc:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  have hzX : (normalizedScore c x).comp (gradientCLM c x e).adjoint=0 := by
    rw [normalizedScore,ContinuousLinearMap.smul_comp,score_gradient_cross_zero c hc x e htanx]
    ext g i
    simp
  have hzY : (normalizedScore c y).comp (gradientCLM c y f).adjoint=0 := by
    rw [normalizedScore,ContinuousLinearMap.smul_comp,score_gradient_cross_zero c hc y f htany]
    ext g i
    simp
  have h:=pair_cross_block_bound (normalizedScore c x) (normalizedScore c y)
    (gradientCLM c x e) (gradientCLM c y f)
  rw [hzX,hzY,norm_zero,zero_add,add_zero] at h
  have h1:=score_gradient_cross_order hN c hc hdeg (center_degree_min μ Q) x y hx f hf hr
  have h2:=score_gradient_cross_order hN c hc hdeg (center_degree_min μ Q) y x hy e he
    (by simpa only [overlap_comm] using hr)
  rw [overlap_comm x y] at h2
  apply h.trans
  nlinarith

/-- Genuine conditional covariance error; only the already-proved inverse
bound for the actual two-gradient Gram is supplied. -/
theorem residualPairScore_gram_reference_bound {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (hdeg : 2 ≤ μ.minDegree)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (f i) y=0)
    (hr : |overlap x y| ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (hA : Surjective (pairGradient (centerCoefficients (mixtureCoefficients μ) Q) x y e f))
    (hInv : ‖(gram (pairGradient (centerCoefficients (mixtureCoefficients μ) Q) x y e f)).inverse‖ ≤ T) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ‖gram (residualPairScore c x y e f)-gram (referenceScorePair μ Q)‖ ≤
      (10*profileBound c+36*(profileBound c)^2*T)*|overlap x y|^μ.minDegree := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let L:=profileBound c
  have hL : 0 < L := profileBound_pos c
  have hs:=scorePair_gram_reference_bound hN μ hQ hdeg x y hx hy hr
  have hc:=scorePair_gradient_cross_bound hN μ hQ hdeg x y hx hy e f he hf htanx htany hr
  have hd:=residual_gram_difference_bound (pairGradient c x y e f) hA (scorePair c x y)
  have hp : |overlap x y|^(2*(μ.minDegree-1)) ≤ |overlap x y|^μ.minDegree :=
    pow_le_pow_of_le_one (abs_nonneg _) hr (by omega)
  calc
    _ ≤ ‖gram (residualPairScore c x y e f)-gram (scorePair c x y)‖+
      ‖gram (scorePair c x y)-gram (referenceScorePair μ Q)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (6*L*|overlap x y|^(μ.minDegree-1))^2*T+10*L*|overlap x y|^μ.minDegree := by
      have hsq:=sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hc
      exact add_le_add (hd.trans (mul_le_mul hsq hInv (norm_nonneg _) (sq_nonneg _))) hs
    _ ≤ (10*L+36*L^2*T)*|overlap x y|^μ.minDegree := by
      have hh:=mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 36*L^2*T)
      rw [mul_pow,← pow_mul,show (μ.minDegree-1)*2=2*(μ.minDegree-1) by omega]
      nlinarith

end
end SlowEquilibration.NormalizedPairObservations
