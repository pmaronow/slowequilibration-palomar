-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairValueObservationGrouping
public import SlowEquilibration.PairScoreCovariancePerturbation

/-! Proper scalar-value conditional covariance, including pure mixtures.
No inverse of the singular pure value/radial score covariance is taken. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity NormalizedObservationCoercivity
open PairObservationCrossCovariance PairObservationNormBounds SphericalTwoPointCovariance
open ScalarCoefficientCovariance SphericalSequentialRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma normalizedValue_dual {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) (u : ℝ) :
    (innerSL ℝ u).comp (normalizedValue c x)=(u/Real.sqrt (N:ℝ)) • valueCLM c x := by
  ext g
  simp only [normalizedValue,ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,
    RCLike.inner_apply,conj_trivial,smul_eq_mul]
  ring

lemma value_cross_inner {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (u v : ℝ) :
    inner ℝ u (normalizedValue c x ((normalizedValue c y).adjoint v))=
      u*v*covariancePolynomial c (overlap x y) := by
  rw [← scalarCross_dual,normalizedValue_dual,normalizedValue_dual,
    scalarCross_smul_left,scalarCross_smul_right]
  change (u/Real.sqrt (N:ℝ))*((v/Real.sqrt (N:ℝ))*scalarCross
    (flatJetCLM c 0 x (fun i => Fin.elim0 i)) (flatJetCLM c 0 y (fun i => Fin.elim0 i)))=_
  rw [scalarCross_flatJet,value_value_two_point hN c hc x y]
  have hs : Real.sqrt (N:ℝ)^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hs0 : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  field_simp
  rw [← hs]
  simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

lemma value_gradient_cross_inner {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : Vector N) (f : Fin m → Vector N)
    (u : ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ u (normalizedValue c x ((gradientCLM c y f).adjoint v))=
      u*firstCovariance c (overlap x y)*(inner ℝ x (frameSum f v)/Real.sqrt (N:ℝ)) := by
  rw [← scalarCross_dual,normalizedValue_dual,gradientCLM_dual,scalarCross_smul_left]
  change (u/Real.sqrt (N:ℝ))*scalarCross
    (flatJetCLM c 0 x (fun i => Fin.elim0 i)) (flatJetCLM c 1 y (fun _ => frameSum f v))=_
  rw [scalarCross_flatJet,covariance_comm,gradient_value_covariance hN c hc y x,overlap_comm,real_inner_comm]
  ring

lemma value_cross_order {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y : Vector N) (hr : |overlap x y| ≤ 1) :
    ‖(normalizedValue c x).comp (normalizedValue c y).adjoint‖ ≤
      profileBound c*|overlap x y|^d := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro v u hv hu
  change inner ℝ (normalizedValue c x ((normalizedValue c y).adjoint v)) u ≤ _
  rw [real_inner_comm,value_cross_inner hN c hc]
  have huc : |u| ≤ 1 := by simpa only [Real.norm_eq_abs] using hu.le
  have hvc : |v| ≤ 1 := by simpa only [Real.norm_eq_abs] using hv.le
  exact (le_abs_self _).trans (abs_triple_le huc hvc (profile_order_common c d hdeg hr).1)

lemma value_gradient_cross_order {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) :
    ‖(normalizedValue c x).comp (gradientCLM c y f).adjoint‖ ≤ profileBound c*|overlap x y|^(d-1) := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro v u hv hu
  change inner ℝ (normalizedValue c x ((gradientCLM c y f).adjoint v)) u ≤ _
  rw [real_inner_comm,value_gradient_cross_inner hN c hc]
  have huc : |u| ≤ 1 := by simpa only [Real.norm_eq_abs] using hu.le
  have hV : ‖frameSum f v‖ ≤ 1 := by rw [frameSum_norm f hf,hv]
  have hi:=normalized_inner_le_one hN x hx (frameSum f v) hV
  have hp:=(profile_order_common c d hdeg hr).2.1
  exact (le_abs_self _).trans (by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le huc hi hp)

def referenceValue (μ : FiniteMixture) (Q : ℝ) : EuclideanDisorder 1 μ.maxDegree →L[ℝ] ℝ :=
  valueCLM (centerCoefficients (mixtureCoefficients μ) Q) referencePoint

def referenceValuePair (μ : FiniteMixture) (Q : ℝ) :
    WithLp 2 (EuclideanDisorder 1 μ.maxDegree×EuclideanDisorder 1 μ.maxDegree) →L[ℝ] ValuePairSpace :=
  independentPair (referenceValue μ Q) (referenceValue μ Q)

lemma normalizedValue_gram_eq_reference {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    gram (normalizedValue (centerCoefficients (mixtureCoefficients μ) Q) x)=gram (referenceValue μ Q) := by
  rw [normalizedValue,sqrtNormalized_value_gram hN μ hQ x hx,referenceValue,
    center_value_gram (by norm_num) μ hQ referencePoint (by simpa using referencePoint_norm_sq)]
  simp

lemma valuePair_gram_reference_bound {N : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hr : |overlap x y| ≤ 1) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ‖gram (valuePair c x y)-gram (referenceValuePair μ Q)‖ ≤
      2*profileBound c*|overlap x y|^μ.minDegree := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have h:=pair_gram_difference_independent (normalizedValue c x) (normalizedValue c y)
    (referenceValue μ Q) (referenceValue μ Q) (normalizedValue_gram_eq_reference hN μ hQ x hx)
      (normalizedValue_gram_eq_reference hN μ hQ y hy)
  have ho:=value_cross_order hN c (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ)
    (center_degree_min μ Q) x y hr
  apply h.trans
  nlinarith

lemma valuePair_gradient_cross_bound {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (f i) y=0)
    (hr : |overlap x y| ≤ 1) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ‖(valuePair c x y).comp (pairGradient c x y e f).adjoint‖ ≤
      2*profileBound c*|overlap x y|^(μ.minDegree-1) := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hc:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  have hzX : (normalizedValue c x).comp (gradientCLM c x e).adjoint=0 := by
    rw [normalizedValue,ContinuousLinearMap.smul_comp,value_gradient_cross_zero c hc x e htanx]
    ext g
    simp
  have hzY : (normalizedValue c y).comp (gradientCLM c y f).adjoint=0 := by
    rw [normalizedValue,ContinuousLinearMap.smul_comp,value_gradient_cross_zero c hc y f htany]
    ext g
    simp
  have h:=pair_cross_block_bound (normalizedValue c x) (normalizedValue c y)
    (gradientCLM c x e) (gradientCLM c y f)
  rw [hzX,hzY,norm_zero,zero_add,add_zero] at h
  have h1:=value_gradient_cross_order hN c hc (center_degree_min μ Q) x y hx f hf hr
  have h2:=value_gradient_cross_order hN c hc (center_degree_min μ Q) y x hy e he
    (by simpa only [overlap_comm] using hr)
  rw [overlap_comm x y] at h2
  apply h.trans
  nlinarith

end
end SlowEquilibration.NormalizedPairObservations
