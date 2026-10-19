-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.PairValueCovariancePerturbation
/-! Actual conditional scalar-value Schur covariance, including proper pure models. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity PairObservationNormBounds
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
/-- Genuine conditional covariance error; only the already-proved inverse
bound for the actual two-gradient Gram is supplied. -/
theorem residualPairValue_gram_reference_bound {N m : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (hdeg : 2 ≤ μ.minDegree)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (f i) y=0)
    (hr : |overlap x y| ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (hA : Surjective (pairGradient (centerCoefficients (mixtureCoefficients μ) Q) x y e f))
    (hInv : ‖(gram (pairGradient (centerCoefficients (mixtureCoefficients μ) Q) x y e f)).inverse‖ ≤ T) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ‖gram (residualPairValue c x y e f)-gram (referenceValuePair μ Q)‖ ≤
      (2*profileBound c+4*(profileBound c)^2*T)*|overlap x y|^μ.minDegree := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let L:=profileBound c
  have hL : 0 < L := profileBound_pos c
  have hs:=valuePair_gram_reference_bound hN μ hQ x y hx hy hr
  have hc:=valuePair_gradient_cross_bound hN μ hQ x y hx hy e f he hf htanx htany hr
  have hd:=residual_gram_difference_bound (pairGradient c x y e f) hA (valuePair c x y)
  have hp : |overlap x y|^(2*(μ.minDegree-1)) ≤ |overlap x y|^μ.minDegree :=
    pow_le_pow_of_le_one (abs_nonneg _) hr (by omega)
  calc
    _ ≤ ‖gram (residualPairValue c x y e f)-gram (valuePair c x y)‖+
      ‖gram (valuePair c x y)-gram (referenceValuePair μ Q)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2*L*|overlap x y|^(μ.minDegree-1))^2*T+2*L*|overlap x y|^μ.minDegree := by
      have hsq:=sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hc
      exact add_le_add (hd.trans (mul_le_mul hsq hInv (norm_nonneg _) (sq_nonneg _))) hs
    _ ≤ (2*L+4*L^2*T)*|overlap x y|^μ.minDegree := by
      have hh:=mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*L^2*T)
      rw [mul_pow,← pow_mul,show (μ.minDegree-1)*2=2*(μ.minDegree-1) by omega]
      nlinarith

end
end SlowEquilibration.NormalizedPairObservations
