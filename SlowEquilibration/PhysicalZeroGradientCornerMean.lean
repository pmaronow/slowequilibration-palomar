-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalZeroGradientCornerLift
public import SlowEquilibration.PhysicalZeroGradientCornerPairRows
public import SlowEquilibration.PairResidualScoreCoercivity

/-! Sharp corner mean on the literal zero-gradient Gaussian fiber.
The score/gradient covariance has order d−1, while its Hessian row has
order d−3. Sequential regression therefore preserves the source d−2 rate. -/
@[expose] public section
namespace SlowEquilibration.PhysicalZeroGradientCorner
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds
open GaussianRegression GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma zero_gradient_rate_algebra {L T M s r : ℝ} {d : ℕ}
    (_hL : 0≤L) (_hT : 0≤T) (hM : 0≤M) (hs : 0<s)
    (hr0 : 0≤r) (hr1 : r≤1) (hd : 4≤d) :
    ((4*L*r^(d-2)/s)+(7*L*r^(d-3)/s)*T*(6*L*r^(d-1))) *
        (T*(M*s)) ≤ ((4*L+42*L^2*T)*T*M)*r^(d-2) := by
  have hp : r^(d-3)*r^(d-1)≤r^(d-2) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one hr0 hr1 (by omega)
  calc
    _ = (4*L*T*M)*r^(d-2)+(42*L^2*T^2*M)*(r^(d-3)*r^(d-1)) := by
      field_simp
      ring
    _ ≤ (4*L*T*M)*r^(d-2)+(42*L^2*T^2*M)*r^(d-2) := by
      gcongr
    _ = _ := by ring

/-- An actual residual-score lift with the exact active minimum-degree order.
The inverse bounds are ordinary covariance nondegeneracy inputs, independently
proved for the physical model by uniform_residual_pair_score_coercivity. -/
theorem residual_pair_score_corner_mean {N m : ℕ} (hN : 0<N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) (hd : 4≤μ.minDegree)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (htanu : inner ℝ u x=0) (htanv : inner ℝ v x=0)
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (f i) y=0)
    (b : ScorePairSpace) {T M : ℝ} (hT : 0≤T) (hM : 0≤M)
    (hA : Surjective (pairGradient (centerCoefficients (mixtureCoefficients μ) Q) x y e f))
    (hinvA : ‖(gram (pairGradient (centerCoefficients (mixtureCoefficients μ) Q) x y e f)).inverse‖≤T)
    (hinvB : ‖(gram (residualPairScore (centerCoefficients (mixtureCoefficients μ) Q) x y e f)).inverse‖≤T)
    (hb : ‖b‖≤M*Real.sqrt (N:ℝ)) (hr : |overlap x y|≤1) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    |flatJetCLM c 2 x ![u,v] (lift (residualPairScore c x y e f) b)| ≤
      ((4*profileBound c+42*(profileBound c)^2*T)*T*M)*|overlap x y|^(μ.minDegree-2) := by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let A:=pairGradient c x y e f
  let B:=scorePair c x y
  let H:=flatJetCLM c 2 x ![u,v]
  have hc:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ
  have hdeg:=center_degree_min μ Q
  have hscore:=hessian_pair_score_degree_order hN c hc (by omega : 3≤μ.minDegree)
    hdeg x y u v hy hu hv htanu htanv hr
  have hgrad:=hessian_pair_gradient_degree_order hN c hc (by omega : 3≤μ.minDegree)
    hdeg x y u v hx hy hu hv htanu htanv e f hf hr
  have hcross : ‖A.comp B.adjoint‖≤6*profileBound c*|overlap x y|^(μ.minDegree-1) := by
    have hn := ContinuousLinearMap.adjoint.norm_map (A.comp B.adjoint)
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint] at hn
    rw [← hn]
    exact scorePair_gradient_cross_bound hN μ hQ (by omega) x y hx hy e f he hf htanx htany hr
  have hbound:=residual_score_hessian_bound A hA B H b hscore hgrad hcross hinvA hinvB
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  change |H (lift (B.comp (residual A)) b)|≤_ at hbound ⊢
  calc
    _ ≤ ((4*profileBound c*|overlap x y|^(μ.minDegree-2)/Real.sqrt (N:ℝ))+
        (7*profileBound c*|overlap x y|^(μ.minDegree-3)/Real.sqrt (N:ℝ))*T*
          (6*profileBound c*|overlap x y|^(μ.minDegree-1)))*(T*‖b‖) := hbound
    _ ≤ ((4*profileBound c*|overlap x y|^(μ.minDegree-2)/Real.sqrt (N:ℝ))+
        (7*profileBound c*|overlap x y|^(μ.minDegree-3)/Real.sqrt (N:ℝ))*T*
          (6*profileBound c*|overlap x y|^(μ.minDegree-1)))*(T*(M*Real.sqrt (N:ℝ))) := by
      gcongr
      positivity [profileBound_pos c]
    _ ≤ _ := zero_gradient_rate_algebra (profileBound_pos c).le hT hM hs (abs_nonneg _) hr hd

end
end SlowEquilibration.PhysicalZeroGradientCorner
