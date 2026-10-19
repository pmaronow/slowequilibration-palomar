-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalZeroGradientCornerScoreRows
public import SlowEquilibration.PairHessianMean
public import SlowEquilibration.PairScoreCovariancePerturbation

/-! Sharp literal two-point Hessian rows. Tangency removes the own-point
block exactly, before the active-degree bound is applied to the other point. -/
@[expose] public section
namespace SlowEquilibration.PhysicalZeroGradientCorner
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds ScalarCoefficientCovariance
open HessianObservationCovariance PairObservationCrossCovariance
open GaussianRegression GaussianObservationCoercivity PairHessianMean
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 700000

lemma mixed_adjoint_gradient {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (w : EuclideanSpace ℝ (Fin m)) :
    (singleMixedObservation c x e).adjoint (WithLp.toLp 2 (0,w)) =
      (gradientCLM c x e).adjoint w := by
  have hd : (innerSL ℝ (WithLp.toLp 2 (0,w) : MixedObservationSpace m)).comp
      (singleMixedObservation c x e) = (innerSL ℝ w).comp (gradientCLM c x e) := by
    rw [singleMixedObservation_dual, gradientCLM_dual]
    simp
  have hh := congrArg (fun L : EuclideanDisorder N P →L[ℝ] ℝ => L.adjoint (1:ℝ)) hd
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_innerSL_apply, ContinuousLinearMap.toSpanSingleton_apply_one] using hh

lemma own_score_hessian_zero {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x u v : Vector N) (hu : inner ℝ u x=0) (hv : inner ℝ v x=0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    flatJetCLM c 2 x ![u,v] ((normalizedScore c x).adjoint w)=0 := by
  rw [hessian_score_coupling hN c hc hdeg]
  simp only [hu,hv,mul_zero,add_zero]

lemma own_gradient_hessian_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x u v : Vector N) (hu : inner ℝ u x=0) (hv : inner ℝ v x=0)
    (e : Fin m → Vector N) (w : EuclideanSpace ℝ (Fin m)) :
    flatJetCLM c 2 x ![u,v] ((gradientCLM c x e).adjoint w)=0 := by
  rw [← mixed_adjoint_gradient c x e w]
  exact own_mixed_hessian_zero hN c hc hdeg x u v hu hv e _

lemma norm_pair_hessian_row {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (H : E →L[ℝ] ℝ) (D₁ : E →L[ℝ] F) (D₂ : E →L[ℝ] G)
    {a : ℝ} (ha : 0≤a) (hzero : ∀ w,H (D₁.adjoint w)=0)
    (hrow : ∀ w,|H (D₂.adjoint w)|≤a*‖w‖) :
    ‖H.comp (pairHilbert D₁ D₂).adjoint‖≤a := by
  apply (H.comp (pairHilbert D₁ D₂).adjoint).opNorm_le_bound ha
  intro w
  change |H ((pairHilbert D₁ D₂).adjoint w)|≤a*‖w‖
  rw [pairHilbert_adjoint,map_add,hzero,zero_add]
  exact (hrow w.snd).trans
    (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le _ w) ha)

theorem hessian_pair_score_degree_order {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 3 ≤ d)
    (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y u v : Vector N) (hy : ‖y‖^2=(N:ℝ)) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (htanu : inner ℝ u x=0) (htanv : inner ℝ v x=0) (hr : |overlap x y|≤1) :
    ‖(flatJetCLM c 2 x ![u,v]).comp (scorePair c x y).adjoint‖ ≤
      4*profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ) := by
  let H:=flatJetCLM c 2 x ![u,v]
  have hrow := hessian_score_degree_order hN c hc hd hdeg x y u v hy hu hv hr
  apply norm_pair_hessian_row H (normalizedScore c x) (normalizedScore c y)
    (by positivity [profileBound_pos c])
  · intro w
    exact own_score_hessian_zero hN c hc (fun p hp => by have hh:=hdeg p hp;omega)
      x u v htanu htanv w
  · intro w
    exact ((H.comp (normalizedScore c y).adjoint).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hrow (norm_nonneg w))

theorem hessian_pair_gradient_degree_order {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 3 ≤ d)
    (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (htanu : inner ℝ u x=0) (htanv : inner ℝ v x=0)
    (e f : Fin m → Vector N) (hf : Orthonormal ℝ f) (hr : |overlap x y|≤1) :
    ‖(flatJetCLM c 2 x ![u,v]).comp (pairGradient c x y e f).adjoint‖ ≤
      7*profileBound c*|overlap x y|^(d-3)/Real.sqrt (N:ℝ) := by
  let H:=flatJetCLM c 2 x ![u,v]
  apply norm_pair_hessian_row H (gradientCLM c x e) (gradientCLM c y f)
    (by positivity [profileBound_pos c])
  · intro w
    exact own_gradient_hessian_zero hN c hc (fun p hp => by have hh:=hdeg p hp;omega)
      x u v htanu htanv e w
  · intro w
    have hn : ‖(WithLp.toLp 2 (0,w) : MixedObservationSpace m)‖=‖w‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp only [WithLp.prod_norm_sq_eq_of_L2]
      change ‖(0 : EuclideanSpace ℝ (Fin 2))‖^2+‖w‖^2=‖w‖^2
      simp
    have hb := hessian_mixed_degree_order hN c hc hd hdeg x y u v hx hy hu hv f hf
      (WithLp.toLp 2 (0,w)) hr
    rwa [mixed_adjoint_gradient,hn] at hb

end
end SlowEquilibration.PhysicalZeroGradientCorner
