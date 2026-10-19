-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairHessianMean
public import SlowEquilibration.SphericalHessianBilinear

/-! The actual full tangent conditional Hessian mean has a dimension-free
operator norm bound; no Frobenius dimension factor or matrix surrogate. -/
@[expose] public section
namespace SlowEquilibration.PairHessianMean
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity HessianObservationCovariance
open SphericalTwoPointCovariance PairObservationNormBounds PairObservationTargets
open SphericalHessianTraceCovariance GOEAsymptotics OAI.CriticalSK
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem mixed_lift_hessian_opNorm {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (htan : ∀ i,inner ℝ (e i) x=0)
    (w : WithLp 2 (MixedObservationSpace m×MixedObservationSpace m))
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f))).inverse‖ ≤ 1/δ)
    (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) (hr : |overlap x y| ≤ 1) :
    ‖gaussianMatrixCLM (hessianGaussianCLM c x e
      (lift (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)) w))‖ ≤
      (7*profileBound c*M/δ)*|overlap x y| := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro q p hq hp
  change inner ℝ (gaussianMatrixCLM _ q) p ≤ _
  rw [real_inner_comm,hessianGaussianCLM_bilinear]
  exact (le_abs_self _).trans (mixed_lift_hessian_bound hN c hc hdeg x y
    (frameSum e p) (frameSum e q) hx hy
    ((frameSum_norm e he p).trans hp) ((frameSum_norm e he q).trans hq)
    (frameSum_tangent x e htan p) (frameSum_tangent x e htan q) e f hf w hδ hM hinv hw hr)

theorem value_lift_hessian_opNorm {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (e f : Fin m → Vector N) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (htan : ∀ i,inner ℝ (e i) x=0)
    (w : WithLp 2 (ValueObservationSpace m×ValueObservationSpace m))
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hinv : ‖(gram (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))).inverse‖ ≤ 1/δ)
    (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) (hr : |overlap x y| ≤ 1) :
    ‖gaussianMatrixCLM (hessianGaussianCLM c x e
      (lift (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)) w))‖ ≤
      (7*profileBound c*M/δ)*|overlap x y| := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity [profileBound_pos c])
  intro q p hq hp
  change inner ℝ (gaussianMatrixCLM _ q) p ≤ _
  rw [real_inner_comm,hessianGaussianCLM_bilinear]
  exact (le_abs_self _).trans (value_lift_hessian_bound hN c hc hdeg x y
    (frameSum e p) (frameSum e q) hx hy
    ((frameSum_norm e he p).trans hp) ((frameSum_norm e he q).trans hq)
    (frameSum_tangent x e htan p) (frameSum_tangent x e htan q) e f hf w hδ hM hinv hw hr)

end
end SlowEquilibration.PairHessianMean
