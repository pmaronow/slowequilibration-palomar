-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianActualCornerMeanSquare
public import SlowEquilibration.GaussianNormShiftMoment

/-! Uniform ordinary posterior corner moments, retaining the original
whole tensor coefficient kernel and its true small-overlap regression mean. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance SphericalConditionalMatrices
open NormalizedPairObservations PairHessianMean PairObservationNormBounds GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

/-- Genuine original mixed-pair posterior corner norm moments. Every
moment estimate is derived from actual covariance and regression. -/
theorem actual_common_corner_mixed_norm_moments {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (e f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : Surjective (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)))
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (MixedObservationSpace m×MixedObservationSpace m)) (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) :
    let A:=pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)
    ∀ r:ℕ,Integrable (fun J:Disorder N P=>‖actualObservation (cornerCLM c x v) J‖^r) (coefficientKernel A w) ∧
      (∫ J,‖actualObservation (cornerCLM c x v) J‖^r ∂coefficientKernel A w) ≤
        (2:ℝ)^r*((r.factorial:ℝ)*Real.exp (Real.sqrt (2*secondCovariance c 1)+secondCovariance c 1)+
          ((7*profileBound c*M/δ)*|overlap x y|)^r) := by
  dsimp only
  intro r
  have hC:=conditional_corner_norm_moments hN c hc hb x hx v hv hvtan _ hA r
  have hMean:=mixed_lift_hessian_bound hN c hc hdeg x y v v hx hy hv hv hvtan hvtan e f hf w hδ hM hinv hw hr
  have hm : ‖cornerCLM c x v (lift (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)) w)‖ ≤
      (7*profileBound c*M/δ)*|overlap x y| := by
    simpa only [Real.norm_eq_abs,cornerCLM] using hMean
  exact coefficientKernel_norm_moment_of_centered_moment _ (cornerCLM c x v) w r hC.1 hC.2 hm

/-- Proper value-only observations have identical ordinary corner control. -/
theorem actual_common_corner_value_norm_moments {N P m : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (e f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (hr : |overlap x y| ≤ 1) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : Surjective (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)))
    (hinv : ‖(gram (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))).inverse‖ ≤ 1/δ)
    (w : WithLp 2 (ValueObservationSpace m×ValueObservationSpace m)) (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) :
    let A:=pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)
    ∀ r:ℕ,Integrable (fun J:Disorder N P=>‖actualObservation (cornerCLM c x v) J‖^r) (coefficientKernel A w) ∧
      (∫ J,‖actualObservation (cornerCLM c x v) J‖^r ∂coefficientKernel A w) ≤
        (2:ℝ)^r*((r.factorial:ℝ)*Real.exp (Real.sqrt (2*secondCovariance c 1)+secondCovariance c 1)+
          ((7*profileBound c*M/δ)*|overlap x y|)^r) := by
  dsimp only
  intro r
  have hC:=conditional_corner_norm_moments hN c hc hb x hx v hv hvtan _ hA r
  have hMean:=value_lift_hessian_bound hN c hc hdeg x y v v hx hy hv hv hvtan hvtan e f hf w hδ hM hinv hw hr
  have hm : ‖cornerCLM c x v (lift (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)) w)‖ ≤
      (7*profileBound c*M/δ)*|overlap x y| := by
    simpa only [Real.norm_eq_abs,cornerCLM] using hMean
  exact coefficientKernel_norm_moment_of_centered_moment _ (cornerCLM c x v) w r hC.1 hC.2 hm

end
end SlowEquilibration.SphericalCommonHessianRegression
