-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.HessianObservationBounds
public import SlowEquilibration.ValueObservationSmallOverlap

/-! True isometric omission of the redundant radial coordinate, and the
same actual small-overlap Hessian estimates for proper pure observations. -/
@[expose] public section
namespace SlowEquilibration.HessianObservationCovariance
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds PairObservationSmallOverlap
open ScalarCoefficientCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

def embedValueMixed {m : ℕ} (w : ValueObservationSpace m) : MixedObservationSpace m :=
  WithLp.toLp 2 (WithLp.toLp 2 ![w.fst,0],w.snd)

lemma embedValueMixed_norm {m : ℕ} (w : ValueObservationSpace m) :
    ‖embedValueMixed w‖=‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
  change ‖(WithLp.toLp 2 ![w.fst,0] : EuclideanSpace ℝ (Fin 2))‖^2+‖w.snd‖^2=‖w.fst‖^2+‖w.snd‖^2
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_two]

lemma mixed_adjoint_embedValue {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (w : ValueObservationSpace m) :
    (singleMixedObservation c x e).adjoint (embedValueMixed w)=
      (singleValueObservation c x e).adjoint w := by
  have hd : (innerSL ℝ (embedValueMixed w)).comp (singleMixedObservation c x e)=
      (innerSL ℝ w).comp (singleValueObservation c x e) := by
    rw [singleMixedObservation_dual,singleValueObservation_dual]
    simp [embedValueMixed]
  have hh:=congrArg (fun L : EuclideanDisorder N P →L[ℝ] ℝ => L.adjoint (1:ℝ)) hd
  simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply_one] using hh

theorem hessian_value_bound {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (w : ValueObservationSpace m) (hr : |overlap x y| ≤ 1) :
    |flatJetCLM c 2 x ![u,v] ((singleValueObservation c y f).adjoint w)| ≤
      (7*profileBound c*|overlap x y|/Real.sqrt (N:ℝ))*‖w‖ := by
  simpa only [mixed_adjoint_embedValue,embedValueMixed_norm] using
    hessian_mixed_bound hN c hc hdeg x y u v hx hy hu hv f hf (embedValueMixed w) hr

end
end SlowEquilibration.HessianObservationCovariance
