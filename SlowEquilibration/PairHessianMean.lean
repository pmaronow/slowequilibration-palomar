-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ValueHessianObservationBounds
public import SlowEquilibration.PairObservationTargets

/-! Actual small-overlap conditional Hessian means. The regression lift is
the canonical full-coefficient Gaussian lift; its inverse bound is explicit
and will be discharged by the proved uniform pair coercivity. -/
@[expose] public section
namespace SlowEquilibration.PairHessianMean
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity HessianObservationCovariance
open SphericalTwoPointCovariance PairObservationNormBounds PairObservationTargets
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma own_mixed_hessian_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x u v : Vector N) (hu : inner ℝ u x=0) (hv : inner ℝ v x=0)
    (e : Fin m → Vector N) (w : MixedObservationSpace m) :
    flatJetCLM c 2 x ![u,v] ((singleMixedObservation c x e).adjoint w)=0 := by
  rw [hessian_mixed_coupling hN c hc hdeg]
  simp only [hu,hv,mul_zero,zero_mul,add_zero]

lemma own_value_hessian_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x u v : Vector N) (hu : inner ℝ u x=0) (hv : inner ℝ v x=0)
    (e : Fin m → Vector N) (w : ValueObservationSpace m) :
    flatJetCLM c 2 x ![u,v] ((singleValueObservation c x e).adjoint w)=0 := by
  rw [← mixed_adjoint_embedValue]
  exact own_mixed_hessian_zero hN c hc hdeg x u v hu hv e (embedValueMixed w)

/-- Literal scalar conditional Hessian mean, uniformly bounded after the
true target sqrt N scaling cancels the genuine covariance 1/sqrt N. -/
theorem mixed_lift_hessian_bound {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (htanu : inner ℝ u x=0) (htanv : inner ℝ v x=0)
    (e f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (w : WithLp 2 (MixedObservationSpace m×MixedObservationSpace m))
    {δ M : ℝ} (hδ : 0 < δ) (_hM : 0 ≤ M)
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f))).inverse‖ ≤ 1/δ)
    (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) (hr : |overlap x y| ≤ 1) :
    |flatJetCLM c 2 x ![u,v] (lift (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)) w)| ≤
      (7*profileBound c*M/δ)*|overlap x y| := by
  have hL:=profileBound_pos c
  let A:=pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)
  let z:=(gram A).inverse w
  have hz : ‖z.snd‖ ≤ (1/δ)*‖w‖ :=
    (WithLp.norm_snd_le _ z).trans (((gram A).inverse.le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hinv (norm_nonneg w)))
  have heq : flatJetCLM c 2 x ![u,v] (lift A w)=
      flatJetCLM c 2 x ![u,v] ((singleMixedObservation c y f).adjoint z.snd) := by
    rw [lift,ContinuousLinearMap.comp_apply]
    change flatJetCLM c 2 x ![u,v] (A.adjoint z)=_
    rw [pairHilbert_adjoint,map_add,own_mixed_hessian_zero hN c hc
      (fun p hp => by have hh:=hdeg p hp;omega) x u v htanu htanv,zero_add]
  rw [heq]
  calc
    _ ≤ (7*profileBound c*|overlap x y|/Real.sqrt (N:ℝ))*‖z.snd‖ :=
      hessian_mixed_bound hN c hc hdeg x y u v hx hy hu hv f hf z.snd hr
    _ ≤ (7*profileBound c*|overlap x y|/Real.sqrt (N:ℝ))*((1/δ)*‖w‖) := by
      gcongr
    _ ≤ (7*profileBound c*|overlap x y|/Real.sqrt (N:ℝ))*((1/δ)*(M*Real.sqrt (N:ℝ))) := by
      gcongr
    _ = _ := by field_simp

/-- The proper value-only pair has the identical actual mean bound. -/
theorem value_lift_hessian_bound {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (htanu : inner ℝ u x=0) (htanv : inner ℝ v x=0)
    (e f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (w : WithLp 2 (ValueObservationSpace m×ValueObservationSpace m))
    {δ M : ℝ} (hδ : 0 < δ) (_hM : 0 ≤ M)
    (hinv : ‖(gram (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))).inverse‖ ≤ 1/δ)
    (hw : ‖w‖ ≤ M*Real.sqrt (N:ℝ)) (hr : |overlap x y| ≤ 1) :
    |flatJetCLM c 2 x ![u,v] (lift (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)) w)| ≤
      (7*profileBound c*M/δ)*|overlap x y| := by
  have hL:=profileBound_pos c
  let A:=pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)
  let z:=(gram A).inverse w
  have hz : ‖z.snd‖ ≤ (1/δ)*‖w‖ :=
    (WithLp.norm_snd_le _ z).trans (((gram A).inverse.le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hinv (norm_nonneg w)))
  have heq : flatJetCLM c 2 x ![u,v] (lift A w)=
      flatJetCLM c 2 x ![u,v] ((singleValueObservation c y f).adjoint z.snd) := by
    rw [lift,ContinuousLinearMap.comp_apply]
    change flatJetCLM c 2 x ![u,v] (A.adjoint z)=_
    rw [pairHilbert_adjoint,map_add,own_value_hessian_zero hN c hc
      (fun p hp => by have hh:=hdeg p hp;omega) x u v htanu htanv,zero_add]
  rw [heq]
  calc
    _ ≤ (7*profileBound c*|overlap x y|/Real.sqrt (N:ℝ))*‖z.snd‖ :=
      hessian_value_bound hN c hc hdeg x y u v hx hy hu hv f hf z.snd hr
    _ ≤ (7*profileBound c*|overlap x y|/Real.sqrt (N:ℝ))*((1/δ)*‖w‖) := by
      gcongr
    _ ≤ (7*profileBound c*|overlap x y|/Real.sqrt (N:ℝ))*((1/δ)*(M*Real.sqrt (N:ℝ))) := by
      gcongr
    _ = _ := by field_simp

end
end SlowEquilibration.PairHessianMean
