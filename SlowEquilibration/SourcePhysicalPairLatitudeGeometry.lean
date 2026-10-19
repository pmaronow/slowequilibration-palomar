-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPosteriorAmbientBounds
public import SlowEquilibration.SphericalLatitudeMesh
public import SlowEquilibration.IntrinsicHessianLaw
public import Mathlib.Analysis.Calculus.MeanValue

/-! The actual complete tangent latitude parametrization and whole-ball
Hamiltonian modulus on the posterior ordered-tensor regularity event. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm IntrinsicHessianLaw
open Set Metric
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceLatitudeIsometry {n:ℕ} (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)) :
    Vector n→ₗᵢ[ℝ]Vector (n+1):=
  (tangentPlane u).subtypeₗᵢ.comp (tangentBasis u hu).repr.symm.toLinearIsometry

lemma sourceLatitudeIsometry_orthogonal {n:ℕ} (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (v:Vector n) : inner ℝ (sourceLatitudeIsometry u hu v) u=0:=by
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp
    ((tangentBasis u hu).repr.symm v).property

lemma sourceLatitudeIsometry_reconstruct {n:ℕ} (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (v:tangentPlane u) : sourceLatitudeIsometry u hu ((tangentBasis u hu).repr v)=v:=by
  change ((tangentBasis u hu).repr.symm ((tangentBasis u hu).repr v):Vector (n+1))=v
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem source_ordered_field_dist_le {N P:ℕ} (hN:0<N) (c:Degree P→ℝ)
    (K:ℝ) (J:Disorder N P) (hJ:J ∈ sourcePosteriorOrderedRegularity K)
    (x y:Vector N) (hx:‖x‖^2=(N:ℝ)) (hy:‖y‖^2=(N:ℝ)) :
    |field c J x-field c J y| ≤ sourcePosteriorDerivativeConstant c K*Real.sqrt N*‖x-y‖:=by
  have hb:∀ z ∈ closedBall (0:Vector N) (Real.sqrt N),
      ‖fderiv ℝ (field c J) z‖ ≤ sourcePosteriorDerivativeConstant c K*Real.sqrt N:=by
    intro z hz
    have hz':‖z‖ ≤ Real.sqrt N:=by simpa only [mem_closedBall,dist_zero_right] using hz
    have hh:=(source_posterior_ordered_ball_bounds (by omega) c K J hJ z hz').2.1
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hh
  have hxm:x ∈ closedBall (0:Vector N) (Real.sqrt N):=by
    simp only [mem_closedBall,dist_zero_right]
    exact (SphericalAging.LandscapeDerivatives.sphere_norm x hx).le
  have hym:y ∈ closedBall (0:Vector N) (Real.sqrt N):=by
    simp only [mem_closedBall,dist_zero_right]
    exact (SphericalAging.LandscapeDerivatives.sphere_norm y hy).le
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _=>(field_contDiff c J).differentiable (by simp) z) hb
    (convex_closedBall (0:Vector N) (Real.sqrt N)) hym hxm

theorem source_ordered_latitude_field_modulus {n P:ℕ} (hn:1 ≤ n)
    (c:Degree P→ℝ) (K:ℝ) (hK:0 ≤ K) (J:Disorder (n+1) P)
    (hJ:J ∈ sourcePosteriorOrderedRegularity K) (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (e:Vector n→ₗᵢ[ℝ]Vector (n+1)) (he:∀ v,inner ℝ (e v) u=0)
    {q r:ℝ} (hq:|q| ≤ 1) (hr:|r| ≤ 1) (x:Vector n) (hx:‖x‖^2=(n:ℝ)) :
    |field c J (latitudeMap u e q x)-field c J (latitudeMap u e r x)| ≤
      2*sourcePosteriorDerivativeConstant c K*(n+1:ℕ)*Real.sqrt |q-r|:=by
  have hf:=source_ordered_field_dist_le (by omega) c K J hJ
    (latitudeMap u e q x) (latitudeMap u e r x)
    (latitudeMap_norm_sq hn u hu e he hq x hx) (latitudeMap_norm_sq hn u hu e he hr x hx)
  have hh:(sourcePosteriorDerivativeConstant c K*Real.sqrt (n+1:ℕ))*
      ‖latitudeMap u e q x-latitudeMap u e r x‖ ≤
      (sourcePosteriorDerivativeConstant c K*Real.sqrt (n+1:ℕ))*
        (2*Real.sqrt (n+1:ℕ)*Real.sqrt |q-r|):=
    mul_le_mul_of_nonneg_left (latitudeMap_dist_le hn u hu e he hq hr x hx)
      (mul_nonneg (sourcePosteriorDerivativeConstant_pos c hK).le (Real.sqrt_nonneg _))
  exact hf.trans (hh.trans_eq (by
    rw [show (sourcePosteriorDerivativeConstant c K*Real.sqrt (n+1:ℕ))*
      (2*Real.sqrt (n+1:ℕ)*Real.sqrt |q-r|)=
      2*sourcePosteriorDerivativeConstant c K*(Real.sqrt (n+1:ℕ)*Real.sqrt (n+1:ℕ))*Real.sqrt |q-r| by ring,
      Real.mul_self_sqrt (by positivity)]))

end
end SlowEquilibration.PairConditionalDeterminantMoments
