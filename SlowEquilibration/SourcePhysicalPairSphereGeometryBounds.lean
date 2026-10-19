-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPosteriorAmbientBounds
public import SlowEquilibration.SourcePhysicalPairSelectionMaxima

/-! Deterministic geometry estimates connecting actual ambient operator
derivatives to the literal covariant sphere-jet regularity event. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped RealInnerProductSpace Topology
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma source_fderiv_clm_comp_norm_le {E F G H:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (c:E→G→L[ℝ]H) (d:E→F→L[ℝ]G) (x:E)
    (hc:DifferentiableAt ℝ c x) (hd:DifferentiableAt ℝ d x) :
    ‖fderiv ℝ (fun y=>(c y).comp (d y)) x‖ ≤
      ‖c x‖*‖fderiv ℝ d x‖+‖d x‖*‖fderiv ℝ c x‖:=by
  rw [fderiv_clm_comp hc hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(c x).comp (fderiv ℝ d x v)+(fderiv ℝ c x v).comp (d x)‖ ≤ _
  calc
    _ ≤ ‖(c x).comp (fderiv ℝ d x v)‖+‖(fderiv ℝ c x v).comp (d x)‖:=norm_add_le _ _
    _ ≤ ‖c x‖*‖fderiv ℝ d x v‖+‖fderiv ℝ c x v‖*‖d x‖:=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ‖c x‖*(‖fderiv ℝ d x‖*‖v‖)+(‖fderiv ℝ c x‖*‖v‖)*‖d x‖:=
      add_le_add (mul_le_mul_of_nonneg_left ((fderiv ℝ d x).le_opNorm v) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right ((fderiv ℝ c x).le_opNorm v) (norm_nonneg _))
    _ = _:=by ring

lemma source_fderiv_clm_apply_norm_le {E F G:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c:E→F→L[ℝ]G) (d:E→F) (x:E)
    (hc:DifferentiableAt ℝ c x) (hd:DifferentiableAt ℝ d x) :
    ‖fderiv ℝ (fun y=>(c y) (d y)) x‖ ≤
      ‖c x‖*‖fderiv ℝ d x‖+‖fderiv ℝ c x‖*‖d x‖:=by
  rw [fderiv_clm_apply hc hd]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (by
      have hh:=(fderiv ℝ c x).flip.le_opNorm (d x)
      simpa only [ContinuousLinearMap.opNorm_flip] using hh))

lemma source_tangentProjection_fderiv_norm_le {N:ℕ} (x:Vector N) :
    ‖fderiv ℝ (fun y:Vector N=>tangentProjection y) x‖ ≤ 2*‖x‖/(N:ℝ):=by
  let S:Vector N→L[ℝ]ℝ→L[ℝ]Vector N:=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Vector N)).toContinuousLinearEquiv.toContinuousLinearMap
  let D:Vector N→L[ℝ]Vector N→L[ℝ]ℝ:=
    (InnerProductSpace.toDual ℝ (Vector N)).toContinuousLinearEquiv.toContinuousLinearMap
  have hS:‖S‖ ≤ 1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    change ‖(ContinuousLinearMap.toSpanSingletonLIE ℝ (Vector N)) v‖ ≤ 1*‖v‖
    rw [(ContinuousLinearMap.toSpanSingletonLIE ℝ (Vector N)).norm_map,one_mul]
  have hD:‖D‖ ≤ 1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    change ‖(InnerProductSpace.toDual ℝ (Vector N)) v‖ ≤ 1*‖v‖
    rw [(InnerProductSpace.toDual ℝ (Vector N)).norm_map,one_mul]
  have he:(fun y:Vector N=>tangentProjection y)=
      (fun y=>ContinuousLinearMap.id ℝ (Vector N)-(1/(N:ℝ)) • ((S y).comp (D y))):=by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    simp only [tangentProjection,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
      InnerProductSpace.rankOne_apply,S,D]
    rfl
  have hd:=source_fderiv_clm_comp_norm_le S D x S.differentiableAt D.differentiableAt
  have hnS:‖S x‖=‖x‖:=(ContinuousLinearMap.toSpanSingletonLIE ℝ (Vector N)).norm_map x
  have hnD:‖D x‖=‖x‖:=(InnerProductSpace.toDual ℝ (Vector N)).norm_map x
  simp only [ContinuousLinearMap.fderiv,hnS,hnD] at hd
  have hf:DifferentiableAt ℝ (fun y=>(S y).comp (D y)) x:=
    S.differentiableAt.clm_comp D.differentiableAt
  have heD:=(hasFDerivAt_const (ContinuousLinearMap.id ℝ (Vector N)) x).sub
    (hf.hasFDerivAt.const_smul (1/(N:ℝ)))
  rw [he]
  change ‖fderiv ℝ ((fun _:Vector N=>ContinuousLinearMap.id ℝ (Vector N))-
    (1/(N:ℝ)) • (fun y=>(S y).comp (D y))) x‖ ≤ _
  rw [heD.fderiv,zero_sub]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖-((1/(N:ℝ)) • (fderiv ℝ (fun y=>(S y).comp (D y)) x v))‖ ≤ _
  rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 1/(N:ℝ) by positivity)]
  calc
    _ ≤ (1/(N:ℝ))*(‖fderiv ℝ (fun y=>(S y).comp (D y)) x‖*‖v‖):=
      mul_le_mul_of_nonneg_left ((fderiv ℝ (fun y=>(S y).comp (D y)) x).le_opNorm v) (by positivity)
    _ ≤ (1/(N:ℝ))*((2*‖x‖)*‖v‖):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      exact hd.trans (by nlinarith [norm_nonneg x])
    _ = _:=by ring

lemma source_tangent_fderiv_eq_of_agree_on_sphere {N:ℕ} {F:Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hN:N≠0)
    (f g:Vector N→F) (x v:Vector N) (hx:OnSphere x)
    (hv:inner ℝ x v=0) (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x)
    (hagree:∀ y,OnSphere y→f y=g y) : fderiv ℝ f x v=fderiv ℝ g x v:=by
  let A:=tangentRotation x v
  have hA:star A = -A:=tangentRotation_skew x v
  have hAx:A x=v:=tangentRotation_apply hN x v hx hv
  have hflowSphere:∀ t,OnSphere (operatorFlow A t x):=by
    intro t
    rw [onSphere_iff_norm_sq,operatorFlow_norm A hA t x]
    exact (onSphere_iff_norm_sq x).mp hx
  have heq:(fun t=>(f-g) (operatorFlow A t x))=(fun _:ℝ=>(0:F)):=by
    funext t
    exact sub_eq_zero.mpr (hagree _ (hflowSphere t))
  have hcurve:=operatorFlow_apply_hasDerivAt A 0 x
  have hcomp:=(hf.sub hg).hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve
    (show x=operatorFlow A 0 x from (operatorFlow_zero A x).symm)
  have hz:fderiv ℝ (f-g) x v=0:=by
    have hc0:HasDerivAt ((f-g) ∘ fun t=>operatorFlow A t x) 0 0:=by
      simpa only [Function.comp_def,heq] using hasDerivAt_const (0:ℝ) (0:F)
    simpa only [operatorFlow_zero,hAx] using hcomp.unique hc0
  rw [fderiv_sub hf hg] at hz
  simpa only [sub_apply,sub_eq_zero] using hz

def sourceSphereAmbientHessianExtension {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) (x:Vector N):
    Vector N→L[ℝ]Vector N:=
  (tangentProjection x).comp ((fderiv ℝ (gradient (field c J)) x).comp (tangentProjection x))-
    radialMultiplier (field c J) x • tangentProjection x

lemma sourceSphereHessianExtension_eq_ambient {N P:ℕ} (hN:N≠0) (c:Degree P→ℝ)
    (J:Disorder N P) (x:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    sourceSphereHessianExtension c J x=sourceSphereAmbientHessianExtension c J x:=by
  have hx':OnSphere x:=by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  have hπ:tangentProjection x=(tangentPlane x).starProjection:=tangentProjection_eq_starProjection hN x hx'
  apply ContinuousLinearMap.ext
  intro v
  let w: tangentPlane x := (tangentPlane x).orthogonalProjectionOnto v
  have hw:(w:Vector N)=tangentProjection x v:=by
    simp only [w,Submodule.coe_orthogonalProjectionOnto_apply,hπ]
  have hp:tangentProjection x (w:Vector N)=w:=by
    rw [hπ]
    exact (tangentPlane x).starProjection_eq_self_iff.mpr w.property
  have he:=intrinsicHessian_apply hN (field c J) x hx'
    ((field_gradient_contDiff c J).differentiable (by simp) x) w
  rw [sourceSphereHessianExtension_intrinsic_apply hN c J x hx w] at he
  simp only [sourceSphereHessianExtension,ContinuousLinearMap.comp_apply,hp] at he
  change tangentProjection x (fderiv ℝ (surfaceGradient (field c J)) x (tangentProjection x v))=_
  rw [←hw]
  simpa only [sourceSphereAmbientHessianExtension,ContinuousLinearMap.comp_apply,sub_apply,smul_apply,hw] using he

end
end SlowEquilibration.PairConditionalDeterminantMoments
