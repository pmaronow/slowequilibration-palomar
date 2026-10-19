-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereRegularityPointBounds

/-! Exact slope, curvature, and covariant cubic identities along actual
round-sphere great circles. These discharge the scalar critical collar. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma source_tangentProjection_fixed {N:ℕ} (x v:Vector N) (hv:inner ℝ x v=0) :
    tangentProjection x v=v:=by simp only [tangentProjection_apply,projection,hv,zero_div,zero_smul,sub_zero]

lemma source_tangentProjection_radial_zero {N:ℕ} (hN:0<N) (x:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    tangentProjection x x=0:=by
  have hNr:(0:ℝ)<N:=Nat.cast_pos.mpr hN
  simp only [tangentProjection_apply,projection,real_inner_self_eq_norm_sq,hx,
    div_self hNr.ne',one_smul,sub_self]

lemma source_inner_tangentProjection {N:ℕ} (x v w:Vector N) (hv:inner ℝ x v=0) :
    inner ℝ v (tangentProjection x w)=inner ℝ v w:=by
  have hvr:inner ℝ v x=0:=by rw [real_inner_comm];exact hv
  simp only [tangentProjection_apply,projection,inner_sub_right,real_inner_smul_right,hvr,mul_zero,sub_zero]

lemma sourceSphereHessianExtension_radial_zero {N P:ℕ} (hN:0<N) (c:Degree P→ℝ)
    (J:Disorder N P) (x:Vector N) (hx:‖x‖^2=(N:ℝ)) : sourceSphereHessianExtension c J x x=0:=by
  simp only [sourceSphereHessianExtension,ContinuousLinearMap.comp_apply,
    source_tangentProjection_radial_zero hN x hx,map_zero]

lemma sourceSphereHessianExtension_range_tangent {N P:ℕ} (hN:0<N) (c:Degree P→ℝ)
    (J:Disorder N P) (x v:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    inner ℝ x (sourceSphereHessianExtension c J x v)=0:=by
  simp only [sourceSphereHessianExtension,ContinuousLinearMap.comp_apply,tangentProjection_apply]
  exact projection_tangent hN.ne' x _ (by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx)

lemma sourceSphereThirdExtension_tangent_apply {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P)
    (x v w:Vector N) (hv:inner ℝ x v=0) (hw:inner ℝ x w=0) :
    sourceSphereThirdExtension c J x v w=
      tangentProjection x ((fderiv ℝ (sourceSphereHessianExtension c J) x v) w):=by
  change tangentProjection x ((fderiv ℝ (sourceSphereHessianExtension c J) x (tangentProjection x v))
    (tangentProjection x w))=_
  rw [source_tangentProjection_fixed x v hv,source_tangentProjection_fixed x w hw]

def sourceSphereGeodesicSlope {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) (u v:Vector N) (t:ℝ):ℝ:=
  inner ℝ (sourceSphereGeodesicVelocity u v t) (surfaceGradient (field c J) (sourceSphereGeodesic u v t))

def sourceSphereGeodesicCurvature {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) (u v:Vector N) (t:ℝ):ℝ:=
  inner ℝ (sourceSphereGeodesicVelocity u v t)
    (sourceSphereHessianExtension c J (sourceSphereGeodesic u v t) (sourceSphereGeodesicVelocity u v t))

def sourceSphereGeodesicCubic {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) (u v:Vector N) (t:ℝ):ℝ:=
  inner ℝ (sourceSphereGeodesicVelocity u v t)
    (sourceSphereThirdExtension c J (sourceSphereGeodesic u v t)
      (sourceSphereGeodesicVelocity u v t) (sourceSphereGeodesicVelocity u v t))

theorem sourceSphereGeodesicSlope_hasDerivAt {N P:ℕ} (hN:0<N) (c:Degree P→ℝ) (J:Disorder N P)
    (u v:Vector N) (hu:‖u‖^2=(N:ℝ)) (hv:‖v‖^2=(N:ℝ)) (huv:inner ℝ u v=0) (t:ℝ) :
    HasDerivAt (sourceSphereGeodesicSlope c J u v) (sourceSphereGeodesicCurvature c J u v t) t:=by
  let x:=sourceSphereGeodesic u v t
  let d:=sourceSphereGeodesicVelocity u v t
  have hx:‖x‖^2=(N:ℝ):=sourceSphereGeodesic_norm_sq u v hu hv huv t
  have hxd:inner ℝ x d=0:=sourceSphereGeodesic_tangent u v hu hv huv t
  have hG:ContDiff ℝ ⊤ (surfaceGradient (field c J)):=by
    simpa only [Function.comp_def,id_eq] using
      (source_surfaceGradient_joint_contDiff c).comp (contDiff_const.prodMk contDiff_id)
  have hcurve:=sourceSphereGeodesic_hasDerivAt u v t
  have hvel:=sourceSphereGeodesicVelocity_hasDerivAt u v t
  have hgrad:=(hG.differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt t hcurve
  have H:=hvel.inner ℝ hgrad
  have hRad:inner ℝ (-x) (surfaceGradient (field c J) x)=0:=by
    rw [inner_neg_left,real_inner_comm,inner_surfaceGradient,
      source_tangentProjection_radial_zero hN x hx,map_zero,neg_zero]
  have hH:inner ℝ d (sourceSphereHessianExtension c J x d)=
      inner ℝ d (fderiv ℝ (surfaceGradient (field c J)) x d):=by
    simp only [sourceSphereHessianExtension,ContinuousLinearMap.comp_apply,source_tangentProjection_fixed x d hxd]
    exact source_inner_tangentProjection x d _ hxd
  convert H using 1
  · rfl
  · change inner ℝ d (sourceSphereHessianExtension c J x d)=
      inner ℝ d (fderiv ℝ (surfaceGradient (field c J)) x d)+inner ℝ (-x) (surfaceGradient (field c J) x)
    rw [hRad,add_zero,hH]

theorem sourceSphereGeodesicCurvature_hasDerivAt {N P:ℕ} (hN:0<N) (c:Degree P→ℝ) (J:Disorder N P)
    (u v:Vector N) (hu:‖u‖^2=(N:ℝ)) (hv:‖v‖^2=(N:ℝ)) (huv:inner ℝ u v=0) (t:ℝ) :
    HasDerivAt (sourceSphereGeodesicCurvature c J u v) (sourceSphereGeodesicCubic c J u v t) t:=by
  let x:=sourceSphereGeodesic u v t
  let d:=sourceSphereGeodesicVelocity u v t
  have hx:‖x‖^2=(N:ℝ):=sourceSphereGeodesic_norm_sq u v hu hv huv t
  have hxd:inner ℝ x d=0:=sourceSphereGeodesic_tangent u v hu hv huv t
  have hcurve:=sourceSphereGeodesic_hasDerivAt u v t
  have hvel:=sourceSphereGeodesicVelocity_hasDerivAt u v t
  have hess:=((sourceSphereHessianExtension_contDiff c J).differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt t hcurve
  have happ:=hess.clm_apply hvel
  have H:=hvel.inner ℝ happ
  have hRad:=sourceSphereHessianExtension_radial_zero hN c J x hx
  have hRan:=sourceSphereHessianExtension_range_tangent hN c J x d hx
  have hT:inner ℝ d (sourceSphereThirdExtension c J x d d)=
      inner ℝ d ((fderiv ℝ (sourceSphereHessianExtension c J) x d) d):=by
    rw [sourceSphereThirdExtension_tangent_apply c J x d d hxd hxd]
    exact source_inner_tangentProjection x d _ hxd
  convert H using 1
  · rfl
  · change inner ℝ d (sourceSphereThirdExtension c J x d d)=
      inner ℝ d ((fderiv ℝ (sourceSphereHessianExtension c J) x d) d+sourceSphereHessianExtension c J x (-x))+
        inner ℝ (-x) (sourceSphereHessianExtension c J x d)
    rw [map_neg,hRad,neg_zero,add_zero,inner_neg_left,hRan,neg_zero,add_zero,hT]

theorem sourceSphereGeodesicCubic_abs_le {N P:ℕ} (hN:0<N) (c:Degree P→ℝ) (J:Disorder N P)
    (u v:Vector N) (hu:‖u‖^2=(N:ℝ)) (hv:‖v‖^2=(N:ℝ)) (huv:inner ℝ u v=0)
    {C:ℝ} (hC:sourceSphereRegularity c J ≤ C) (t:ℝ) :
    |sourceSphereGeodesicCubic c J u v t| ≤ C*(N:ℝ):=by
  let x:=sourceSphereGeodesic u v t
  let d:=sourceSphereGeodesicVelocity u v t
  let T:=sourceSphereThirdExtension c J x
  have hx:‖x‖^2=(N:ℝ):=sourceSphereGeodesic_norm_sq u v hu hv huv t
  have hd:‖d‖^2=(N:ℝ):=sourceSphereGeodesicVelocity_norm_sq u v hu hv huv t
  have hdNorm:‖d‖=Real.sqrt (N:ℝ):=SphericalAging.LandscapeDerivatives.sphere_norm d hd
  have hT:‖T‖ ≤ C/Real.sqrt (N:ℝ):=sourceSphereRegularity_third_point_bound hN c J hC x hx
  have hs:0<Real.sqrt (N:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  change |inner ℝ d (T d d)| ≤ _
  calc
    _ ≤ ‖d‖*‖T d d‖:=abs_real_inner_le_norm _ _
    _ ≤ ‖d‖*(‖T d‖*‖d‖):=
      mul_le_mul_of_nonneg_left ((T d).le_opNorm d) (norm_nonneg d)
    _ ≤ ‖d‖*((‖T‖*‖d‖)*‖d‖):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (T.le_opNorm d) (norm_nonneg d)) (norm_nonneg d)
    _ ≤ ‖d‖*((C/Real.sqrt (N:ℝ)*‖d‖)*‖d‖):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hT (norm_nonneg d)) (norm_nonneg d)) (norm_nonneg d)
    _ = C*(N:ℝ):=by
      rw [hdNorm,div_mul_cancel₀ _ hs.ne']
      calc
        _=C*(Real.sqrt (N:ℝ))^2:=by ring
        _=C*(N:ℝ):=by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

end
end SlowEquilibration.PairConditionalDeterminantMoments
