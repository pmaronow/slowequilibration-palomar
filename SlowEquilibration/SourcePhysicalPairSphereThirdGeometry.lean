-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereAmbientJetBounds

/-! The literal projected derivative of the actual covariant sphere Hessian
is the projected derivative of its ambient Hessian-minus-radial extension.
Every projection is a contraction on the physical sphere. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma sourceSphereHessianExtension_contDiff {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) :
    ContDiff ℝ ⊤ (sourceSphereHessianExtension c J):=by
  simpa only [Function.comp_def,id_eq] using
    (sourceSphereHessianExtension_joint_contDiff c).comp (contDiff_const.prodMk contDiff_id)

lemma sourceSphereHessianExtension_tangent_fderiv {N P:ℕ} (hN:N≠0) (c:Degree P→ℝ)
    (J:Disorder N P) (x:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    (fderiv ℝ (sourceSphereHessianExtension c J) x).comp (tangentProjection x)=
      (fderiv ℝ (sourceSphereAmbientHessianExtension c J) x).comp (tangentProjection x):=by
  have hx':OnSphere x:=by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  apply ContinuousLinearMap.ext
  intro v
  exact source_tangent_fderiv_eq_of_agree_on_sphere hN _ _ x (tangentProjection x v) hx'
    (by simpa only [tangentProjection_apply] using projection_tangent hN x v hx')
    ((sourceSphereHessianExtension_contDiff c J).differentiable (by simp) x)
    ((sourceSphereAmbientHessianExtension_contDiff c J).differentiable (by simp) x)
    (fun y hy=>sourceSphereHessianExtension_eq_ambient hN c J y
      (by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hy))

lemma sourceSphereThirdExtension_eq_ambient {N P:ℕ} (hN:N≠0) (c:Degree P→ℝ)
    (J:Disorder N P) (x:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    sourceSphereThirdExtension c J x=
      (((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N) (tangentProjection x)).comp
        ((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N)).flip (tangentProjection x))).comp
          (fderiv ℝ (sourceSphereAmbientHessianExtension c J) x)).comp (tangentProjection x):=by
  change _=
    ((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N) (tangentProjection x)).comp
      ((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N)).flip (tangentProjection x))).comp
        ((fderiv ℝ (sourceSphereAmbientHessianExtension c J) x).comp (tangentProjection x))
  change ((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N) (tangentProjection x)).comp
      ((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N)).flip (tangentProjection x))).comp
        ((fderiv ℝ (sourceSphereHessianExtension c J) x).comp (tangentProjection x))=_
  rw [sourceSphereHessianExtension_tangent_fderiv hN c J x hx]

lemma sourceSphereThirdExtension_norm_le {N P:ℕ} (hN:N≠0) (c:Degree P→ℝ)
    (J:Disorder N P) (x:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    ‖sourceSphereThirdExtension c J x‖ ≤ ‖fderiv ℝ (sourceSphereAmbientHessianExtension c J) x‖:=by
  have hx':OnSphere x:=by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  have hP:‖tangentProjection x‖ ≤ 1:=tangentProjection_norm_le hN x hx'
  let B:=(ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N))
  have hB:‖B‖ ≤ 1:=ContinuousLinearMap.norm_compL_le ℝ (Vector N) (Vector N) (Vector N)
  have hl:‖B (tangentProjection x)‖ ≤ 1:=
    (B.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hB).trans hP)
  have hr:‖B.flip (tangentProjection x)‖ ≤ 1:=by
    have hb:‖B.flip‖ ≤ 1:=by rw [ContinuousLinearMap.opNorm_flip];exact hB
    exact (B.flip.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hb).trans hP)
  have hL:‖(B (tangentProjection x)).comp (B.flip (tangentProjection x))‖ ≤ 1:=by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      calc
        _ ≤ 1*1:=mul_le_mul hl hr (norm_nonneg _) (by norm_num)
        _ = _:=one_mul _)
  rw [sourceSphereThirdExtension_eq_ambient hN c J x hx]
  calc
    _ ≤ ‖((B (tangentProjection x)).comp (B.flip (tangentProjection x))).comp
        (fderiv ℝ (sourceSphereAmbientHessianExtension c J) x)‖*‖tangentProjection x‖:=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖((B (tangentProjection x)).comp (B.flip (tangentProjection x))).comp
        (fderiv ℝ (sourceSphereAmbientHessianExtension c J) x)‖:=
      mul_le_of_le_one_right (norm_nonneg _) hP
    _ ≤ ‖(B (tangentProjection x)).comp (B.flip (tangentProjection x))‖*
        ‖fderiv ℝ (sourceSphereAmbientHessianExtension c J) x‖:=ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _:=mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg
      (fderiv ℝ (sourceSphereAmbientHessianExtension c J) x)) hL

end
end SlowEquilibration.PairConditionalDeterminantMoments
