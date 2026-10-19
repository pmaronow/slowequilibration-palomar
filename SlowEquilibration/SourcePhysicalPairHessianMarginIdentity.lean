-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionMaxima
public import SlowEquilibration.PosteriorMaximumDeterminant

/-! The literal all-vector intrinsic Hessian margin follows from strict
negativity after the actual scalar identity shift, in the true complete
tangent basis. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open NegativeDefiniteOperators SphericalMarkedWindows IntrinsicHessianLaw ConditionedIntrinsicHessian
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma sourceHessianMargin_of_shifted_negative {N P:ℕ} (hN:N≠0) (c:Degree P→ℝ)
    (κ:ℝ) (J:Disorder N P) (u:Vector N) (hu:‖u‖^2=(N:ℝ))
    (hNeg:NegativeDefinite (intrinsicHessian (field c J) u+
      κ • ContinuousLinearMap.id ℝ (tangentPlane u))) : sourceHessianMargin c κ J u:=by
  intro v
  have hu':OnSphere u:=by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hu
  let w:tangentPlane u:=(tangentPlane u).orthogonalProjectionOnto v
  have hpv:(w:Vector N)=tangentProjection u v:=by
    simp only [w,Submodule.coe_orthogonalProjectionOnto_apply,
      tangentProjection_eq_starProjection hN u hu']
  have hpw:tangentProjection u (w:Vector N)=w:=by
    rw [tangentProjection_eq_starProjection hN u hu']
    exact (tangentPlane u).starProjection_eq_self_iff.mpr w.property
  have he:sourceSphereHessianExtension c J u v=(intrinsicHessian (field c J) u w:Vector N):=by
    have hh:=sourceSphereHessianExtension_intrinsic_apply hN c J u hu w
    simp only [sourceSphereHessianExtension,ContinuousLinearMap.comp_apply,hpw] at hh
    simpa only [sourceSphereHessianExtension,ContinuousLinearMap.comp_apply,←hpv] using hh.symm
  have hi:inner ℝ (w:Vector N) (intrinsicHessian (field c J) u w:Vector N)=
      inner ℝ v (intrinsicHessian (field c J) u w:Vector N):=
    (tangentPlane u).inner_orthogonalProjectionOnto_eq_of_mem_right (intrinsicHessian (field c J) u w) v
  rw [he,←hi,←hpv]
  by_cases hw:w=0
  · simp [hw]
  · have hh:=hNeg w hw
    change inner ℝ (w:Vector N) ((intrinsicHessian (field c J) u w:Vector N)+κ • (w:Vector N))<0 at hh
    rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq] at hh
    linarith

lemma source_intrinsic_shifted_matrix {n P:ℕ} (c:Degree P→ℝ) (κ:ℝ)
    (J:Disorder (n+1) P) (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)) :
    LinearMap.toMatrix (tangentBasis u hu).toBasis (tangentBasis u hu).toBasis
      (intrinsicHessian (field c J) u+κ • ContinuousLinearMap.id ℝ (tangentPlane u)).toLinearMap=
      intrinsicMatrix c u hu J+κ • (1:Matrix (Fin n) (Fin n) ℝ):=by
  change LinearMap.toMatrix (tangentBasis u hu).toBasis (tangentBasis u hu).toBasis
    ((intrinsicHessian (field c J) u).toLinearMap+κ • LinearMap.id)=_
  rw [map_add,map_smul,LinearMap.toMatrix_id]
  rfl

lemma sourceHessianMargin_of_negative_matrix {n P:ℕ} (c:Degree P→ℝ) (κ:ℝ)
    (J:Disorder (n+1) P) (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (hNeg:NegativeDefinite (OAI.CriticalSK.gaussianMatrixCLM
      (GOEAsymptotics.matrixToGaussian (intrinsicMatrix c u hu J+κ • 1)))) :
    sourceHessianMargin c κ J u:=by
  apply sourceHessianMargin_of_shifted_negative (by omega) c κ J u hu
  have hh:=(negativeDefinite_toMatrix_iff (tangentBasis u hu)
    (intrinsicHessian (field c J) u+κ • ContinuousLinearMap.id ℝ (tangentPlane u)))
  rw [source_intrinsic_shifted_matrix c κ J u hu] at hh
  exact hh.mp hNeg

end
end SlowEquilibration.PairConditionalDeterminantMoments
