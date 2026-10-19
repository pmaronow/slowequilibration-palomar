-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphereHessian
public import SlowEquilibration.SphericalInfiniteWithinJets

/-! Tangential derivatives on the sphere are determined by genuine derivatives
within its closed ball. This includes the covariant Hessian of any C² ambient
representative of the restricted function. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphereHessian
open Set Filter Metric SphericalModel SphericalForm InnerProductSpace
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {N : ℕ}

theorem tangent_derivative_eq_of_within_ball {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hN : N ≠ 0) (f g : Vector N → E) (x v : Vector N) (hx : OnSphere x)
    (hv : inner ℝ x v = 0) (A : Vector N →L[ℝ] E)
    (hf : HasFDerivWithinAt f A (closedBall 0 (Real.sqrt N)) x)
    (hg : DifferentiableAt ℝ g x)
    (he : ∀ y, OnSphere y → f y=g y) : A v=(fderiv ℝ g x) v := by
  let T := tangentRotation x v
  have hT : star T = -T := tangentRotation_skew x v
  have hTx : T x=v := tangentRotation_apply hN x v hx hv
  have hs : ∀ t,OnSphere (operatorFlow T t x) := by
    intro t
    rw [onSphere_iff_norm_sq,operatorFlow_norm T hT t x]
    exact (onSphere_iff_norm_sq x).mp hx
  have hb : ∀ᶠ t : ℝ in 𝓝 0,operatorFlow T t x∈closedBall 0 (Real.sqrt N) := by
    filter_upwards [] with t
    rw [mem_closedBall,dist_zero_right]
    exact le_of_eq ((Real.sqrt_sq (norm_nonneg _)).symm.trans
      (congrArg Real.sqrt ((onSphere_iff_norm_sq _).mp (hs t))))
  have hc := operatorFlow_apply_hasDerivAt T 0 x
  have hfd := hf.comp_hasDerivAt_of_eq 0 hc hb (operatorFlow_zero T x).symm
  have hgd := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (operatorFlow_zero T x).symm
  have heq : (f ∘ fun t => operatorFlow T t x)=(g ∘ fun t => operatorFlow T t x) :=
    funext (fun t => he _ (hs t))
  rw [heq] at hfd
  simpa only [operatorFlow_zero,hTx] using hfd.unique hgd

/-- The Riesz representative of an actual within-ball first derivative,
projected onto the genuine spherical tangent plane. -/
def withinGradient (A : Vector N → (Vector N →L[ℝ] ℝ)) (x : Vector N) : Vector N :=
  tangentProjection x ((InnerProductSpace.toDual ℝ (Vector N)).symm (A x))

theorem surfaceGradient_eq_within (hN : N ≠ 0) (f F : Vector N → ℝ)
    (A : Vector N → (Vector N →L[ℝ] ℝ)) (x : Vector N) (hx : OnSphere x)
    (hf : HasFDerivWithinAt f (A x) (closedBall 0 (Real.sqrt N)) x)
    (hF : DifferentiableAt ℝ F x) (he : ∀ y,OnSphere y → f y=F y) :
    surfaceGradient F x=withinGradient A x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient]
  unfold withinGradient
  rw [(tangentProjection_symmetric x).apply_clm]
  rw [← InnerProductSpace.toDual_apply_apply,LinearIsometryEquiv.apply_symm_apply]
  exact (tangent_derivative_eq_of_within_ball hN f F x (tangentProjection x v) hx
    (by simpa only [tangentProjection_apply] using projection_tangent hN x v hx)
    (A x) hf hF he).symm

theorem withinGradient_norm_le (hN : N ≠ 0)
    (A : Vector N → (Vector N →L[ℝ] ℝ)) (x : Vector N) (hx : OnSphere x) :
    ‖withinGradient A x‖ ≤ ‖A x‖ := by
  unfold withinGradient
  calc
    _ ≤ ‖tangentProjection x‖ * ‖(InnerProductSpace.toDual ℝ (Vector N)).symm (A x)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖A x‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (tangentProjection_norm_le hN x hx) (norm_nonneg _)
    _ = _ := one_mul _

/-- Derivative of the projected within-ball gradient, with its actual curvature
correction. No Hessian bound or extension identity is assumed. -/
theorem intrinsicHessian_eq_within (hN : N ≠ 0) (f F : Vector N → ℝ)
    (hF : ContDiff ℝ 2 F) (A : Vector N → (Vector N →L[ℝ] ℝ))
    (B : Vector N → (Vector N →L[ℝ] (Vector N →L[ℝ] ℝ)))
    (hf : ∀ x,OnSphere x → HasFDerivWithinAt f (A x) (closedBall 0 (Real.sqrt N)) x)
    (hA : ∀ x,OnSphere x → HasFDerivWithinAt A (B x) (closedBall 0 (Real.sqrt N)) x)
    (he : ∀ x,OnSphere x → f x=F x)
    (x : Vector N) (hx : OnSphere x) (v : tangentPlane x) :
    (intrinsicHessian F x v : Vector N)=
      tangentProjection x ((InnerProductSpace.toDual ℝ (Vector N)).symm (B x v)) -
        (A x x/(N:ℝ)) • (v : Vector N) := by
  let R := (InnerProductSpace.toDual ℝ (Vector N)).symm
  let G : Vector N → Vector N := fun y => R (A y)
  have hG := R.hasFDerivAt.comp_hasFDerivWithinAt x (hA x hx)
  have hL := (hasFDerivWithinAt_id x (closedBall 0 (Real.sqrt N))).inner ℝ hG
  have hD := hG.sub ((hL.mul_const (N:ℝ)⁻¹).smul (hasFDerivWithinAt_id x (closedBall 0 (Real.sqrt N))))
  have hgF : ContDiff ℝ 1 (gradient F) := by
    exact R.contDiff.comp (hF.fderiv_right (by norm_num))
  have hsF : ContDiff ℝ 1 (surfaceGradient F) := by
    rw [surfaceGradient_eq]
    exact hgF.sub (((contDiff_id.inner ℝ hgF).div_const (N:ℝ)).smul contDiff_id)
  have hGe : (fun y => G y - (inner ℝ y (G y)/(N:ℝ)) • y)=withinGradient A := by
    funext y
    simp only [withinGradient,tangentProjection_apply,projection,G,R]
  simp only [div_eq_mul_inv] at hGe
  change HasFDerivWithinAt (fun y => G y-(inner ℝ y (G y)*(N:ℝ)⁻¹) • y) _ _ _ at hD
  rw [hGe] at hD
  have hde := tangent_derivative_eq_of_within_ball hN (withinGradient A) (surfaceGradient F)
    x v hx (Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property) _ hD
    (hsF.differentiable (by norm_num) x) (fun y hy =>
      (surfaceGradient_eq_within hN f F A y hy (hf y hy)
        (hF.differentiable (by norm_num) y) he).symm)
  have hπ : tangentProjection x (v : Vector N)=v := by
    rw [tangentProjection_eq_starProjection hN x hx]
    exact (tangentPlane x).starProjection_eq_self_iff.mpr v.property
  have hπx : tangentProjection x x=0 := by
    rw [tangentProjection_apply]
    exact projection_normal_zero hN x hx
  simp only [intrinsicHessian,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
    Submodule.coe_orthogonalProjectionOnto_apply]
  rw [← tangentProjection_eq_starProjection hN x hx,← hde]
  simp only [sub_apply,add_apply,
    _root_.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,id_eq]
  rw [map_sub,map_add,map_smul,map_smul,hπ,hπx,smul_zero,add_zero]
  congr 1
  congr 1
  change (inner ℝ x (R (A x))/(N:ℝ))=(A x x/(N:ℝ))
  rw [real_inner_comm,← InnerProductSpace.toDual_apply_apply,LinearIsometryEquiv.apply_symm_apply]

/-- The genuine spherical Hessian gains only the geometric radial correction
‖Df‖/sqrt(N) compared with the second within-ball derivative. -/
theorem intrinsicHessian_norm_le_within (hN : N ≠ 0) (f F : Vector N → ℝ)
    (hF : ContDiff ℝ 2 F) (A : Vector N → (Vector N →L[ℝ] ℝ))
    (B : Vector N → (Vector N →L[ℝ] (Vector N →L[ℝ] ℝ)))
    (hf : ∀ x,OnSphere x → HasFDerivWithinAt f (A x) (closedBall 0 (Real.sqrt N)) x)
    (hA : ∀ x,OnSphere x → HasFDerivWithinAt A (B x) (closedBall 0 (Real.sqrt N)) x)
    (he : ∀ x,OnSphere x → f x=F x)
    (x : Vector N) (hx : OnSphere x) :
    ‖intrinsicHessian F x‖ ≤ ‖B x‖+‖A x‖/Real.sqrt N := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hsq : Real.sqrt N*Real.sqrt N=(N:ℝ) := Real.mul_self_sqrt hNr.le
  have hxn : ‖x‖=Real.sqrt N :=
    (Real.sqrt_sq (norm_nonneg x)).symm.trans (congrArg Real.sqrt ((onSphere_iff_norm_sq x).mp hx))
  have hr : |A x x/(N:ℝ)| ≤ ‖A x‖/Real.sqrt N := by
    rw [abs_div,abs_of_pos hNr]
    calc
      _ ≤ (‖A x‖*Real.sqrt N)/(N:ℝ) :=
        div_le_div_of_nonneg_right (by simpa only [← Real.norm_eq_abs,hxn] using (A x).le_opNorm x) hNr.le
      _ = _ := by field_simp; rw [Real.sq_sqrt hNr.le]
  apply (intrinsicHessian F x).opNorm_le_bound (by positivity)
  intro v
  change ‖((intrinsicHessian F x) v : Vector N)‖ ≤ _
  rw [intrinsicHessian_eq_within hN f F hF A B hf hA he x hx v]
  calc
    _ ≤ ‖tangentProjection x ((InnerProductSpace.toDual ℝ (Vector N)).symm (B x v))‖+
        ‖(A x x/(N:ℝ)) • (v : Vector N)‖ := norm_sub_le _ _
    _ ≤ ‖B x‖*‖v‖+(‖A x‖/Real.sqrt N)*‖v‖ := by
      apply add_le_add
      · calc
          _ ≤ ‖(InnerProductSpace.toDual ℝ (Vector N)).symm (B x v)‖ := by
            rw [tangentProjection_eq_starProjection hN x hx]
            exact (tangentPlane x).norm_starProjection_apply_le _
          _ = ‖B x v‖ := LinearIsometryEquiv.norm_map _ _
          _ ≤ ‖B x‖*‖v‖ := (B x).le_opNorm v
      · rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    _ = _ := (add_mul _ _ _).symm

end SlowEquilibration.SphereHessian
