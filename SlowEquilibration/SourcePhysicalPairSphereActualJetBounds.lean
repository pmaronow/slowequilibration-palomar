-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereThirdGeometry

/-! Literal sphere-jet bounds, uniformly over the physical sphere, on the
actual ordered tensor regularity event. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem source_ordered_sphere_jet_bounds {N P:ℕ} (hN:0<N)
    (c:Degree P→ℝ) {K:ℝ} (hK:0 ≤ K) (J:Disorder N P)
    (hJ:J ∈ sourcePosteriorOrderedRegularity K) (x:Vector N) (hx:‖x‖^2=(N:ℝ)) :
    ‖surfaceGradient (field c J) x‖ ≤ sourcePosteriorDerivativeConstant c K*Real.sqrt N ∧
    ‖sourceSphereHessianExtension c J x‖ ≤ 2*sourcePosteriorDerivativeConstant c K ∧
    ‖sourceSphereThirdExtension c J x‖ ≤ 9*sourcePosteriorDerivativeConstant c K/Real.sqrt N:=by
  let L:=sourcePosteriorDerivativeConstant c K
  have hL:0<L:=sourcePosteriorDerivativeConstant_pos c hK
  have hNr:(0:ℝ)<N:=Nat.cast_pos.mpr hN
  have hr:0<Real.sqrt (N:ℝ):=Real.sqrt_pos.mpr hNr
  have hs:Real.sqrt (N:ℝ)^2=(N:ℝ):=Real.sq_sqrt hNr.le
  have hnorm:‖x‖=Real.sqrt (N:ℝ):=SphericalAging.LandscapeDerivatives.sphere_norm x hx
  have hx':OnSphere x:=by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  have hP:‖tangentProjection x‖ ≤ 1:=tangentProjection_norm_le hN.ne' x hx'
  obtain ⟨_,hg,hH,hT⟩:=source_posterior_ordered_ball_bounds (by omega) c K J hJ x hnorm.le
  have hD:‖fderiv ℝ (gradient (field c J)) x‖ ≤ L:=by
    simpa only [SphericalAging.LandscapeDerivatives.gradient_derivative_norm,L] using hH
  have hLambda:|radialMultiplier (field c J) x| ≤ L:=by
    rw [radialMultiplier,abs_div,abs_of_pos hNr]
    apply (div_le_iff₀ hNr).mpr
    calc
      _ ≤ ‖x‖*‖gradient (field c J) x‖:=abs_real_inner_le_norm _ _
      _ ≤ Real.sqrt (N:ℝ)*(L*Real.sqrt N):=by rw [hnorm];exact mul_le_mul_of_nonneg_left hg hr.le
      _ = _:=by rw [show Real.sqrt (N:ℝ)*(L*Real.sqrt N)=L*Real.sqrt N^2 by ring,hs]
  have hDP:‖fderiv ℝ (fun y:Vector N=>tangentProjection y) x‖ ≤ 2/Real.sqrt N:=by
    have hb:=source_tangentProjection_fderiv_norm_le x
    rw [hnorm] at hb
    have he:2*Real.sqrt (N:ℝ)/(N:ℝ)=2/Real.sqrt N:=by
      apply (eq_div_iff hr.ne').mpr
      calc
        _ = 2*Real.sqrt (N:ℝ)^2/(N:ℝ):=by ring
        _ = _:=by rw [hs];field_simp
    exact hb.trans_eq he
  have hDLambda:‖fderiv ℝ (radialMultiplier (field c J)) x‖ ≤ 2*L/Real.sqrt N:=by
    have hb:=source_radialMultiplier_fderiv_norm_le c J x
    calc
      _ ≤ (‖gradient (field c J) x‖+‖x‖*‖fderiv ℝ (gradient (field c J)) x‖)/(N:ℝ):=hb
      _ ≤ (L*Real.sqrt N+Real.sqrt N*L)/(N:ℝ):=by
        apply div_le_div_of_nonneg_right _ hNr.le
        exact add_le_add hg (by rw [hnorm];exact mul_le_mul_of_nonneg_left hD hr.le)
      _ = _:=by
        apply (eq_div_iff hr.ne').mpr
        calc
          _ = 2*L*Real.sqrt (N:ℝ)^2/(N:ℝ):=by ring
          _ = _:=by rw [hs];field_simp
  have hPHP:‖(tangentProjection x).comp ((fderiv ℝ (gradient (field c J)) x).comp (tangentProjection x))‖ ≤ L:=by
    calc
      _ ≤ ‖tangentProjection x‖*‖(fderiv ℝ (gradient (field c J)) x).comp (tangentProjection x)‖:=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(fderiv ℝ (gradient (field c J)) x).comp (tangentProjection x)‖:=
        mul_le_of_le_one_left (norm_nonneg _) hP
      _ ≤ ‖fderiv ℝ (gradient (field c J)) x‖*‖tangentProjection x‖:=ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ L:=(mul_le_of_le_one_right (norm_nonneg _) hP).trans hD
  have hLambdaP:‖radialMultiplier (field c J) x • tangentProjection x‖ ≤ L:=by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) hP).trans hLambda
  refine ⟨?_,?_,?_⟩
  · exact ((tangentProjection x).le_opNorm _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hP).trans hg)
  · rw [sourceSphereHessianExtension_eq_ambient hN.ne' c J x hx]
    exact (norm_sub_le _ _).trans ((add_le_add hPHP hLambdaP).trans_eq (by ring))
  · apply (sourceSphereThirdExtension_norm_le hN.ne' c J x hx).trans
    apply (sourceSphereAmbientHessianExtension_fderiv_norm_le c J x hP).trans
    calc
      _ ≤ 2*(2/Real.sqrt N)*L+L/Real.sqrt N+2*L/Real.sqrt N+L*(2/Real.sqrt N):=by
        apply add_le_add
        · apply add_le_add
          · apply add_le_add
            · exact mul_le_mul (mul_le_mul_of_nonneg_left hDP (by norm_num)) hD
                (norm_nonneg _) (by positivity)
            · exact hT
          · exact hDLambda
        · exact mul_le_mul hLambda hDP (ContinuousLinearMap.opNorm_nonneg
            (fderiv ℝ (fun y:Vector N=>tangentProjection y) x)) hL.le
      _ = _:=by ring

end
end SlowEquilibration.PairConditionalDeterminantMoments
