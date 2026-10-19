-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereGeometryBounds
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! True ambient derivative estimates for the alternate sphere Hessian
extension, which agrees with the literal covariant extension on the sphere. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma source_fderiv_smul_norm_le {E F:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c:E→ℝ) (f:E→F) (x:E)
    (hc:DifferentiableAt ℝ c x) (hf:DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (fun y=>c y • f y) x‖ ≤
      |c x| * ‖fderiv ℝ f x‖+‖fderiv ℝ c x‖*‖f x‖:=by
  rw [show (fun y=>c y • f y)=c • f by rfl,fderiv_smul hc hf]
  exact (norm_add_le _ _).trans (by
    rw [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply])

lemma source_gradient_second_fderiv_norm_le {N P:ℕ} (c:Degree P→ℝ)
    (J:Disorder N P) (x:Vector N) :
    ‖fderiv ℝ (fderiv ℝ (gradient (field c J))) x‖ ≤ ‖iteratedFDeriv ℝ 3 (field c J) x‖:=by
  let L: (Vector N→L[ℝ]ℝ)→L[ℝ]Vector N:=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL:‖L‖ ≤ 1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    change ‖(InnerProductSpace.toDual ℝ (Vector N)).symm v‖ ≤ 1*‖v‖
    rw [(InnerProductSpace.toDual ℝ (Vector N)).symm.norm_map,one_mul]
  have hdiff:ContDiff ℝ ⊤ (fderiv ℝ (field c J)):=
    (field_contDiff c J).fderiv_right (by simp)
  have hh:=L.norm_iteratedFDeriv_comp_left (x:=x) hdiff.contDiffAt (n:=2) (by simp)
  rw [←norm_iteratedFDeriv_one (fderiv ℝ (gradient (field c J))),norm_iteratedFDeriv_fderiv]
  change ‖iteratedFDeriv ℝ 2 (L ∘ fderiv ℝ (field c J)) x‖ ≤ _
  exact hh.trans (by
    rw [norm_iteratedFDeriv_fderiv]
    exact mul_le_of_le_one_left (norm_nonneg _) hL)

lemma source_radialMultiplier_contDiff {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) :
    ContDiff ℝ ⊤ (radialMultiplier (field c J)):=
  (contDiff_id.inner ℝ (field_gradient_contDiff c J)).div_const _

lemma source_radialMultiplier_fderiv_norm_le {N P:ℕ} (c:Degree P→ℝ)
    (J:Disorder N P) (x:Vector N) :
    ‖fderiv ℝ (radialMultiplier (field c J)) x‖ ≤
      (‖gradient (field c J) x‖+‖x‖*‖fderiv ℝ (gradient (field c J)) x‖)/(N:ℝ):=by
  have hg:DifferentiableAt ℝ (gradient (field c J)) x:=
    (field_gradient_contDiff c J).differentiable (by simp) x
  have hi:DifferentiableAt ℝ (fun y:Vector N=>inner ℝ y (gradient (field c J) y)) x:=
    differentiableAt_id.inner ℝ hg
  have hn:‖fderiv ℝ (fun y:Vector N=>inner ℝ y (gradient (field c J) y)) x‖ ≤
      ‖gradient (field c J) x‖+‖x‖*‖fderiv ℝ (gradient (field c J)) x‖:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have he:=fderiv_inner_apply ℝ (show DifferentiableAt ℝ (id:Vector N→Vector N) x from differentiableAt_id) hg v
    simp only [id_eq,fderiv_id,ContinuousLinearMap.id_apply] at he
    rw [Real.norm_eq_abs,he]
    calc
      _ ≤ |inner ℝ x (fderiv ℝ (gradient (field c J)) x v)|+|inner ℝ v (gradient (field c J) x)|:=abs_add_le _ _
      _ ≤ ‖x‖*(‖fderiv ℝ (gradient (field c J)) x‖*‖v‖)+‖v‖*‖gradient (field c J) x‖:=
        add_le_add ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left ((fderiv ℝ (gradient (field c J)) x).le_opNorm v) (norm_nonneg _)))
          (abs_real_inner_le_norm _ _)
      _ = _:=by ring
  have he:(radialMultiplier (field c J):Vector N→ℝ)=
      (1/(N:ℝ)) • (fun y=>inner ℝ y (gradient (field c J) y)):=by
    funext y
    simp only [radialMultiplier,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,fderiv_const_smul hi,norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 1/(N:ℝ) by positivity)]
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by ring)

lemma sourceSphereAmbientHessianExtension_contDiff {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) :
    ContDiff ℝ ⊤ (sourceSphereAmbientHessianExtension c J):=by
  have hP:=source_tangentProjection_contDiff N
  have hD:ContDiff ℝ ⊤ (fderiv ℝ (gradient (field c J))):=
    (field_gradient_contDiff c J).fderiv_right (by simp)
  exact (hP.clm_comp (hD.clm_comp hP)).sub ((source_radialMultiplier_contDiff c J).smul hP)

lemma sourceSphereAmbientHessianExtension_fderiv_norm_le {N P:ℕ} (c:Degree P→ℝ)
    (J:Disorder N P) (x:Vector N) (hP:‖tangentProjection x‖ ≤ 1) :
    ‖fderiv ℝ (sourceSphereAmbientHessianExtension c J) x‖ ≤
      2*‖fderiv ℝ (fun y:Vector N=>tangentProjection y) x‖*‖fderiv ℝ (gradient (field c J)) x‖+
      ‖iteratedFDeriv ℝ 3 (field c J) x‖+‖fderiv ℝ (radialMultiplier (field c J)) x‖+
      |radialMultiplier (field c J) x| * ‖fderiv ℝ (fun y:Vector N=>tangentProjection y) x‖:=by
  let P:Vector N→Vector N→L[ℝ]Vector N:=fun y=>tangentProjection y
  let D:=fderiv ℝ (gradient (field c J))
  have hpd:DifferentiableAt ℝ P x:=(source_tangentProjection_contDiff N).differentiable (by simp) x
  have hdd:DifferentiableAt ℝ D x:=
    ((field_gradient_contDiff c J).fderiv_right (m:=⊤) (by simp)).differentiable (by simp) x
  have hld:DifferentiableAt ℝ (fun y=>(P y).comp ((D y).comp (P y))) x:=
    hpd.clm_comp (hdd.clm_comp hpd)
  have hrd:DifferentiableAt ℝ (fun y=>radialMultiplier (field c J) y • P y) x:=
    ((source_radialMultiplier_contDiff c J).differentiable (by simp) x).smul hpd
  have hb:=source_fderiv_clm_comp_norm_le P (fun y=>(D y).comp (P y)) x hpd (hdd.clm_comp hpd)
  have hi:=source_fderiv_clm_comp_norm_le D P x hdd hpd
  have hc:‖(D x).comp (P x)‖ ≤ ‖D x‖:=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hP)
  have hl:‖fderiv ℝ (fun y=>(P y).comp ((D y).comp (P y))) x‖ ≤
      2*‖fderiv ℝ P x‖*‖D x‖+‖iteratedFDeriv ℝ 3 (field c J) x‖:=by
    have hj:=source_gradient_second_fderiv_norm_le c J x
    calc
      _ ≤ ‖fderiv ℝ (fun y=>(D y).comp (P y)) x‖+‖D x‖*‖fderiv ℝ P x‖:=hb.trans
        (add_le_add (mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fun y=>(D y).comp (P y)) x)) hP)
          (mul_le_mul_of_nonneg_right hc (norm_nonneg (fderiv ℝ P x))))
      _ ≤ ‖D x‖*‖fderiv ℝ P x‖+‖iteratedFDeriv ℝ 3 (field c J) x‖+‖D x‖*‖fderiv ℝ P x‖:=by
        exact add_le_add
          (hi.trans (add_le_add le_rfl ((mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg (fderiv ℝ D x)) hP).trans hj))) le_rfl
      _ = _:=by ring
  have hr:=source_fderiv_smul_norm_le (radialMultiplier (field c J)) P x
    ((source_radialMultiplier_contDiff c J).differentiable (by simp) x) hpd
  change ‖fderiv ℝ ((fun y=>(P y).comp ((D y).comp (P y)))-
    (fun y=>radialMultiplier (field c J) y • P y)) x‖ ≤ _
  rw [fderiv_sub hld hrd]
  have hbnd:‖fderiv ℝ (fun y=>(P y).comp ((D y).comp (P y))) x‖+
      ‖fderiv ℝ (fun y=>radialMultiplier (field c J) y • P y) x‖ ≤
      (2*‖fderiv ℝ P x‖*‖D x‖+‖iteratedFDeriv ℝ 3 (field c J) x‖)+
        (|radialMultiplier (field c J) x| * ‖fderiv ℝ P x‖+‖fderiv ℝ (radialMultiplier (field c J)) x‖):=
    add_le_add hl (hr.trans (add_le_add le_rfl (mul_le_of_le_one_right (norm_nonneg _) hP)))
  have he:(2*‖fderiv ℝ P x‖*‖D x‖+‖iteratedFDeriv ℝ 3 (field c J) x‖)+
        (|radialMultiplier (field c J) x| * ‖fderiv ℝ P x‖+‖fderiv ℝ (radialMultiplier (field c J)) x‖)=
      2*‖fderiv ℝ P x‖*‖D x‖+‖iteratedFDeriv ℝ 3 (field c J) x‖+
        ‖fderiv ℝ (radialMultiplier (field c J)) x‖+|radialMultiplier (field c J) x| * ‖fderiv ℝ P x‖:=by ring
  have hsub:‖fderiv ℝ (fun y=>(P y).comp ((D y).comp (P y))) x-
      fderiv ℝ (fun y=>radialMultiplier (field c J) y • P y) x‖ ≤
      ‖fderiv ℝ (fun y=>(P y).comp ((D y).comp (P y))) x‖+
      ‖fderiv ℝ (fun y=>radialMultiplier (field c J) y • P y) x‖:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [sub_apply]
    exact (norm_sub_le _ _).trans ((add_le_add
      ((fderiv ℝ (fun y=>(P y).comp ((D y).comp (P y))) x).le_opNorm v)
      ((fderiv ℝ (fun y=>radialMultiplier (field c J) y • P y) x).le_opNorm v)).trans_eq (by ring))
  exact hsub.trans (hbnd.trans_eq he)

end
end SlowEquilibration.PairConditionalDeterminantMoments
