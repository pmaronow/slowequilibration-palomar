-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensityEnergy
public import SlowEquilibration.NearIdentityLogDeterminant

/-! Actual Gaussian covariance determinant comparison by genuine whitening.
The reference square observation is constructed from its full covariance. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {E E' F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- No desired determinant comparison is assumed: whitening and the actual
near-identity eigenvalue theorem derive it from the covariance difference. -/
theorem gram_log_difference_le (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E' →L[ℝ] F) (hB : Surjective B)
    (hsmall : ‖((squareObservation B hB).symm : F →L[ℝ] F)‖^2*‖gram A-gram B‖ ≤ 1/2) :
    |Real.log (gram A).det-Real.log (gram B).det| ≤
      2*(Module.finrank ℝ F:ℝ)*‖((squareObservation B hB).symm : F →L[ℝ] F)‖^2*
        ‖gram A-gram B‖ := by
  let L:=squareObservation B hB
  let S:=(L.symm : F →L[ℝ] F)
  let C:=(S.comp (gram B-gram A)).comp S.adjoint
  let ε:=‖S‖^2*‖gram A-gram B‖
  have hsymGram (D : E →L[ℝ] F) : IsSelfAdjoint (gram D) := by
    change (gram D).adjoint=gram D
    rw [gram,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hsymB : IsSelfAdjoint (gram B) := by
    change (gram B).adjoint=gram B
    rw [gram,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  have hC : C.toLinearMap.IsSymmetric :=
    ((hsymB.sub (hsymGram A)).conj_adjoint S).isSymmetric
  have hε : 0 ≤ ε := by dsimp [ε];positivity
  have hnorm : ‖C‖ ≤ ε := by
    calc
      _ ≤ ‖S.comp (gram B-gram A)‖*‖S.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖S‖*‖gram B-gram A‖)*‖S.adjoint‖ := by gcongr;exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = ε := by rw [LinearIsometryEquiv.norm_map,norm_sub_rev];dsimp only [ε];ring
  have hNear:=NearIdentityLogDeterminant.det_positive_and_abs_log_le C hC hε hsmall hnorm
  have hId : (S.comp (gram B)).comp S.adjoint=ContinuousLinearMap.id ℝ F := by
    rw [← squareObservation_gram B hB]
    change ((L.symm : F →L[ℝ] F).comp
      ((L : F →L[ℝ] F).comp (L : F →L[ℝ] F).adjoint)).comp
      (L.symm : F →L[ℝ] F).adjoint=ContinuousLinearMap.id ℝ F
    rw [← ContinuousLinearMap.comp_assoc,ContinuousLinearEquiv.coe_symm_comp_coe,
      ContinuousLinearMap.id_comp,← ContinuousLinearMap.adjoint_comp,
      ContinuousLinearEquiv.coe_symm_comp_coe]
    simp
  have hWhiten : ContinuousLinearMap.id ℝ F-C=(S.comp (gram A)).comp S.adjoint := by
    dsimp only [C]
    rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp,hId]
    abel
  have hdetA : (ContinuousLinearMap.id ℝ F-C).det=S.det^2*(gram A).det := by
    rw [hWhiten]
    change LinearMap.det ((S.toLinearMap.comp (gram A).toLinearMap).comp S.adjoint.toLinearMap)=_
    rw [LinearMap.det_comp,LinearMap.det_comp]
    change S.det*(gram A).det*S.adjoint.det=_
    rw [det_adjoint_real]
    ring
  have hdetB : (1:ℝ)=S.det^2*(gram B).det := by
    have h:=congrArg ContinuousLinearMap.det hId
    change LinearMap.det ((S.toLinearMap.comp (gram B).toLinearMap).comp S.adjoint.toLinearMap)=
      LinearMap.det (LinearMap.id) at h
    rw [LinearMap.det_comp,LinearMap.det_comp,LinearMap.det_id] at h
    change S.det*(gram B).det*S.adjoint.det=1 at h
    rw [det_adjoint_real] at h
    nlinarith [h]
  have hS : S.det^2≠0 := by intro h;rw [h,zero_mul] at hdetB;norm_num at hdetB
  have hlogId : Real.log (ContinuousLinearMap.id ℝ F-C).det=
      Real.log (gram A).det-Real.log (gram B).det := by
    rw [hdetA,Real.log_mul hS (gram_det_pos A hA).ne']
    have h:=congrArg Real.log hdetB
    rw [Real.log_mul hS (gram_det_pos B hB).ne',Real.log_one] at h
    linarith
  rw [hlogId] at hNear
  convert hNear.2 using 1
  dsimp only [ε,S,L]
  ring

end
end SlowEquilibration.GaussianRegression
