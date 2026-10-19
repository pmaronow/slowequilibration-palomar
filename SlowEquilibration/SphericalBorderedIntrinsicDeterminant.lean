-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalBorderedIntrinsicHessian

/-! Literal actual intrinsic absolute determinant equals the genuine
one-border determinant in the complete geometric tangent basis. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet SphericalForm
open IntrinsicHessianLaw SphereHessian SphericalCommonHessianRegression WholeFieldRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

lemma abs_det_shift_order {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (k : ℝ) :
    |(A-k • (1:Matrix (Fin m) (Fin m) ℝ)).det|=
      |(k • (1:Matrix (Fin m) (Fin m) ℝ)-A).det| := by
  have heq : A-k • (1:Matrix (Fin m) (Fin m) ℝ)=-(k • (1:Matrix (Fin m) (Fin m) ℝ)-A) := by
    ext i j
    simp only [Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [heq,Matrix.det_neg,abs_mul,abs_pow]
  simp

/-- Actual complete intrinsic Hessian, at every specified radial target,
has precisely the literal one-border absolute determinant. No posterior
matrix law or determinant approximation is assumed. -/
theorem actual_intrinsic_abs_det_eq_border {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (x y : Vector (n+2))
    (hx : ‖x‖^2=(n+2:ℕ)) (hy : ‖y‖^2=(n+2:ℕ)) (hr : |overlap x y| < 1) (k : ℝ)
    (hrad : jet c 1 x (fun _=>x) J=(n+2:ℕ)*k) :
    |(intrinsicHessian (field c J) x).det|=
    |(GOEBorderedDeterminant.border
      (k-jet c 2 x ![planeDirection x y,planeDirection x y] J)
      (fun i=>-jet c 2 x ![commonFrame (by omega) x y hx hy hr i,planeDirection x y] J)
      (fun i=>-jet c 2 x ![commonFrame (by omega) x y hx hy hr i,planeDirection x y] J)
      (k • (1:Matrix (Fin n) (Fin n) ℝ)-hessianMatrix (k:=n) c x (commonFrame (by omega) x y hx hy hr) J)).det| := by
  let B:=borderedTangentBasis x y hx hy hr
  have hFrame : (fun i:Fin (n+1)=>(B i:Vector (n+2)))=borderedFrame x y hx hy hr :=
    funext (borderedTangentBasis_coe x y hx hy hr)
  have hRad : radialMultiplier (field c J) x=k := by
    rw [radialMultiplier_eq_jet,hrad]
    have hN : (n+2:ℝ)≠0:=by positivity
    field_simp
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix B.toBasis,
    intrinsicHessian_toMatrix_basis (by omega) c J x hx B,hFrame,hRad,abs_det_shift_order]
  rw [← Matrix.det_reindex_self (borderIndexEquiv n).symm
    (k • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-hessianMatrix c x (borderedFrame x y hx hy hr) J),
    full_shifted_hessian_eq_border]

end
end SlowEquilibration.SphericalPairCommonFrame

