-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeometricBorderMeanLaw

/-! The literal intrinsic Hessian determinant is the true actual border
on every fixed physical radial fiber of the original tensor disorder. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open SphericalCommonHessianRegression PhysicalCommonBorderMoments GOERawMoments
open IntrinsicHessianLaw SphericalForm SphereHessian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem intrinsic_abs_det_eq_actual_fullBorder {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+3) P) (x y : Vector (n+3))
    (hx : ‖x‖^2=(n+3:ℕ)) (hy : ‖y‖^2=(n+3:ℕ)) (hr : |overlap x y| < 1) (k : ℝ)
    (hrad : jet c 1 x (fun _=>x) J=(n+3:ℕ)*k) :
    |(intrinsicHessian (field c J) x).det|=
      fullBorder (n:=n) (hessianMatrix (k:=n+1) c x (commonFrame (by omega) x y hx hy hr)) k
        (actualObservation (cornerCLM c x (planeDirection x y)))
        (actualObservation (commonRowCLM (m:=n+1) c x (commonFrame (by omega) x y hx hy hr) (planeDirection x y))) J := by
  have hI:=actual_intrinsic_abs_det_eq_border (n:=n+1) c J x y hx hy hr k hrad
  have hG:=geometric_fullBorder_eq_shifted_absoluteDet (n:=n) c J x y hx hy hr k
  rw [hG]
  unfold matrixAbsoluteDet
  rw [← Matrix.det_reindex_self (borderIndexEquiv (n+1)).symm
    (k • (1:Matrix (Fin (n+2)) (Fin (n+2)) ℝ)-hessianMatrix c x (borderedFrame x y hx hy hr) J),
    full_shifted_hessian_eq_border]
  exact hI

end
end SlowEquilibration.SphericalPairCommonFrame
