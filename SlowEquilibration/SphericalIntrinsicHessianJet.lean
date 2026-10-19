-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereHessian

/-!
# The genuine intrinsic Hessian in actual polynomial field jets
-/

@[expose] public section

namespace SlowEquilibration.SphereHessian

open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace

noncomputable section

/-- The genuine intrinsic Hessian has the actual ambient second derivative
minus the actual radial field derivative, on all actual tangent vectors. -/
theorem intrinsicHessian_field_inner {N P : ℕ} (hN : N ≠ 0)
    (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) (hx : OnSphere x)
    (v w : tangentPlane x) :
    inner ℝ (intrinsicHessian (field c J) x v) w =
      fderiv ℝ (fderiv ℝ (field c J)) x v w -
        (jet c 1 x (fun _ => x) J / (N : ℝ)) * inner ℝ v w := by
  change inner ℝ (intrinsicHessian (field c J) x v : Vector N) (w : Vector N) = _
  rw [intrinsicHessian_apply hN _ x hx ((field_gradient_contDiff c J).differentiable (by simp) x),
    inner_sub_left, real_inner_smul_left, (tangentProjection_symmetric x).apply_clm]
  have hw : tangentProjection x (w : Vector N) = w := by
    rw [tangentProjection_eq_starProjection hN x hx]
    exact (tangentPlane x).starProjection_eq_self_iff.mpr w.2
  rw [hw, field_gradient_derivative_inner, radialMultiplier_eq_jet]
  rfl

/-- Symmetry is derived from the actual polynomial field's second Frechet
derivative, confirming the genuine intrinsic self-adjoint Hessian operator. -/
theorem intrinsicHessian_field_symmetric {N P : ℕ} (hN : N ≠ 0)
    (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) (hx : OnSphere x) :
    (intrinsicHessian (field c J) x).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (intrinsicHessian (field c J) x v) w =
    inner ℝ v (intrinsicHessian (field c J) x w)
  conv_rhs => rw [real_inner_comm]
  rw [intrinsicHessian_field_inner hN c J x hx,
    intrinsicHessian_field_inner hN c J x hx]
  rw [(field_contDiff c J).contDiffAt.isSymmSndFDerivAt (by simp) (v : Vector N) (w : Vector N)]
  congr 2
  exact real_inner_comm _ _

/-- Every ordinary tangent-frame matrix entry of the intrinsic Hessian is
the actual polynomial Hessian jet with its actual radial multiplier removed. -/
theorem intrinsicHessian_frame_entry {N P k : ℕ} (hN : N ≠ 0)
    (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) (hx : OnSphere x)
    (e : Fin k → tangentPlane x) (i j : Fin k) :
    inner ℝ (intrinsicHessian (field c J) x (e i)) (e j) =
      hessianEntry c x (fun a => (e a : Vector N)) i j J -
        (jet c 1 x (fun _ => x) J / (N : ℝ)) * inner ℝ (e i) (e j) := by
  rw [intrinsicHessian_field_inner hN c J x hx, hessianEntry_eq_fderiv]

end
end SlowEquilibration.SphereHessian
