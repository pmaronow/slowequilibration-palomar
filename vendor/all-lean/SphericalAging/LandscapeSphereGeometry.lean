module

public import SphericalAging.LandscapeDerivatives

public section

/-! The spherical Hessian used in the landscape bounds is the actual
covariant derivative obtained by differentiating and projecting the tangent gradient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
namespace SphericalAging.LandscapeSphereGeometry
open FiniteModel LandscapeDerivatives HardSphereDynamics

@[expose] def projectedGradient {N : ℕ} (g : Vector N → Vector N) (x : Vector N) : Vector N :=
  tangentProjection x (g x)

theorem projectedGradient_fderiv_apply {N : ℕ} (g : Vector N → Vector N)
    (x v : Vector N) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (projectedGradient g) x v =
      fderiv ℝ g x v -
        ((inner ℝ v (g x)+inner ℝ x (fderiv ℝ g x v))/(N : ℝ)) • x -
        (inner ℝ x (g x)/(N : ℝ)) • v := by
  have hi : DifferentiableAt ℝ (fun y : Vector N => inner ℝ y (g y)) x := by
    simpa only [id_eq] using differentiableAt_id.inner ℝ hg
  have hc : DifferentiableAt ℝ (fun y : Vector N => inner ℝ y (g y)/(N : ℝ)) x :=
    by simpa only [div_eq_mul_inv] using hi.mul_const (N : ℝ)⁻¹
  unfold projectedGradient
  simp only [tangentProjection_apply, projection]
  simp only [div_eq_mul_inv] at hc ⊢
  change (fderiv ℝ (fun y : Vector N => g y -
    (inner ℝ y (g y)*(N : ℝ)⁻¹) • id y) x) v = _
  rw [fderiv_fun_sub hg (hc.fun_smul differentiableAt_id),
    fderiv_fun_smul hc differentiableAt_id]
  rw [fderiv_mul_const hi]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, fderiv_id]
  rw [fderiv_inner_apply ℝ (f := fun y : Vector N => y) (g := g) differentiableAt_id hg]
  dsimp only [id_eq]
  simp only [smul_eq_mul, fderiv_fun_id, ContinuousLinearMap.id_apply]
  module

theorem projectedGradient_covariantDerivative {N : ℕ} (hN : 0 < N)
    (g : Vector N → Vector N) (x : Vector N) (hx : ‖x‖^2=(N : ℝ))
    (hg : DifferentiableAt ℝ g x) :
    (tangentProjection x).comp ((fderiv ℝ (projectedGradient g) x).comp (tangentProjection x)) =
      (tangentProjection x).comp ((fderiv ℝ g x).comp (tangentProjection x)) -
        (inner ℝ x (g x)/(N : ℝ)) • tangentProjection x := by
  have hs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  apply ContinuousLinearMap.ext
  intro v
  change tangentProjection x (fderiv ℝ (projectedGradient g) x (tangentProjection x v)) = _
  rw [projectedGradient_fderiv_apply g x _ hg, map_sub, map_sub, map_smul, map_smul]
  have hz : tangentProjection x x = 0 := by
    rw [tangentProjection_apply]
    exact projection_normal_zero (Nat.ne_of_gt hN) x hs
  have hid : tangentProjection x (tangentProjection x v) = tangentProjection x v := by
    simp only [tangentProjection_apply]
    exact projection_idempotent (Nat.ne_of_gt hN) x v hs
  rw [hz, smul_zero, sub_zero, hid]
  rfl

/-- The bounded operator is exactly the derivative of the actual spherical gradient,
projected on both tangent arguments; it is not an auxiliary substitute for the Hessian. -/
theorem sphericalHessian_eq_covariantDerivative {N p : ℕ} (hN : 0 < N)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    sphericalHessian J x = (tangentProjection x).comp
      ((fderiv ℝ (projectedGradient (gradient (Hamiltonian N p J))) x).comp (tangentProjection x)) := by
  apply Eq.symm
  apply projectedGradient_covariantDerivative hN _ x hx
  have hg : ContDiff ℝ ⊤ (gradient (Hamiltonian N p J)) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Vector N)).symm.contDiff.comp
      ((Hamiltonian_contDiff J).fderiv_right (by simp))
  exact hg.differentiable (by simp) x

end SphericalAging.LandscapeSphereGeometry
