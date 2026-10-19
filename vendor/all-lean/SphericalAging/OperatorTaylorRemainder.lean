module

public import SphericalAging.SecantCoefficient

public section

/-! Actual operator-valued quadratic Taylor remainders for Jacobian rows. -/
noncomputable section
open scoped NNReal ContDiff
namespace SphericalAging.OperatorTaylorRemainder
open HardSphereDynamics Set
variable {N : ℕ}

theorem taylor_remainder_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : State N → G} (hg : ContDiff ℝ ∞ g) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ g)) (x y : State N) :
    ‖g y-g x-fderiv ℝ g x (y-x)‖≤(L : ℝ)*‖y-x‖^2 := by
  let f : State N → G := fun z => g z-g x-fderiv ℝ g x (z-x)
  have hd (z : State N) : HasFDerivAt f (fderiv ℝ g z-fderiv ℝ g x) z :=
    (((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).sub_const _).sub
      ((fderiv ℝ g x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
  have hb : ∀ z∈Metric.closedBall x ‖y-x‖,‖fderiv ℝ f z‖≤(L : ℝ)*‖y-x‖ := by
    intro z hz
    rw [(hd z).fderiv]
    exact (hL.norm_sub_le z x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) L.coe_nonneg)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => (hd z).differentiableAt) hb
    (convex_closedBall x ‖y-x‖) (Metric.mem_closedBall_self (norm_nonneg (y-x)))
    (show y∈Metric.closedBall x ‖y-x‖ from by simp [Metric.mem_closedBall,dist_eq_norm])
  simpa only [f,sub_self,map_zero,sub_zero,mul_assoc,← pow_two] using hh

theorem jacobian_remainder_bound {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ (fderiv ℝ g))) (x y v : State N) :
    ‖(fderiv ℝ g y-fderiv ℝ g x-fderiv ℝ (fderiv ℝ g) x (y-x)) v‖≤
      (L : ℝ)*‖y-x‖^2*‖v‖ := by
  exact ((fderiv ℝ g y-fderiv ℝ g x-fderiv ℝ (fderiv ℝ g) x (y-x)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right
      (taylor_remainder_bound (hg.fderiv_right (m := ∞) (by simp)) hL x y) (norm_nonneg _))

end SphericalAging.OperatorTaylorRemainder
