module

public import SphericalAging.MultivariateTaylor

public section

/-! Uniform first-order remainder control with only C¹ regularity and
uniform continuity of the actual derivative. This supports genuine C²
expectation tests without imposing a third derivative. -/
noncomputable section
open Set Filter Topology
open scoped NNReal
namespace SphericalAging.UniformDerivativeRemainder
open HardSphereDynamics
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem remainder_small_plus_quadratic (g : State N → G)
    (hg : Differentiable ℝ g) (huc : UniformContinuous (fderiv ℝ g))
    (K : ℝ≥0) (hK : ∀ x,‖fderiv ℝ g x‖≤K) :
    ∀ ε : ℝ,0<ε → ∃ C : ℝ,0≤C ∧ ∀ x y,
      ‖g y-g x-fderiv ℝ g x (y-x)‖≤ε*‖y-x‖+C*‖y-x‖^2 := by
  have hLip : LipschitzWith K g := lipschitzWith_of_nnnorm_fderiv_le hg
    (fun x => by exact_mod_cast hK x)
  intro ε hε
  obtain ⟨δ,hδ,hm⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨2*(K : ℝ)/δ,by positivity,?_⟩
  intro x y
  by_cases hxy : ‖y-x‖<δ
  · let f : State N → G := fun z => g z-g x-fderiv ℝ g x (z-x)
    have hd (z : State N) : HasFDerivAt f (fderiv ℝ g z-fderiv ℝ g x) z :=
      ((hg z).hasFDerivAt.sub_const _).sub
        ((fderiv ℝ g x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
    have hb : ∀ z∈Metric.closedBall x ‖y-x‖,‖fderiv ℝ f z‖≤ε := by
      intro z hz
      rw [(hd z).fderiv]
      have hzdist : dist z x<δ :=
        (Metric.mem_closedBall.mp hz).trans_lt hxy
      have hh := hm hzdist
      change dist (fderiv ℝ g z) (fderiv ℝ g x)<ε at hh
      rw [dist_eq_norm] at hh
      exact hh.le
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => (hd z).differentiableAt) hb
      (convex_closedBall x ‖y-x‖) (Metric.mem_closedBall_self (norm_nonneg (y-x)))
      (show y∈Metric.closedBall x ‖y-x‖ from by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl])
    have hsmall : ‖g y-g x-fderiv ℝ g x (y-x)‖≤ε*‖y-x‖ := by
      simpa only [f,sub_self,map_zero,sub_zero] using hh
    exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  · have hfar : δ≤‖y-x‖ := le_of_not_gt hxy
    have hfirst : ‖g y-g x‖≤(K : ℝ)*‖y-x‖ := by
      simpa only [norm_sub_rev] using hLip.norm_sub_le y x
    have hsecond : ‖fderiv ℝ g x (y-x)‖≤(K : ℝ)*‖y-x‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))
    have hb := (norm_sub_le (g y-g x) (fderiv ℝ g x (y-x))).trans (add_le_add hfirst hsecond)
    apply hb.trans
    have hq : 2*(K : ℝ)*‖y-x‖≤(2*(K : ℝ)/δ)*‖y-x‖^2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hδ).mpr
      have hh := mul_le_mul_of_nonneg_left hfar (show 0≤2*(K : ℝ)*‖y-x‖ by positivity)
      nlinarith
    nlinarith [mul_nonneg hε.le (norm_nonneg (y-x))]

end SphericalAging.UniformDerivativeRemainder
