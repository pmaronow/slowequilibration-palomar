module

public import SphericalAging.LpEightInterpolation

public section

/-! Genuine moment bounds give linear Lp bounds, and the sharp interpolation
inequality gives the nonlinear fourth-norm remainder estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace SphericalAging.LpMomentBounds
open LpEightInterpolation
variable {α E V : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedAddCommGroup V] {μ : Measure α} {f : α → E} {v : V}

theorem lpNorm_le_of_moment {p : ℕ} (hp : 0<p) (hf : MemLp f (p:ℝ≥0∞) μ)
    {C : ℝ} (hC : 0≤C) (hb : (∫ x,‖f x‖^p ∂μ)≤C*‖v‖^p) :
    lpNorm f (p:ℝ≥0∞) μ≤C^((p:ℝ)⁻¹)*‖v‖ := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne'
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hp.ne') (by finiteness)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast,Real.rpow_natCast]
  calc
    _ ≤ (C*‖v‖^p)^((p:ℝ)⁻¹) := Real.rpow_le_rpow
      (integral_nonneg (fun x => pow_nonneg (norm_nonneg _) _)) hb (by positivity)
    _ = C^((p:ℝ)⁻¹)*‖v‖ := by
      rw [Real.mul_rpow hC (pow_nonneg (norm_nonneg _) _),←Real.rpow_natCast,
        ←Real.rpow_mul (norm_nonneg _),mul_inv_cancel₀ hp0,Real.rpow_one]

theorem lpNorm_four_le_of_moment (hf : MemLp f 4 μ) {C : ℝ} (hC : 0≤C)
    (hb : (∫ x,‖f x‖^4 ∂μ)≤C*‖v‖^4) : lpNorm f 4 μ≤C^((1:ℝ)/4)*‖v‖ := by
  simpa only [Nat.cast_ofNat,one_div] using lpNorm_le_of_moment (p:=4) (by decide) hf hC hb

theorem lpNorm_eight_le_of_moment (hf : MemLp f 8 μ) {C : ℝ} (hC : 0≤C)
    (hb : (∫ x,‖f x‖^8 ∂μ)≤C*‖v‖^8) : lpNorm f 8 μ≤C^((1:ℝ)/8)*‖v‖ := by
  simpa only [Nat.cast_ofNat,one_div] using lpNorm_le_of_moment (p:=8) (by decide) hf hC hb

theorem fourth_remainder_bound (h2 : MemLp f 2 μ) (h8 : MemLp f 8 μ)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hb2 : lpNorm f 2 μ≤A*‖v‖^2) (hb8 : lpNorm f 8 μ≤B*‖v‖) :
    lpNorm f 4 μ≤(A*‖v‖^2)^((1:ℝ)/3)*(B*‖v‖)^((2:ℝ)/3) := by
  apply (lpNorm_four_le h2 h8).trans
  exact mul_le_mul
    (Real.rpow_le_rpow lpNorm_nonneg hb2 (by norm_num))
    (Real.rpow_le_rpow lpNorm_nonneg hb8 (by norm_num))
    (Real.rpow_nonneg lpNorm_nonneg _) (Real.rpow_nonneg (by positivity) _)

end SphericalAging.LpMomentBounds
