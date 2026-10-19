-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeRegularDisorder
public import SlowEquilibration.SphericalLatitudePhysicalIntensity

@[expose] public section

/-! # Uniform actual latitude score bounds on the physical regularity event -/
namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open SphericalModel SphericalGaussianJet WholeFieldRegression
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[simp] theorem actualLatitudeScore_one {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (J : Disorder (n+2) P) (y : Vector (n+1)) :
    actualLatitudeScore c w e q J y 1=
      fderiv ℝ (field c J) (latitudeMap w e q y) (latitudeRadialVector e q y)/((n+2 : ℕ) : ℝ) := by
  simp only [actualLatitudeScore,PiLp.smul_apply,smul_eq_mul,latitudeScoreCLM_apply_one,
    unpack_euclideanDisorder,jet,iteratedFDeriv_one_apply]
  ring

theorem latitudeScore_regularDisorder_bounds {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (hJ : J ∈ regularDisorder)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x,inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    |actualLatitudeScore c w e q J y 0| ≤ derivativeConstant c ∧
    |actualLatitudeScore c w e q J y 1| ≤ derivativeConstant c := by
  have hN : (0:ℝ) < ((n+2 : ℕ) : ℝ) := by positivity
  have hnorm : ‖latitudeMap w e q y‖=Real.sqrt ((n+2 : ℕ) : ℝ) := by
    rw [← latitudeMap_norm_sq (by omega) w hw e he hq y hy,Real.sqrt_sq (norm_nonneg _)]
  have hb := field_regularDisorder_ball_bounds (by omega) c J hJ
    (latitudeMap w e q y) hnorm.le
  constructor
  · rw [actualLatitudeScore_zero,abs_div,abs_of_pos hN]
    exact (div_le_iff₀ hN).mpr hb.1
  · have hv : ‖latitudeRadialVector e q y‖ ≤ Real.sqrt ((n+2 : ℕ) : ℝ) := by
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [latitudeRadialVector_norm_sq e hq y hy,Real.sq_sqrt hN.le]
      nlinarith [mul_nonneg (Nat.cast_nonneg (n+2) : (0:ℝ) ≤ ((n+2 : ℕ) : ℝ)) (sq_nonneg q)]
    have hgrad : ‖fderiv ℝ (field c J) (latitudeMap w e q y)‖ ≤
        derivativeConstant c*Real.sqrt ((n+2 : ℕ) : ℝ) := by
      simpa only [gradient,
        LinearIsometryEquiv.norm_map] using hb.2.1
    rw [actualLatitudeScore_one,abs_div,abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    calc
      _ ≤ ‖fderiv ℝ (field c J) (latitudeMap w e q y)‖*‖latitudeRadialVector e q y‖ := by
        simpa only [Real.norm_eq_abs] using
          (fderiv ℝ (field c J) (latitudeMap w e q y)).le_opNorm (latitudeRadialVector e q y)
      _ ≤ (derivativeConstant c*Real.sqrt ((n+2 : ℕ) : ℝ))*Real.sqrt ((n+2 : ℕ) : ℝ) :=
        mul_le_mul hgrad hv (norm_nonneg _)
          (mul_nonneg (derivativeConstant_pos c).le (Real.sqrt_nonneg _))
      _ = _ := by rw [mul_assoc,← pow_two,Real.sq_sqrt hN.le]

end
end SlowEquilibration.SphericalLatitudeChartKacRice
