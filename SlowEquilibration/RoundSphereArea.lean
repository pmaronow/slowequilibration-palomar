-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.RoundSphereVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Exact Gamma normalization of the genuine round sphere area. -/
@[expose] public section
namespace SlowEquilibration.SphereChartVolume
open MeasureTheory Set Module
open scoped ENNReal
noncomputable section

theorem manuscriptRoundVolume_mass_gamma (n : ℕ) :
    manuscriptRoundVolume n univ = ENNReal.ofReal
      ((Real.sqrt (n+1 : ℕ))^n * (n+1 : ℕ) *
        ((Real.sqrt Real.pi)^(n+1) / Real.Gamma (((n+1 : ℕ) : ℝ)/2+1))) := by
  have hd : Module.finrank ℝ (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) = n+1 := by
    rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod]
    simp
  rw [manuscriptRoundVolume_total, Measure.toSphere_apply_univ,
    InnerProductSpace.volume_ball, hd]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, radiusAreaScale]
  rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (by positivity)),
    ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) _), ENNReal.ofReal_natCast]
  exact (mul_assoc _ _ _).symm

end
end SlowEquilibration.SphereChartVolume
