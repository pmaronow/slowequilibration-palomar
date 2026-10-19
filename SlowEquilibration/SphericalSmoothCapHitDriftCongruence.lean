-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSmoothParameterCapHit

/-! A literal finite-horizon cap-hitting probability depends only on the
fixed spherical drift and axis, even when its two parameter spaces differ. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalSmoothCapHitDriftCongruence
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalSmoothParameter SphericalAging.HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem uniformCapHitProbability_eq_of_fixed_drift_eq
    {N : ℕ} {Θ₁ Θ₂ : Type*}
    [NormedAddCommGroup Θ₁] [NormedSpace ℝ Θ₁]
    [FiniteDimensional ℝ Θ₁] [MeasurableSpace Θ₁] [BorelSpace Θ₁]
    [NormedAddCommGroup Θ₂] [NormedSpace ℝ Θ₂]
    [FiniteDimensional ℝ Θ₂] [MeasurableSpace Θ₂] [BorelSpace Θ₂]
    (β : ℝ) (g₁ : Θ₁ × Vector N → Vector N) (hg₁ : ContDiff ℝ 1 g₁)
    (g₂ : Θ₂ × Vector N → Vector N) (hg₂ : ContDiff ℝ 1 g₂)
    (T : ℝ≥0) (a : ℝ) (u : Vector N) (p₁ : Θ₁) (p₂ : Θ₂)
    (h : ∀ x, g₁ (p₁,x) = g₂ (p₂,x)) :
    uniformCapHitProbability β g₁ hg₁ T a (u,p₁) =
      uniformCapHitProbability β g₂ hg₂ T a (u,p₂) := by
  rw [uniformCapHitProbability_eq_actual,
    uniformCapHitProbability_eq_actual]
  have he : (fun x => g₁ (p₁,x)) = (fun x => g₂ (p₂,x)) := funext h
  simp only [he]

end SlowEquilibration.SphericalSmoothCapHitDriftCongruence
