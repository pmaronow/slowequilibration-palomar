-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalUniformStartEntropy

/-! Finite integrability of literal bounded square tests and their
continuous spherical multipliers. No moment or energy is assumed. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {E : Type*} [MeasurableSpace E]

theorem norm_bounded_weight_square (μ : Measure E) (F U : E→ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀ᵐ x ∂μ,‖F x‖≤C) (hU : ∀ᵐ x ∂μ,‖U x‖≤1) :
    ∀ᵐ x ∂μ,‖F x*(U x)^2‖≤C := by
  filter_upwards [hF,hU] with x hx hy
  rw [norm_mul,norm_pow]
  have hsq : ‖U x‖^2≤1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) hy 2
  exact (mul_le_mul hx hsq (sq_nonneg _) hC).trans_eq (mul_one C)

theorem integrable_bounded_weight_square (μ : Measure E) [IsFiniteMeasure μ]
    (F U : E→ℝ) (C : ℝ) (hC : 0≤C)
    (hFm : AEStronglyMeasurable F μ) (hUm : AEStronglyMeasurable U μ)
    (hF : ∀ᵐ x ∂μ,‖F x‖≤C) (hU : ∀ᵐ x ∂μ,‖U x‖≤1) :
    Integrable (fun x => F x*(U x)^2) μ :=
  Integrable.of_bound (hFm.mul (hUm.pow 2)) C (norm_bounded_weight_square μ F U C hC hF hU)

theorem integrable_continuous_bounded_weight_square {N : ℕ} (hN : 1≤N) (β : ℝ)
    (H a F U : Vector N→ℝ) (hH : Continuous H) (ha : Continuous a) (C : ℝ) (hC : 0≤C)
    (hFm : AEStronglyMeasurable F (gibbsLaw N β H))
    (hUm : AEStronglyMeasurable U (gibbsLaw N β H))
    (hF : ∀ᵐ x ∂gibbsLaw N β H,‖F x‖≤C) (hU : ∀ᵐ x ∂gibbsLaw N β H,‖U x‖≤1) :
    Integrable (fun x => a x*F x*(U x)^2) (gibbsLaw N β H) := by
  have hi := (integrable_gibbs_of_continuous hN β hH ha).mul_bdd
    (hFm.mul (hUm.pow 2)) (norm_bounded_weight_square (gibbsLaw N β H) F U C hC hF hU)
  exact hi.congr (.of_forall (fun x => by
    change a x*(F x*(U x)^2)=a x*F x*(U x)^2
    ring))

end SlowEquilibration.SphericalForm
