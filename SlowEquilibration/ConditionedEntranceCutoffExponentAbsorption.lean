-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalCutoffEnergy

/-! The source cutoff energy changes the cap-tail exponent by a higher
power of the physical cap radius. A fixed small radius absorbs that cost
uniformly in the dimension. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SphericalModel
set_option autoImplicit false
set_option maxHeartbeats 300000

/-- The explicit absorption radius is positive for a nonnegative energy
coefficient. -/
theorem cutoff_energy_cap_tail_radius_pos
    {β A : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A) :
    0 < 1 / (128 * (1 + β * A)) := by
  positivity

/-- At minimum mixture degree four, the cutoff energy exponential is
absorbed by half of the physical uniform-axis cap-tail exponent. The
radius threshold is explicit and independent of the dimension. -/
theorem cutoff_energy_cap_tail_exponent_absorption
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {β A α : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hα : 0 < α) (hαsmall : α ≤ 1 / (128 * (1 + β * A)))
    (N : ℕ) :
    Real.exp (β * A * (N : ℝ) * α^μ.minDegree) *
      Real.exp (-(N : ℝ) * α^2 / 64) ≤
        Real.exp (-(N : ℝ) * α^2 / 128) := by
  have hBA : 0 ≤ β * A := mul_nonneg hβ hA
  have hden : 0 < 128 * (1 + β * A) := by positivity
  have hαone : α ≤ 1 := by
    have hd128 : (1 : ℝ) ≤ 128 * (1 + β * A) := by nlinarith
    have hdiv : 1 / (128 * (1 + β * A)) ≤ (1 : ℝ) :=
      (div_le_iff₀ hden).2 (by simpa using hd128)
    exact hαsmall.trans hdiv
  have hcoef : 128 * (β * A) * α ≤ 1 := by
    have hs : α * (128 * (1 + β * A)) ≤ 1 :=
      (le_div_iff₀ hden).1 hαsmall
    nlinarith [mul_nonneg hα.le hBA]
  have hpow : α ^ μ.minDegree ≤ α ^ 3 :=
    pow_le_pow_of_le_one hα.le hαone (by omega)
  have henergy : β * A * α^μ.minDegree ≤ α^2 / 128 := by
    have hp := mul_le_mul_of_nonneg_left hpow hBA
    have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg α)
    nlinarith only [hp, hc]
  have hdim := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg N)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hdim]

/-- The actual bounded-mark source-cutoff energy coefficient is
nonnegative. -/
theorem uniform_source_cutoff_energy_constant_nonneg
    (μ : FiniteMixture) {Q hbar kbar B R : ℝ}
    (hh : 0 ≤ hbar) (hk : 0 ≤ kbar) (hR : 0 ≤ R) :
    0 ≤ uniformCutoffEnergyConstant μ Q hbar kbar B R := by
  have hM : 0 ≤ hbar + kbar + 3 * centerConstant μ Q := by
    have hc := (centerConstant_pos μ Q).le
    positivity
  exact cutoffEnergyConstant_nonneg μ Q _ B R hM hR

/-- The actual bounded-mark cutoff coefficient admits a positive
dimension-independent absorption radius. -/
theorem uniform_source_cutoff_cap_tail_radius_pos
    (μ : FiniteMixture) {β Q hbar kbar B R : ℝ}
    (hβ : 0 ≤ β) (hh : 0 ≤ hbar) (hk : 0 ≤ kbar) (hR : 0 ≤ R) :
    0 < 1 / (128 * (1 + β * uniformCutoffEnergyConstant μ Q hbar kbar B R)) :=
  cutoff_energy_cap_tail_radius_pos hβ
    (uniform_source_cutoff_energy_constant_nonneg μ hh hk hR)

/-- The absorption applies to the actual uniform source-cutoff energy
constant for bounded physical marks. -/
theorem uniform_source_cutoff_cap_tail_absorption
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {β Q hbar kbar B R α : ℝ} (hβ : 0 ≤ β)
    (hh : 0 ≤ hbar) (hk : 0 ≤ kbar) (hR : 0 ≤ R)
    (hα : 0 < α)
    (hαsmall : α ≤
      1 / (128 * (1 + β * uniformCutoffEnergyConstant μ Q hbar kbar B R)))
    (N : ℕ) :
    Real.exp (β * uniformCutoffEnergyConstant μ Q hbar kbar B R *
      (N : ℝ) * α^μ.minDegree) *
      Real.exp (-(N : ℝ) * α^2 / 64) ≤
        Real.exp (-(N : ℝ) * α^2 / 128) := by
  have hA : 0 ≤ uniformCutoffEnergyConstant μ Q hbar kbar B R :=
    uniform_source_cutoff_energy_constant_nonneg μ hh hk hR
  exact cutoff_energy_cap_tail_exponent_absorption μ hd hβ hA hα hαsmall N

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
