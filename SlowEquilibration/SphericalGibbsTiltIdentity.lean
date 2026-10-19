-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalEnergy
public import SlowEquilibration.ConditionedEntranceTiltCommutator

/-! A change of continuous spherical Hamiltonian is the literal normalized
exponential tilt, with its exact partition-ratio normalization. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace SlowEquilibration.SphericalModel
open ConditionedEntrance
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def gibbsEnergyDifference (β₀ β₁ : ℝ) (H₀ H₁ : Vector N → ℝ) (x : Vector N) : ℝ :=
  β₁*H₁ x-β₀*H₀ x

theorem gibbsLaw_normalizedTilt (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N → ℝ) (hH₀ : Continuous H₀) (hH₁ : Continuous H₁) :
    gibbsLaw N β₁ H₁=normalizedTilt (gibbsLaw N β₀ H₀)
      (gibbsEnergyDifference β₀ β₁ H₀ H₁) (partition N β₁ H₁/partition N β₀ H₀) := by
  have hw : Continuous (gibbsEnergyDifference β₀ β₁ H₀ H₁) :=
    (hH₁.const_mul β₁).sub (hH₀.const_mul β₀)
  unfold normalizedTilt gibbsLaw
  rw [← withDensity_mul (sphereLaw N)
    (f:=fun x => ENNReal.ofReal (gibbsDensity N β₀ H₀ x))
    (g:=fun x => ENNReal.ofReal (Real.exp (gibbsEnergyDifference β₀ β₁ H₀ H₁ x)/(partition N β₁ H₁/partition N β₀ H₀)))
    (gibbsDensity_continuous β₀ hH₀).measurable.ennreal_ofReal
    ((Real.continuous_exp.comp hw).div_const _).measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  apply ae_of_all
  intro x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (gibbsDensity_pos hN β₀ hH₀ x).le]
  congr 1
  dsimp only [gibbsDensity,gibbsEnergyDifference]
  rw [Real.exp_sub]
  field_simp [(partition_pos hN β₀ hH₀).ne',(partition_pos hN β₁ hH₁).ne',Real.exp_ne_zero]

theorem gibbsTilt_mass (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N → ℝ) (hH₀ : Continuous H₀) (_hH₁ : Continuous H₁) :
    (∫ x,Real.exp (gibbsEnergyDifference β₀ β₁ H₀ H₁ x) ∂gibbsLaw N β₀ H₀)=
      partition N β₁ H₁/partition N β₀ H₀ := by
  rw [integral_gibbsLaw hN β₀ hH₀]
  have hp (x : Vector N) : gibbsDensity N β₀ H₀ x*
      Real.exp (gibbsEnergyDifference β₀ β₁ H₀ H₁ x)=Real.exp (β₁*H₁ x)/partition N β₀ H₀ := by
    dsimp only [gibbsDensity,gibbsEnergyDifference]
    rw [Real.exp_sub]
    field_simp [Real.exp_ne_zero]
  simp_rw [hp]
  rw [integral_div]
  rfl

end SlowEquilibration.SphericalModel
