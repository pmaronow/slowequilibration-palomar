-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalJointEnergyIntegrals

/-! Literal measurable zero-order square-commutator defect. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ} {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]

def jointGibbsZeroDefectSquare (β : ℝ) (H w F U : Θ×Vector N→ℝ) (p : Θ) : ℝ :=
  ∫ x,(1-Real.exp (-w (p,x)))*(F (p,x)-1)*(U (p,x))^2 ∂gibbsLaw N β (fun y => H (p,y))

theorem jointGibbsZeroDefectSquare_measurable (hN : 1≤N) (β : ℝ)
    (H w F U : Θ×Vector N→ℝ) (hH : Continuous H) (hw : StronglyMeasurable w)
    (hF : StronglyMeasurable F) (hU : StronglyMeasurable U) :
    Measurable (jointGibbsZeroDefectSquare β H w F U) := by
  exact jointHamiltonian_integral_measurable hN β H hH _
    (((stronglyMeasurable_const.sub (Real.continuous_exp.comp_stronglyMeasurable hw.neg)).mul
      (hF.sub stronglyMeasurable_const)).mul (hU.pow 2))

end SlowEquilibration.SphericalForm
