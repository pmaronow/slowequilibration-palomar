-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedShiftExpectation

@[expose] public section

/-! # Borel dependence of the literal covariance disorder shift -/
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory FourPapersCommon
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem plantedShift_measurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    Measurable (plantedShift (N := N) c β) := by
  have h : StronglyMeasurable (fun z : Vector N × Disorder N P =>
      (β*field c z.2 z.1) • z.2) :=
    ((continuous_const.mul ((field_jointContinuous c).comp
      (continuous_snd.prodMk continuous_fst))).smul continuous_snd).stronglyMeasurable
  have hm := h.integral_prod_right' (ν := disorderLaw N P)
  have he (x : Vector N) : plantedShift c β x=
      ∫ D : Disorder N P,(β*field c D x) • D ∂disorderLaw N P := by
    simp only [plantedShift,gaussianLinearCovarianceShift,smul_apply,fieldCLM_apply,smul_eq_mul]
  rw [funext he]
  exact hm.measurable


end
end SlowEquilibration.SphericalModel
