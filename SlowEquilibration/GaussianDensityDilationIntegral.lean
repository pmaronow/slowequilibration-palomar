-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensityDilation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Exact physical density integral transport, including arbitrary nonnegative
integrands. The finite canonical densities make the change of variables valid
without a separate measurability premise on the transported integrand. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRegression
open Function MeasureTheory
open scoped ENNReal
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Genuine scalar change of variables for every nonnegative mark. -/
theorem lintegral_density_dilation (f : F → ℝ≥0∞) (hf : Measurable f)
    (hfinite : ∀ w,f w≠⊤) {c : ℝ} (hc : 0 < c) (g : F → ℝ≥0∞) :
    (∫⁻ w,f w*g w)=∫⁻ h,ENNReal.ofReal (c^Module.finrank ℝ F)*f (c • h)*g (c • h) := by
  let e : F ≃L[ℝ] F := (LinearEquiv.smulOfNeZero ℝ F c hc.ne').toContinuousLinearEquiv
  have hm:=map_withDensity_div_smul f hf hc
  have ht:=lintegral_map_equiv (fun h : F=>g (c • h)) e.symm.toHomeomorph.toMeasurableEquiv
    (μ:=volume.withDensity f)
  simp only [Homeomorph.toMeasurableEquiv_coe,ContinuousLinearEquiv.coe_toHomeomorph] at ht
  have he (w : F) : c • e.symm w=w := by
    change c • (c⁻¹ • w)=w
    rw [smul_smul,mul_inv_cancel₀ hc.ne',one_smul]
  simp only [he] at ht
  change (∫⁻ h,g (c • h) ∂(volume.withDensity f).map (fun w : F=>c⁻¹ • w))=_ at ht
  rw [hm] at ht
  have hmf : Measurable (fun h : F=>ENNReal.ofReal (c^Module.finrank ℝ F)*f (c • h)) :=
    measurable_const.mul (hf.comp (continuous_const.smul continuous_id).measurable)
  have hmfinite : ∀ᵐ h ∂(volume : Measure F),
      ENNReal.ofReal (c^Module.finrank ℝ F)*f (c • h)<⊤ :=
    Filter.Eventually.of_forall (fun h=>lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite _)))
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume hmf hmfinite,
    lintegral_withDensity_eq_lintegral_mul_non_measurable volume hf
      (Filter.Eventually.of_forall fun w=>lt_top_iff_ne_top.mpr (hfinite w))] at ht
  exact ht.symm

end SlowEquilibration.GaussianRegression
