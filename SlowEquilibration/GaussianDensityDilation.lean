-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianOrthogonalRegression

/-! Genuine Lebesgue density transport under scalar normalization, with the
Jacobian derived from the linear determinant in the actual target dimension. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function MeasureTheory
open scoped ENNReal
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Pulling a genuine density back by division by c gives exactly the
Jacobian c^dim. This is a measure identity, not an assumed change of variables. -/
theorem map_withDensity_div_smul (f : F → ℝ≥0∞) (hf : Measurable f)
    {c : ℝ} (hc : 0 < c) :
    (volume.withDensity f).map (fun w : F=>c⁻¹ • w)=
      volume.withDensity (fun w=>ENNReal.ofReal (c^Module.finrank ℝ F)*f (c • w)) := by
  let e : F ≃L[ℝ] F := (LinearEquiv.smulOfNeZero ℝ F c hc.ne').toContinuousLinearEquiv
  have hdet : (e.symm : F →L[ℝ] F).det=(c⁻¹)^Module.finrank ℝ F := by
    change LinearMap.det (c⁻¹ • (LinearMap.id : F →ₗ[ℝ] F))=_
    rw [LinearMap.det_smul,LinearMap.det_id,mul_one]
  have hdet0 : (e.symm : F →L[ℝ] F).det≠0 := by
    rw [hdet]
    exact pow_ne_zero _ (inv_ne_zero hc.ne')
  have hm : (volume : Measure F).map e.symm=
      ENNReal.ofReal (c^Module.finrank ℝ F) • volume := by
    have h:=Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure F) (f:=(e.symm : F →L[ℝ] F).toLinearMap) hdet0
    change (volume : Measure F).map e.symm=
      ENNReal.ofReal |(e.symm : F →L[ℝ] F).det⁻¹| • volume at h
    simpa only [hdet,← inv_pow,inv_inv,abs_of_pos (pow_pos hc _)] using h
  have ht:=map_withDensity_equiv e.symm.toHomeomorph.toMeasurableEquiv
    (volume : Measure F) f hf
  simp only [Homeomorph.toMeasurableEquiv_coe,Homeomorph.toMeasurableEquiv_symm_coe,
    ContinuousLinearEquiv.coe_toHomeomorph] at ht
  change (volume.withDensity f).map (fun w : F=>c⁻¹ • w)=_ at ht
  rw [ht,hm,withDensity_smul_measure,← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1

end
end SlowEquilibration.GaussianRegression
