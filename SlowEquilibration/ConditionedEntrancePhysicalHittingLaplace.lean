-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalHittingBound

/-! Exact Fubini identification of the actual finite firing mass with the
finite discounted killed-kernel integral used by rate-Laplace pairing. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open MeasureTheory ProbabilityTheory Set Filter
open FeynmanKac
open scoped NNReal ENNReal
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]

/-- The finite physical discounted hazard expectation is exactly the
finite rate-Laplace integral of the actual killed expectations. -/
theorem finiteDiscountedMass_expectation_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : E → ℝ) (hκ : Measurable κ) (hκ0 : ∀ y,0 ≤ κ y) (hκ1 : ∀ y,κ y ≤ 1)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    {θ : ℝ} (hθ : 0 ≤ θ) (L : ℝ≥0) :
    (∫ omega,finiteDiscountedMass κ X θ L omega ∂P) =
      ∫ t in (0 : ℝ)..(L : ℝ),Real.exp (-θ * t) * killedExpectation P κ X t.toNNReal κ := by
  let J : ℝ × Ω → ℝ := fun q => Real.exp (-θ * q.1) * κ (X q.1.toNNReal q.2) * survival κ X q.1.toNNReal q.2
  let μ := volume.restrict (Ioc (0 : ℝ) (L : ℝ))
  have hm : Measurable (fun q : ℝ × Ω => (q.1.toNNReal,q.2)) := by fun_prop
  have hJ : StronglyMeasurable J :=
    (((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).stronglyMeasurable).mul
      (((hκ.comp hX).comp hm).stronglyMeasurable)).mul
      ((survival_joint_stronglyMeasurable κ hκ X hX).comp_measurable hm)
  have hi : Integrable J (μ.prod P) := by
    apply Integrable.of_bound hJ.aestronglyMeasurable 1
    have htime : ∀ᵐ q ∂μ.prod P,q.1 ∈ Ioc (0 : ℝ) (L : ℝ) :=
      (measurePreserving_fst (μ := μ) (ν := P)).quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [htime] with q hq
    have he : Real.exp (-θ * q.1) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hq.1])
    have hs := survival_le_one κ hκ0 X q.1.toNNReal q.2
    dsimp [J]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (hκ0 _)) (survival_nonneg κ X _ _))]
    exact (mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le (hκ0 _)) hs).trans
      ((mul_le_of_le_one_left (hκ0 _) he).trans (hκ1 _))
  have he (t : ℝ) : (∫ omega,J (t,omega) ∂P) = Real.exp (-θ * t) * killedExpectation P κ X t.toNNReal κ := by
    unfold killedExpectation
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun omega => by dsimp [J]; ring
  calc
    _ = ∫ omega,∫ t,J (t,omega) ∂μ ∂P := by
      apply integral_congr_ae
      exact .of_forall fun omega => by
        unfold finiteDiscountedMass
        rw [intervalIntegral.integral_of_le L.coe_nonneg]
    _ = ∫ t,∫ omega,J (t,omega) ∂P ∂μ := (integral_integral_swap hi).symm
    _ = ∫ t,Real.exp (-θ * t) * killedExpectation P κ X t.toNNReal κ ∂μ := integral_congr_ae (.of_forall he)
    _ = _ := by rw [intervalIntegral.integral_of_le L.coe_nonneg]

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
