-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledDerivativeLift
public import SlowEquilibration.SphericalInfiniteL2Generator

/-! Uniform difference-quotient bounds for the actual physical killed
expectation.  The correction is controlled by the genuine bounded hazard
and the ordinary physical Dynkin derivative. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalReversibility SphericalReversibility.Ito
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem killedExpectation_defect_norm_le {E Ω : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : E → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, ‖κ x‖ ≤ K)
    (X : ℝ≥0 → Ω → E) (hXm : Measurable (Function.uncurry X))
    (t : ℝ≥0) (f : E → ℝ) (hf : Continuous f) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, ‖f (X t ω)‖ ≤ C) :
    ‖killedExpectation P κ X t f - ∫ ω, f (X t ω) ∂P‖ ≤ K*t*C := by
  have hfm : StronglyMeasurable (fun ω => f (X t ω)) :=
    hf.comp_stronglyMeasurable (hXm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
  have hfi : Integrable (fun ω => f (X t ω)) P := Integrable.of_bound hfm.aestronglyMeasurable C hC
  have hwi : Integrable (fun ω => survival κ X t ω*f (X t ω)) P := by
    apply Integrable.of_bound ((survival_stronglyMeasurable κ hκ.measurable X hXm t).mul hfm).aestronglyMeasurable C
    filter_upwards [hC] with ω hω
    change ‖survival κ X t ω*f (X t ω)‖ ≤ C
    rw [norm_mul,Real.norm_of_nonneg (survival_nonneg κ X t ω)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (survival_le_one κ hκ0 X t ω)).trans hω
  rw [killedExpectation,← integral_sub hwi hfi]
  have hb : ∀ᵐ ω ∂P, ‖survival κ X t ω*f (X t ω)-f (X t ω)‖ ≤ K*t*C := by
    filter_upwards [hC] with ω hω
    have he : survival κ X t ω*f (X t ω)-f (X t ω) = (survival κ X t ω-1)*f (X t ω) := by ring
    rw [he,norm_mul]
    exact mul_le_mul (survival_defect_le κ hκ0 K hK X t ω) hω (norm_nonneg _)
      (mul_nonneg hK0 t.coe_nonneg)
  simpa only [Pi.sub_apply,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

variable {N : ℕ}

theorem source_ordinary_expectation (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) (t : ℝ≥0) :
    (∫ ω, f (sourceProcess μ J β x t ω) ∂VectorBrownian.law N) =
      SphericalC1Dynamics.expectation β (mixedGradient μ J)
        ((mixedGradient_contDiff μ J).of_le (by simp)) t f x := by
  rw [SphericalC1Dynamics.expectation_eq_mixed hN μ J β x hx,mixedExpectation_eq_actual]
  apply integral_congr_ae
  exact (sourceProcess_ae_actual μ J β x).mono (fun _ h => congrArg f (h t))

theorem sourceKilledExpectation_slope_norm_le (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, ‖κ x‖ ≤ K)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) (C M : ℝ)
    (hC : ∀ y, OnSphere y → ‖f y‖ ≤ C)
    (hM : ∀ y, OnSphere y → ‖coefficientGenerator β (mixedGradient μ J) f y‖ ≤ M)
    (x : Vector N) (hx : OnSphere x) (r : ℝ) (hr : 0 < r) :
    ‖slope (fun s : ℝ => sourceKilledExpectation μ J β κ s.toNNReal f x) 0 r‖ ≤ M+K*C := by
  let Q : ℝ → ℝ := fun s => sourceKilledExpectation μ J β κ s.toNNReal f x
  let E : ℝ → ℝ := fun s => SphericalC1Dynamics.expectation β (mixedGradient μ J)
    ((mixedGradient_contDiff μ J).of_le (by simp)) s.toNNReal f x
  have hdef : ‖Q r-E r‖ ≤ K*r*C := by
    have hb : ∀ᵐ ω ∂VectorBrownian.law N, ‖f (sourceProcess μ J β x r.toNNReal ω)‖ ≤ C :=
      (sourceProcess_onSphere hN μ J β x hx).mono (fun _ h => hC _ (h _))
    have hd := killedExpectation_defect_norm_le (VectorBrownian.law N) κ hκ hκ0 K hK0 hK
      (sourceProcess μ J β x) (sourceProcess_measurable μ J β x) r.toNNReal f hf.continuous C hb
    rw [Real.coe_toNNReal r hr.le,source_ordinary_expectation hN μ J β f x hx r.toNNReal] at hd
    exact hd
  have hzero : Q 0 = E 0 := by
    rw [show Q 0 = ∫ ω, f (sourceProcess μ J β x 0 ω) ∂VectorBrownian.law N by
      simp only [Q,sourceKilledExpectation,Real.toNNReal_zero,killedExpectation_zero]]
    dsimp only [E]
    rw [Real.toNNReal_zero]
    exact source_ordinary_expectation hN μ J β f x hx 0
  have hEq : slope Q 0 r = slope E 0 r+r⁻¹*(Q r-E r) := by
    simp only [slope_def_module,sub_zero,smul_eq_mul,hzero]
    ring
  have hs := SphericalC1Dynamics.expectation_slope_norm_le hN β (mixedGradient μ J)
    ((mixedGradient_contDiff μ J).of_le (by simp)) f hf M hM x hx r hr
  rw [hEq]
  calc
    _ ≤ ‖slope E 0 r‖+‖r⁻¹*(Q r-E r)‖ := norm_add_le _ _
    _ ≤ M+K*C := by
      apply add_le_add hs
      rw [norm_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left hdef (inv_nonneg.mpr hr.le)).trans_eq (by field_simp)

end SlowEquilibration.ConditionedEntrance.FeynmanKac
