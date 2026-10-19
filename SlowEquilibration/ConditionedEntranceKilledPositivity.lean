-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemigroupLaplaceRate
public import SlowEquilibration.ConditionedEntranceKilledL2
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Positivity of literal killed-kernel operators and their actual
Hilbert Laplace integrals, derived through nonnegative L² tests. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.KilledPositivity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {α : Type*} [MeasurableSpace α] {π : Measure α} [IsFiniteMeasure π]

omit [IsFiniteMeasure π] in
theorem lp_inner_nonneg (U W : Lp ℝ 2 π)
    (hU : ∀ᵐ x ∂π, 0 ≤ U x) (hW : ∀ᵐ x ∂π, 0 ≤ W x) :
    0 ≤ inner ℝ U W := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hU,hW] with x hu hw
  simpa only [RCLike.inner_apply,conj_trivial,Pi.zero_apply] using mul_nonneg hw hu

theorem lp_nonneg_of_inner (U : Lp ℝ 2 π)
    (hU : ∀ W : Lp ℝ 2 π, (∀ᵐ x ∂π,0 ≤ W x) → 0 ≤ inner ℝ U W) :
    ∀ᵐ x ∂π,0 ≤ U x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp U).integrable (by norm_num))
  intro s hs hms
  let W : Lp ℝ 2 π := indicatorConstLp 2 hs hms.ne 1
  have hW : ∀ᵐ x ∂π,0 ≤ W x := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hms.ne) (c := (1 : ℝ))] with x hx
    change W x=s.indicator (fun _ => (1 : ℝ)) x at hx
    rw [hx]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have he : inner ℝ U W=∫ x in s,U x ∂π := by
    rw [L2.inner_def,← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hms.ne) (c := (1 : ℝ))] with x hx
    change W x=s.indicator (fun _ => (1 : ℝ)) x at hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
    by_cases hxs : x∈s <;> simp [Set.indicator,hxs]
  exact he ▸ hU W hW

omit [IsFiniteMeasure π] in
theorem kernel_operator_nonneg [IsProbabilityMeasure π] (K : Kernel α α) [IsFiniteKernel K]
    (hmass : ∀ x,K x univ ≤ 1) (hsub : K ∘ₘ π ≤ π)
    (U : Lp ℝ 2 π) (hU : ∀ᵐ x ∂π,0 ≤ U x) :
    ∀ᵐ x ∂π,0 ≤ KilledL2.operator π K hmass hsub U x := by
  have hslice := Measure.ae_ae_of_ae_comp ((ae_mono hsub) hU)
  filter_upwards [KilledL2.operator_ae π K hmass hsub U,hslice] with x hx hu
  rw [hx]
  exact integral_nonneg_of_ae hu

theorem laplace_nonneg (S : SemigroupLaplace.Data (Lp ℝ 2 π))
    (hP : ∀ t U, (∀ᵐ x ∂π,0 ≤ U x) → ∀ᵐ x ∂π,0 ≤ S.P t U x)
    (U : Lp ℝ 2 π) (hU : ∀ᵐ x ∂π,0 ≤ U x) :
    ∀ᵐ x ∂π,0 ≤ S.operator U x := by
  apply lp_nonneg_of_inner
  intro W hW
  rw [S.inner_operator_left]
  apply integral_nonneg
  intro t
  change 0 ≤ inner ℝ (Real.exp (-t) • S.P t.toNNReal U) W
  rw [real_inner_smul_left]
  exact mul_nonneg (Real.exp_pos _).le (lp_inner_nonneg _ W (hP _ U hU) hW)

theorem rateLaplace_nonneg (S : SemigroupLaplace.Data (Lp ℝ 2 π))
    (hP : ∀ t U, (∀ᵐ x ∂π,0 ≤ U x) → ∀ᵐ x ∂π,0 ≤ S.P t U x)
    (θ : ℝ≥0) (U : Lp ℝ 2 π) (hU : ∀ᵐ x ∂π,0 ≤ U x) :
    ∀ᵐ x ∂π,0 ≤ S.rateOperator θ U x := by
  have hpos := laplace_nonneg (S.timeRescale θ) (fun t V hV => hP _ V hV) U hU
  filter_upwards [hpos,Lp.coeFn_smul ((θ : ℝ)⁻¹) ((S.timeRescale θ).operator U)] with x hx hsmul
  change 0 ≤ (((θ : ℝ)⁻¹) • (S.timeRescale θ).operator U) x
  rw [hsmul,Pi.smul_apply,smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr θ.coe_nonneg) hx

end SlowEquilibration.ConditionedEntrance.KilledPositivity
