-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledPhysicalSemigroup
public import SlowEquilibration.SemigroupLaplace

/-! Strong continuity of the actual physically killed Gibbs L²
semigroup, derived from continuous diffusion paths and bounded survival
weights, followed by the genuine smooth density argument. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics SphericalReversibility
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem occupation_continuous {E Ω : Type*} [TopologicalSpace E]
    (κ : E → ℝ) (hκ : Continuous κ) (X : ℝ≥0 → Ω → E) (ω : Ω)
    (hX : Continuous (fun r => X r ω)) : Continuous (fun t => occupation κ X t ω) := by
  have hg : Continuous (fun r : ℝ => κ (X r.toNNReal ω)) :=
    hκ.comp (hX.comp continuous_real_toNNReal)
  exact (intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

theorem survival_continuous {E Ω : Type*} [TopologicalSpace E]
    (κ : E → ℝ) (hκ : Continuous κ) (X : ℝ≥0 → Ω → E) (ω : Ω)
    (hX : Continuous (fun r => X r ω)) : Continuous (fun t => survival κ X t ω) :=
  Real.continuous_exp.comp (occupation_continuous κ hκ X ω hX).neg

theorem killedExpectation_time_continuous {E Ω : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : E → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (X : ℝ≥0 → Ω → E) (hXm : Measurable (Function.uncurry X))
    (hXc : ∀ᵐ ω ∂P, Continuous (fun r => X r ω)) (f : E → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) : Continuous (fun t => killedExpectation P κ X t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · apply Filter.Eventually.of_forall
    intro t
    exact ((survival_stronglyMeasurable κ hκ.measurable X hXm t).mul
      (hf.comp_stronglyMeasurable (hXm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)).aestronglyMeasurable
  · exact .of_forall (fun t => .of_forall (fun ω => by
      rw [norm_mul,Real.norm_of_nonneg (survival_nonneg κ X t ω)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (survival_le_one κ hκ0 X t ω)).trans (hC _)))
  · exact integrable_const C
  · filter_upwards [hXc] with ω hc
    exact ((survival_continuous κ hκ X ω hc).mul (hf.comp hc)).continuousAt.tendsto

variable {N : ℕ}

theorem sourceKilledExpectation_time_continuous (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (f : Vector N → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : Vector N) :
    Continuous (fun t => sourceKilledExpectation μ J β κ t f x) :=
  killedExpectation_time_continuous (VectorBrownian.law N) κ hκ hκ0
    (sourceProcess μ J β x) (sourceProcess_measurable μ J β x)
    (sourceProcess_ae_continuous μ J β x) f hf C hC

theorem sourceKilledExpectation_stronglyMeasurable (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (t : ℝ≥0)
    (f : Vector N → ℝ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (sourceKilledExpectation μ J β κ t f) := by
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 t
  have h := hf.integral_kernel (κ := sourceKilledKernel μ J β κ hκ t)
  convert h using 1
  exact (funext (sourceKilledKernel_integral_actual μ J β κ hκ t f hf)).symm

theorem sourceKilledKernel_zero (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (x : Vector N) :
    sourceKilledKernel μ J β κ hκ 0 x = Measure.dirac x := by
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 0
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [sourceKilledKernel_integral_actual μ J β κ hκ 0 f f.continuous.stronglyMeasurable x,
    sourceKilledExpectation_eq_actual]
  simp only [survival_zero,one_mul]
  rw [integral_congr_ae ((mixedProcess_zero μ J β x).mono (fun _ h => congrArg f h))]
  simp

theorem sourceKilledOperator_zero (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) :
    sourceKilledOperator hN μ J β κ hκ hκ0 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro U
  apply Lp.ext
  filter_upwards [sourceKilledOperator_ae hN μ J β κ hκ hκ0 0 U] with x hx
  rw [hx,sourceKilledKernel_zero μ J β κ hκ hκ0 x]
  exact integral_dirac U x

end SlowEquilibration.ConditionedEntrance.FeynmanKac
