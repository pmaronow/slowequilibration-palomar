-- SPDX-License-Identifier: Apache-2.0
module

public import SphericalAging.WeightedDriftSums
public import SlowEquilibration.SphericalC1FiniteBridge
public import SlowEquilibration.SphericalDisorderPathKernel
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Literal bounded killing weights on the actual physical paths.  In
particular, the first-order multiplication term is derived from the time
integral of the killing coefficient; it is not a resolvent premise. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging WeightedDriftSums
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {E Ω : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
  [MeasurableSpace Ω]

/-- The genuine Lebesgue occupation integral, including every null path. -/
def occupation (κ : E → ℝ) (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), κ (X s.toNNReal ω)

/-- Surviving an independent unit-exponential hazard threshold has this
literal path weight.  No semigroup or differential equation is used here. -/
def survival (κ : E → ℝ) (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-occupation κ X t ω)

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [MeasurableSpace Ω] in
@[simp] theorem occupation_zero (κ : E → ℝ) (X : ℝ≥0 → Ω → E) (ω : Ω) :
    occupation κ X 0 ω = 0 := by simp [occupation]

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [MeasurableSpace Ω] in
@[simp] theorem survival_zero (κ : E → ℝ) (X : ℝ≥0 → Ω → E) (ω : Ω) :
    survival κ X 0 ω = 1 := by simp [survival]

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem occupation_nonneg (κ : E → ℝ) (hκ : ∀ x, 0 ≤ κ x)
    (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : 0 ≤ occupation κ X t ω := by
  exact intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => hκ _)

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem occupation_norm_le (κ : E → ℝ) (K : ℝ) (hK : ∀ x, ‖κ x‖ ≤ K)
    (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) :
    ‖occupation κ X t ω‖ ≤ K * t := by
  simpa only [occupation,sub_zero,abs_of_nonneg t.coe_nonneg] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (t : ℝ)) (fun s _ => hK _)

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem survival_nonneg (κ : E → ℝ) (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) :
    0 ≤ survival κ X t ω := (Real.exp_pos _).le

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem survival_le_one (κ : E → ℝ) (hκ : ∀ x, 0 ≤ κ x)
    (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : survival κ X t ω ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (occupation_nonneg κ hκ X t ω))

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem survival_defect_le (κ : E → ℝ) (hκ : ∀ x, 0 ≤ κ x)
    (K : ℝ) (hK : ∀ x, ‖κ x‖ ≤ K) (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) :
    ‖survival κ X t ω - 1‖ ≤ K * t := by
  rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (survival_le_one κ hκ X t ω))]
  have he := Real.add_one_le_exp (-occupation κ X t ω)
  have hb := (le_abs_self (occupation κ X t ω)).trans (occupation_norm_le κ K hK X t ω)
  change -(Real.exp (-occupation κ X t ω)-1) ≤ _
  linarith

omit [TopologicalSpace E] [BorelSpace E] in
theorem occupation_stronglyMeasurable (κ : E → ℝ) (hκ : Measurable κ)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X)) (t : ℝ≥0) :
    StronglyMeasurable (occupation κ X t) := by
  have hm : Measurable (Function.uncurry (fun s ω => κ (X s ω))) := hκ.comp hX
  convert stronglyMeasurable_integratedDrift (fun s ω => κ (X s ω)) hm t using 1
  funext ω
  rw [occupation,StochasticCalculus.integratedDrift,
    intervalIntegral.integral_of_le t.coe_nonneg,integral_Icc_eq_integral_Ioc]

omit [TopologicalSpace E] [BorelSpace E] in
theorem survival_stronglyMeasurable (κ : E → ℝ) (hκ : Measurable κ)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X)) (t : ℝ≥0) :
    StronglyMeasurable (survival κ X t) :=
  Real.continuous_exp.comp_stronglyMeasurable
    ((occupation_stronglyMeasurable κ hκ X hX t).neg)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
/-- The multiplication part of the killed generator follows directly
from the fundamental theorem of calculus along each continuous path. -/
theorem survival_hasDerivWithinAt_zero (κ : E → ℝ) (hκ : Continuous κ)
    (X : ℝ≥0 → Ω → E) (ω : Ω) (hX : Continuous (fun t => X t ω)) :
    HasDerivWithinAt (fun r : ℝ => survival κ X r.toNNReal ω)
      (-κ (X 0 ω)) (Ici 0) 0 := by
  let g : ℝ → ℝ := fun r => κ (X r.toNNReal ω)
  have hg : Continuous g := hκ.comp (hX.comp continuous_real_toNNReal)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable (0 : ℝ) 0)
    (hg.stronglyMeasurableAtFilter volume (𝓝 (0 : ℝ))) hg.continuousAt
  have he := hd.neg.exp
  simp only [Pi.neg_apply,intervalIntegral.integral_same,neg_zero,Real.exp_zero,one_mul,
    g,Real.toNNReal_zero] at he
  apply he.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [survival,occupation,Real.coe_toNNReal r hr]
  · simp [survival]

variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Genuine path-weighted expectation. -/
def killedExpectation (κ : E → ℝ) (X : ℝ≥0 → Ω → E) (t : ℝ≥0)
    (f : E → ℝ) : ℝ := ∫ ω, survival κ X t ω * f (X t ω) ∂P

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
theorem killedExpectation_zero (κ : E → ℝ) (X : ℝ≥0 → Ω → E)
    (f : E → ℝ) : killedExpectation P κ X 0 f = ∫ ω, f (X 0 ω) ∂P := by
  simp [killedExpectation]

omit [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] in
/-- Domination is against the actual physical law on the same paths. -/
theorem killedExpectation_norm_le (κ : E → ℝ) (hκ : ∀ x, 0 ≤ κ x)
    (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (f : E → ℝ) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, ‖f (X t ω)‖ ≤ C) :
    ‖killedExpectation P κ X t f‖ ≤ C := by
  have hb : ∀ᵐ ω ∂P, ‖survival κ X t ω * f (X t ω)‖ ≤ C := by
    filter_upwards [hC] with ω hω
    rw [norm_mul,Real.norm_of_nonneg (survival_nonneg κ X t ω)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (survival_le_one κ hκ X t ω)).trans hω
  simpa only [killedExpectation,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const hb

end SlowEquilibration.ConditionedEntrance.FeynmanKac
