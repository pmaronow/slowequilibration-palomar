module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.ConditionedEntranceResolventEnergy
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Converting a genuine killing-time Laplace transform into a horizon bound

The random time may equal infinity. Its contribution to the transform is
literally zero there. This proves the probability-to-transform step and the
constant `14` in `eq:ent-resolvent-horizon`, conditional only on the source
Laplace-transform inequality. The identification of that transform with the
killed operator resolvent is a separate unfinished prerequisite.
-/

namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual killing-time transform, with zero contribution at infinity. -/
def killingLaplace (τ : Ω → ℝ≥0∞) (T : ℝ) (ω : Ω) : ℝ :=
  if τ ω = ∞ then 0 else Real.exp (-(τ ω).toReal / T)

omit [MeasurableSpace Ω] in
lemma killingLaplace_nonneg (τ : Ω → ℝ≥0∞) (T : ℝ) (ω : Ω) :
    0 ≤ killingLaplace τ T ω := by
  unfold killingLaplace
  split_ifs <;> positivity

omit [MeasurableSpace Ω] in
lemma killingLaplace_le_one (τ : Ω → ℝ≥0∞) {T : ℝ} (hT : 0 < T) (ω : Ω) :
    killingLaplace τ T ω ≤ 1 := by
  unfold killingLaplace
  split_ifs
  · norm_num
  · apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ENNReal.toReal_nonneg) hT.le

lemma killingLaplace_measurable {τ : Ω → ℝ≥0∞} (hτ : Measurable τ) (T : ℝ) :
    Measurable (killingLaplace τ T) := by
  exact Measurable.ite (hτ (measurableSet_singleton ∞)) measurable_const
    ((hτ.ennreal_toReal.neg.div_const T).exp)

lemma killingLaplace_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    {τ : Ω → ℝ≥0∞} (hτ : Measurable τ) {T : ℝ} (hT : 0 < T) :
    Integrable (killingLaplace τ T) μ := by
  apply (integrable_const (μ := μ) (1 : ℝ)).mono'
    (killingLaplace_measurable hτ T).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (killingLaplace_nonneg _ _ _)]
    exact killingLaplace_le_one τ hT ω

/-- The exact `1_{τ≤T} ≤ e exp(-τ/T)` probability implication, including
an infinite killing time. No stochastic identification is assumed. -/
theorem killing_probability_le_exp_one_transform (μ : Measure Ω) [IsFiniteMeasure μ]
    {τ : Ω → ℝ≥0∞} (hτ : Measurable τ) {T : ℝ} (hT : 0 < T) :
    μ.real {ω | τ ω ≤ ENNReal.ofReal T} ≤
      Real.exp 1 * ∫ ω, killingLaplace τ T ω ∂μ := by
  have hsub : {ω | τ ω ≤ ENNReal.ofReal T} ⊆
      {ω | Real.exp (-1) ≤ killingLaplace τ T ω} := by
    intro ω hω
    have hfin : τ ω ≠ ∞ := ne_of_lt (lt_of_le_of_lt hω ENNReal.ofReal_lt_top)
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
    rw [ENNReal.toReal_ofReal hT.le] at ht
    change Real.exp (-1) ≤ killingLaplace τ T ω
    rw [killingLaplace, ite_eq_right hfin]
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hT).2
    linarith
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (killingLaplace_nonneg τ T))
    (killingLaplace_integrable μ hτ hT) (Real.exp (-1))
  have hh := (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos (-1)).le).trans hm
  have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos 1).le
  have he : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  simpa only [← mul_assoc, he, one_mul] using hh'

/-- The source constant `14` follows from its transform inequality and the
proved root-error simplification. This result does not supply the missing
killed-resolvent identification as an implicit hypothesis. -/
theorem killing_horizon_of_resolvent_transform (μ : Measure Ω) [IsFiniteMeasure μ]
    {τ : Ω → ℝ≥0∞} (hτ : Measurable τ) {T η ε H R : ℝ} (hT : 0 < T)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (htransform : (∫ ω, killingLaplace τ T ω ∂μ) ≤
      4 * η + 5 * Real.sqrt ε + R +
        2 * Real.sqrt (ε * H * (R + ε * (1 + H)))) :
    μ.real {ω | τ ω ≤ ENNReal.ofReal T} ≤
      14 * (η + Real.sqrt ε + ε * (1 + H) + R) := by
  have hp := killing_probability_le_exp_one_transform μ hτ hT
  have hs := resolvent_root_error_simplification hε hH hR
  have htrans : (∫ ω, killingLaplace τ T ω ∂μ) ≤
      4 * η + 5 * Real.sqrt ε + 2 * R + 3 * ε * (1 + H) := by linarith
  have hbound := mul_le_mul_of_nonneg_left htrans (Real.exp_pos 1).le
  have he : Real.exp 1 ≤ (14 / 5 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hc := mul_le_mul_of_nonneg_right he
    (show 0 ≤ 4 * η + 5 * Real.sqrt ε + 2 * R + 3 * ε * (1 + H) by positivity)
  have hn := Real.sqrt_nonneg ε
  have ht : 0 ≤ ε * (1 + H) := by positivity
  linarith

end
end SlowEquilibration.ConditionedEntrance
