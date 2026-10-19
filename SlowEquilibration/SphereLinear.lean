-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereVolume
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The actual linear-field spherical partition function and its radial
monotonicity. The measure is the proved Gaussian-direction / angular Haar law. -/

@[expose] public section
namespace SlowEquilibration.SphereLinear
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open SphereVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Normalized angular volume viewed in its ordinary ambient vector space. -/
def directionLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  (unitAngular E).map Subtype.val

instance directionLaw_probability : IsProbabilityMeasure (directionLaw E) :=
  inferInstanceAs (IsProbabilityMeasure ((unitAngular E).map Subtype.val))

theorem directionLaw_eq_gaussian :
    directionLaw E = (stdGaussian E).map (SphereVolume.normalize 1) := by
  simpa only [directionLaw, one_smul] using (normalizedGaussian_eq_angular (E := E) 1).symm

theorem directionLaw_norm : ∀ᵐ x ∂directionLaw E, ‖x‖ = 1 := by
  rw [directionLaw]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_eq_fun measurable_norm measurable_const)).mpr
    (Filter.Eventually.of_forall fun u => by simpa only [Metric.mem_sphere, dist_zero_right] using u.property)

theorem directionLaw_neg : (directionLaw E).map Neg.neg = directionLaw E := by
  rw [directionLaw_eq_gaussian, Measure.map_map (by fun_prop) (by unfold SphereVolume.normalize; fun_prop)]
  have he : (Neg.neg ∘ SphereVolume.normalize (1 : ℝ) : E → E) = SphereVolume.normalize 1 ∘ Neg.neg := by
    funext x
    simp [SphereVolume.normalize, Function.comp_def]
  rw [he, ← Measure.map_map (by unfold SphereVolume.normalize; fun_prop) (by fun_prop)]
  have hn : (stdGaussian E).map Neg.neg = stdGaussian E :=
    stdGaussian_map (LinearIsometryEquiv.neg ℝ (E := E))
  rw [hn]

theorem integrable_exp (w : E) (r : ℝ) :
    Integrable (fun x => Real.exp (r * inner ℝ w x)) (directionLaw E) := by
  apply (integrable_const (Real.exp (|r| * ‖w‖))).mono' (by fun_prop)
  filter_upwards [directionLaw_norm (E := E)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    r * inner ℝ w x ≤ |r * inner ℝ w x| := le_abs_self _
    _ = |r| * |inner ℝ w x| := abs_mul _ _
    _ ≤ |r| * (‖w‖ * ‖x‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ = _ := by rw [hx, mul_one]

/-- Exact partition function of a linear field on the radius-r sphere. -/
def partition (w : E) (r : ℝ) : ℝ :=
  ∫ x, Real.exp (r * inner ℝ w x) ∂directionLaw E

theorem partition_even (w : E) (r : ℝ) : partition w (-r) = partition w r := by
  have hi := integral_map (μ := directionLaw E) (φ := (Neg.neg : E → E))
    (by fun_prop) (by fun_prop : AEStronglyMeasurable (fun x : E => Real.exp (r * inner ℝ w x))
      ((directionLaw E).map Neg.neg))
  rw [directionLaw_neg] at hi
  simpa only [partition, inner_neg_right, mul_neg, neg_mul] using hi.symm

theorem integrable_cosh (w : E) (r : ℝ) :
    Integrable (fun x => Real.cosh (r * inner ℝ w x)) (directionLaw E) := by
  simpa only [Real.cosh_eq, neg_mul, Pi.add_apply] using ((integrable_exp w r).add (integrable_exp w (-r))).div_const 2

theorem partition_eq_cosh (w : E) (r : ℝ) :
    partition w r = ∫ x, Real.cosh (r * inner ℝ w x) ∂directionLaw E := by
  simp only [Real.cosh_eq]
  rw [integral_div, integral_add (integrable_exp w r) (by simpa only [neg_mul] using integrable_exp w (-r))]
  simp only [← neg_mul]
  change partition w r = (partition w r + partition w (-r)) / 2
  rw [partition_even]
  ring

theorem partition_mono_radius (w : E) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    partition w r ≤ partition w s := by
  rw [partition_eq_cosh, partition_eq_cosh]
  apply integral_mono (integrable_cosh w r) (integrable_cosh w s)
  intro x
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg (hr.trans hrs)]
  exact mul_le_mul_of_nonneg_right hrs (abs_nonneg _)

theorem partition_one_le (w : E) (r : ℝ) : 1 ≤ partition w r := by
  rw [partition_eq_cosh]
  have h := integral_mono (integrable_const (1 : ℝ)) (integrable_cosh w r)
    (fun x => Real.one_le_cosh (r * inner ℝ w x))
  simpa using h

theorem partition_pos (w : E) (r : ℝ) : 0 < partition w r :=
  lt_of_lt_of_le zero_lt_one (partition_one_le w r)

omit [Nontrivial E] in
theorem partition_eq_angular (w : E) (r : ℝ) :
    partition w r = ∫ u : Metric.sphere (0 : E) 1,
      Real.exp (r * inner ℝ w (u : E)) ∂unitAngular E := by
  exact integral_map measurable_subtype_coe.aemeasurable (by fun_prop)

end
end SlowEquilibration.SphereLinear
