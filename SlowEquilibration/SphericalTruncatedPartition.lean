-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedShift

@[expose] public section

/-!
# Actual spherical truncated partitions and planted first moments

The truncation is a measurable event in the actual disorder--spin product.
The partition, its expectation and the planted probability below are ordinary
integrals and measures. The event's typicality probability is an explicit input;
no replica-symmetric or one-step lower bound is supplied as an assumption.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal partition restricted to a disorder-dependent set of spins. -/
def truncatedPartition {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (T : Set (Disorder N P × Vector N)) (J : Disorder N P) : ℝ :=
  ∫ x, T.indicator (fun z => Real.exp (β*field c z.1 z.2)) (J,x) ∂sphereLaw N

theorem truncatedPartition_measurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    Measurable (truncatedPartition c β T) := by
  have hf : StronglyMeasurable (T.indicator
      (fun z : Disorder N P × Vector N => Real.exp (β*field c z.1 z.2))) :=
    ((Real.continuous_exp.comp (continuous_const.mul (field_jointContinuous c))).stronglyMeasurable).indicator hT
  exact hf.integral_prod_right'.measurable

theorem truncatedPartition_nonneg {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (T : Set (Disorder N P × Vector N)) (J : Disorder N P) :
    0 ≤ truncatedPartition c β T J := by
  apply integral_nonneg
  intro x
  by_cases hx : (J,x) ∈ T <;> simp [hx, Real.exp_nonneg]

theorem truncatedPartition_le_partition {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) {T : Set (Disorder N P × Vector N)}
    (hT : MeasurableSet T) (J : Disorder N P) :
    truncatedPartition c β T J ≤ partition N β (field c J) := by
  have hs : MeasurableSet {x : Vector N | (J,x) ∈ T} :=
    hT.preimage (measurable_const.prodMk measurable_id)
  have hi := partition_integrand_integrable hN β (field_contDiff c J).continuous
  have he : (fun x : Vector N => T.indicator
      (fun z : Disorder N P × Vector N => Real.exp (β*field c z.1 z.2)) (J,x)) =
      {x : Vector N | (J,x) ∈ T}.indicator (fun x => Real.exp (β*field c J x)) := by
    funext x
    by_cases hx : (J,x) ∈ T <;> simp [hx]
  unfold truncatedPartition partition
  rw [he]
  apply integral_mono (hi.indicator hs) hi
  intro x
  by_cases hx : (J,x) ∈ T <;> simp [hx, Real.exp_nonneg]

theorem truncatedPartition_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    Integrable (truncatedPartition c β T) (disorderLaw N P) :=
  (field_exp_prod_integrable hN c hc β).indicator hT |>.integral_prod_left

/-- Real probability of the actual exponential tilt, computed as an ordinary
restricted integral of its actual density. -/
theorem plantedLaw_real_eq_integral {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    (plantedLaw c β).real T =
      ∫ z in T, plantedDensity c β z ∂((disorderLaw N P).prod (sphereLaw N)) := by
  unfold Measure.real plantedLaw
  have hn : 0 ≤ ∫ z in T, plantedDensity c β z ∂((disorderLaw N P).prod (sphereLaw N)) :=
    integral_nonneg (fun z => (Real.exp_pos _).le)
  rw [withDensity_apply _ hT,
    ← ofReal_integral_eq_lintegral_ofReal (plantedDensity_integrable hN c hc β).restrict
      (ae_of_all _ (fun z => (Real.exp_pos _).le)),
    ENNReal.toReal_ofReal hn]

/-- The exact first moment of a genuine truncated spherical partition is its
annealed normalization times the actual planted mass of the truncation. -/
theorem expected_truncatedPartition {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    (∫ J, truncatedPartition c β T J ∂disorderLaw N P) =
      Real.exp (annealedExponent N c β)*(plantedLaw c β).real T := by
  have hi := (field_exp_prod_integrable hN c hc β).indicator hT
  unfold truncatedPartition
  rw [← integral_prod _ hi, integral_indicator hT, plantedLaw_real_eq_integral hN c hc β hT,
    ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun z => by
    unfold plantedDensity
    change Real.exp (β*field c z.1 z.2) =
      Real.exp (annealedExponent N c β)*Real.exp (β*field c z.1 z.2-annealedExponent N c β)
    rw [← Real.exp_add]
    congr 1
    ring

/-- True planted typicality gives the first moment needed by the truncated
second-moment method, with the exact Gaussian normalization. -/
theorem expected_truncatedPartition_lower {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T)
    {p : ℝ} (hp : p ≤ (plantedLaw c β).real T) :
    p*Real.exp (annealedExponent N c β) ≤
      ∫ J, truncatedPartition c β T J ∂disorderLaw N P := by
  rw [expected_truncatedPartition hN c hc β hT]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le

/-- The planted mass of any measurable whole-disorder event equals its
ordinary probability after the genuine covariance translation, averaged over
the actual uniform sphere law. This is the literal planting step used in
truncated typicality arguments. -/
theorem plantedLaw_real_eq_shift_probability {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    (plantedLaw c β).real T =
      ∫ x, (disorderLaw N P).real
        {J : Disorder N P | (J+plantedShift c β x,x) ∈ T} ∂sphereLaw N := by
  have hi := (plantedDensity_integrable hN c hc β).indicator hT
  rw [plantedLaw_real_eq_integral hN c hc β hT, ← integral_indicator hT,
    integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  let F : Disorder N P → ℝ := fun J => T.indicator (fun _ => (1 : ℝ)) (J,x)
  have hF : Measurable F :=
    (measurable_const.indicator hT).comp (measurable_id.prodMk measurable_const)
  have he : (fun J : Disorder N P => T.indicator (plantedDensity c β) (J,x)) =
      fun J => F J*plantedDensity c β (J,x) := by
    funext J
    by_cases hJ : (J,x) ∈ T <;> simp [F,hJ]
  rw [he, planted_disorder_shift_integral hN c hc β x hx F hF]
  have hs : MeasurableSet {J : Disorder N P | (J+plantedShift c β x,x) ∈ T} :=
    hT.preimage ((measurable_id.add measurable_const).prodMk measurable_const)
  have hfshift : (fun J : Disorder N P => F (J+plantedShift c β x)) =
      {J : Disorder N P | (J+plantedShift c β x,x) ∈ T}.indicator (fun _ => (1 : ℝ)) := by
    funext J
    by_cases hJ : (J+plantedShift c β x,x) ∈ T <;> simp [F,hJ]
  rw [hfshift, integral_indicator hs]
  simp

end SlowEquilibration.SphericalModel
