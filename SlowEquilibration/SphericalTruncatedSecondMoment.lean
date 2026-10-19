-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTruncatedPartition
public import SlowEquilibration.SphericalPairPlanting

@[expose] public section

/-!
# Integrated second moment of the actual truncated spherical partition

The three-variable exponential is proved integrable under the literal Gaussian
disorder and two independent uniform sphere laws. Fubini and genuine pair
planting then identify the second moment with an integral of translated-event
probabilities and the exact overlap weight.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sphereLaw_pair_support {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ z : Vector N × Vector N ∂(sphereLaw N).prod (sphereLaw N),
      ‖z.1‖^2=(N : ℝ) ∧ ‖z.2‖^2=(N : ℝ) := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [sphereLaw_support hN] with u hu
  filter_upwards [sphereLaw_support hN] with v hv
  exact ⟨hu,hv⟩

private theorem exp_pair_le (a b : ℝ) :
    Real.exp a*Real.exp b ≤ Real.exp (2*a)+Real.exp (2*b) := by
  have ha : Real.exp (2*a)=(Real.exp a)^2 := by
    rw [two_mul,Real.exp_add,pow_two]
  have hb : Real.exp (2*b)=(Real.exp b)^2 := by
    rw [two_mul,Real.exp_add,pow_two]
  rw [ha,hb]
  nlinarith [sq_nonneg (Real.exp a-Real.exp b),sq_nonneg (Real.exp a+Real.exp b)]

theorem field_exp_pair_integrable {N P : ℕ} (c : Degree P → ℝ)
    (β : ℝ) (u v : Vector N) :
    Integrable (fun J : Disorder N P =>
      Real.exp (β*field c J u)*Real.exp (β*field c J v)) (disorderLaw N P) := by
  apply ((field_exp_integrable c u (2*β)).add (field_exp_integrable c v (2*β))).mono'
  · exact (Real.continuous_exp.comp (((field_jointContinuous c).comp (continuous_id.prodMk continuous_const)).const_mul β)).aestronglyMeasurable.mul
      (Real.continuous_exp.comp (((field_jointContinuous c).comp (continuous_id.prodMk continuous_const)).const_mul β)).aestronglyMeasurable
  · exact .of_forall fun J => by
      rw [Real.norm_of_nonneg (by positivity)]
      simpa only [mul_assoc,Pi.add_apply] using exp_pair_le (β*field c J u) (β*field c J v)

/-- Actual integrability needed for the disorder--spin--spin Fubini exchange. -/
theorem field_exp_pair_prod_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    Integrable (fun z : Disorder N P × (Vector N × Vector N) =>
      Real.exp (β*field c z.1 z.2.1)*Real.exp (β*field c z.1 z.2.2))
      ((disorderLaw N P).prod ((sphereLaw N).prod (sphereLaw N))) := by
  have hm : StronglyMeasurable (fun z : Disorder N P × (Vector N × Vector N) =>
      Real.exp (β*field c z.1 z.2.1)*Real.exp (β*field c z.1 z.2.2)) := by
    apply Continuous.stronglyMeasurable
    exact (Real.continuous_exp.comp (((field_jointContinuous c).comp (continuous_fst.prodMk continuous_snd.fst)).const_mul β)).mul
      (Real.continuous_exp.comp (((field_jointContinuous c).comp (continuous_fst.prodMk continuous_snd.snd)).const_mul β))
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun z => field_exp_pair_integrable c β z.1 z.2),?_⟩
  apply (integrable_const (2*Real.exp ((N : ℝ)*(2*β)^2*covariancePolynomial c 1/2))).mono'
    hm.norm.integral_prod_left'.aestronglyMeasurable
  filter_upwards [sphereLaw_pair_support hN] with z hz
  have hn : 0 ≤ ∫ J : Disorder N P,
      ‖Real.exp (β*field c J z.1)*Real.exp (β*field c J z.2)‖ ∂disorderLaw N P :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hn]
  calc
    _ ≤ ∫ J : Disorder N P,
        Real.exp ((2*β)*field c J z.1)+Real.exp ((2*β)*field c J z.2) ∂disorderLaw N P := by
      apply integral_mono (field_exp_pair_integrable c β z.1 z.2).norm
        ((field_exp_integrable c z.1 (2*β)).add (field_exp_integrable c z.2 (2*β)))
      intro J
      dsimp only
      rw [Real.norm_of_nonneg (by positivity)]
      simpa only [mul_assoc,Pi.add_apply] using exp_pair_le (β*field c J z.1) (β*field c J z.2)
    _ = _ := by
      rw [integral_add (field_exp_integrable c z.1 (2*β)) (field_exp_integrable c z.2 (2*β)),
        field_exp_integral_on_sphere (by omega) c hc z.1 hz.1,
        field_exp_integral_on_sphere (by omega) c hc z.2 hz.2]
      ring

theorem truncated_pair_prod_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    Integrable (fun z : Disorder N P × (Vector N × Vector N) =>
      T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (z.1,z.2.1)*
      T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (z.1,z.2.2))
      ((disorderLaw N P).prod ((sphereLaw N).prod (sphereLaw N))) := by
  let S : Set (Disorder N P × (Vector N × Vector N)) :=
    {z | (z.1,z.2.1) ∈ T ∧ (z.1,z.2.2) ∈ T}
  have hS : MeasurableSet S :=
    (hT.preimage (measurable_fst.prodMk measurable_snd.fst)).inter
      (hT.preimage (measurable_fst.prodMk measurable_snd.snd))
  convert (field_exp_pair_prod_integrable hN c hc β).indicator hS using 1
  funext z
  by_cases hu : (z.1,z.2.1) ∈ T <;> by_cases hv : (z.1,z.2.2) ∈ T <;>
    simp [S,hu,hv]

/-- Every measurable truncation has a finite genuine second moment. -/
theorem truncatedPartition_sq_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    Integrable (fun J => (truncatedPartition c β T J)^2) (disorderLaw N P) := by
  convert (truncated_pair_prod_integrable hN c hc β hT).integral_prod_left using 1
  funext J
  simpa only [truncatedPartition,pow_two] using
    (integral_prod_mul (μ := sphereLaw N) (ν := sphereLaw N)
      (fun x => T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (J,x))
      (fun x => T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (J,x))).symm

/-- Exact integrated two-point planting for the actual truncated partition. -/
theorem expected_truncatedPartition_sq {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {T : Set (Disorder N P × Vector N)} (hT : MeasurableSet T) :
    (∫ J, (truncatedPartition c β T J)^2 ∂disorderLaw N P) =
      ∫ z : Vector N × Vector N,
        Real.exp ((N : ℝ)*β^2*(covariancePolynomial c 1+covariancePolynomial c (overlap z.1 z.2)))*
          (disorderLaw N P).real {J |
            (J+plantedShift c β z.1+plantedShift c β z.2,z.1) ∈ T ∧
            (J+plantedShift c β z.1+plantedShift c β z.2,z.2) ∈ T}
        ∂(sphereLaw N).prod (sphereLaw N) := by
  have he : (fun J : Disorder N P => (truncatedPartition c β T J)^2) =
      fun J => ∫ z : Vector N × Vector N,
        T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (J,z.1)*
        T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (J,z.2)
        ∂(sphereLaw N).prod (sphereLaw N) := by
    funext J
    simpa only [truncatedPartition,pow_two] using
      (integral_prod_mul (μ := sphereLaw N) (ν := sphereLaw N)
        (fun x => T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (J,x))
        (fun x => T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (J,x))).symm
  rw [he,integral_integral_swap (truncated_pair_prod_integrable hN c hc β hT)]
  apply integral_congr_ae
  filter_upwards [sphereLaw_pair_support hN] with z hz
  exact pair_truncated_exponential_moment hN c hc β z.1 z.2 hz.1 hz.2 hT

end SlowEquilibration.SphericalModel
