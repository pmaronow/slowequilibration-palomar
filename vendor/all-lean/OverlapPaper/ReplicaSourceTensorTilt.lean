module
public import OverlapPaper.ReplicaSourceTensor
public import OverlapPaper.ReplicaSourceRecursion
public import Mathlib.Probability.Moments.Tilted

@[expose] public section

/-! Exact product factorization of logarithmic averages and normalized
exponential tilts. This is the analytic block factorization used by the
finite-replica vector baseline recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators
namespace OverlapPaper
variable {ι A : Type*} [Fintype ι] [MeasurableSpace A]

theorem sourceLogAverage_pi_sum (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ℝ) (f : ι → A → ℝ) (hm : ∀ i, Measurable (f i))
    (hi : ∀ i, Integrable (f i) (μ i))
    (he : ∀ i, Integrable (fun x => Real.exp (a * f i x)) (μ i)) :
    sourceLogAverage (Measure.pi μ) a (fun x => ∑ i, f i (x i)) =
      ∑ i, sourceLogAverage (μ i) a (f i) := by
  classical
  by_cases ha : a = 0
  · simp only [sourceLogAverage, ha, ite_true]
    have hil (i : ι) : Integrable (fun x : ι → A => f i (x i)) (Measure.pi μ) :=
      (measurePreserving_eval μ i).hasLaw.integrable_comp (hi i)
    rw [integral_finsetSum Finset.univ (fun i _ => hil i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (measurePreserving_eval μ i).hasLaw.integral_comp (hm i).aestronglyMeasurable
  · have hI : (∫ x, Real.exp (a * ∑ i, f i (x i)) ∂Measure.pi μ) =
        ∏ i, ∫ x, Real.exp (a * f i x) ∂μ i := by
      simp_rw [Finset.mul_sum, Real.exp_sum]
      exact integral_fintype_prod_eq_prod (μ := μ) (fun i x => Real.exp (a * f i x))
    simp only [sourceLogAverage, ha, ite_false, hI]
    rw [Real.log_prod (fun i _ => (integral_exp_pos (he i)).ne'), Finset.sum_div]

theorem tilted_pi_sum (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → A → ℝ) (hm : ∀ i, Measurable (f i))
    (he : ∀ i, Integrable (fun x => Real.exp (f i x)) (μ i)) :
    (Measure.pi μ).tilted (fun x => ∑ i, f i (x i)) =
      Measure.pi (fun i => (μ i).tilted (f i)) := by
  classical
  haveI (i : ι) : IsProbabilityMeasure ((μ i).tilted (f i)) := isProbabilityMeasure_tilted (he i)
  have hI : (∫ x, Real.exp (∑ i, f i (x i)) ∂Measure.pi μ) =
      ∏ i, ∫ x, Real.exp (f i x) ∂μ i := by
    simp_rw [Real.exp_sum]
    exact integral_fintype_prod_eq_prod (μ := μ) (fun i x => Real.exp (f i x))
  have hden (x : ι → A) : Real.exp (∑ i, f i (x i)) /
      (∫ x, Real.exp (∑ i, f i (x i)) ∂Measure.pi μ) =
        ∏ i, Real.exp (f i (x i)) / (∫ x, Real.exp (f i x) ∂μ i) := by
    rw [Real.exp_sum, hI, Finset.prod_div_distrib]
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilted_apply_eq_ofReal_integral _ _]
  simp_rw [hden]
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
    (μ := fun i => (μ i).restrict (s i))
    (fun i x => Real.exp (f i x) / (∫ x, Real.exp (f i x) ∂μ i))]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    ext i
    exact (tilted_apply_eq_ofReal_integral (μ := μ i) (f i) (s i)).symm
  · intro i _
    exact integral_nonneg fun x => div_nonneg (Real.exp_pos _).le (integral_exp_pos (he i)).le

end OverlapPaper
