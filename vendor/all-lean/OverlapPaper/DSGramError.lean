module

public import OverlapPaper.DSTailLimit

@[expose] public section

/-! Actual Gram truncation errors, their measurability and their empirical
mean-square bound before taking the compact limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace BigOperators
namespace OverlapPaper
set_option maxHeartbeats 600000

def coordinateGramError (M : ℕ) (p : DSCoordinateBall×DSCoordinateBall) : ℝ :=
  ⟪coordinateVector p.1,coordinateVector p.2⟫-coordinateInnerPrefix M p.1 p.2

theorem measurable_coordinateGramError (M : ℕ) : Measurable (coordinateGramError M) :=
  measurable_coordinateInner.sub (continuous_coordinateInnerPrefix M).measurable

theorem coordinateGramError_norm_le (M : ℕ) (p : DSCoordinateBall×DSCoordinateBall) :
    ‖coordinateGramError M p‖≤2 := by
  rw [Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by
    have h1 := abs_coordinateInner_le_one p.1 p.2
    have h2 := abs_coordinateInnerPrefix_le_one M p.1 p.2
    linarith)

theorem coordinateGramError_sq_norm_le (M : ℕ) (p : DSCoordinateBall×DSCoordinateBall) :
    ‖coordinateGramError M p ^2‖≤4 := by
  rw [norm_pow]
  nlinarith [coordinateGramError_norm_le M p,norm_nonneg (coordinateGramError M p)]

theorem measurable_pairGramError_mean (M : ℕ) :
    Measurable (fun μ : DSDirectingSpace => ∫p,coordinateGramError M p^2
      ∂((toCoordinateProbability μ).prod (toCoordinateProbability μ) : Measure _)) := by
  have hm : StronglyMeasurable (fun p : DSDirectingSpace×(DSCoordinateBall×DSCoordinateBall) =>
      coordinateGramError M p.2^2) :=
    (((measurable_coordinateGramError M).comp measurable_snd).pow_const 2).stronglyMeasurable
  have hh := hm.integral_kernel_prod_right' (κ := coordinatePairSamplingKernel)
  simpa only [coordinatePairSamplingKernel_apply] using hh.measurable

theorem pairGramError_mean_norm_le (M : ℕ) (μ : DSDirectingSpace) :
    ‖∫p,coordinateGramError M p^2
      ∂((toCoordinateProbability μ).prod (toCoordinateProbability μ) : Measure _)‖≤4 := by
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := ((toCoordinateProbability μ).prod (toCoordinateProbability μ) : Measure _))
      (f := fun p => coordinateGramError M p^2)
      (Eventually.of_forall (coordinateGramError_sq_norm_le M))

theorem empirical_pairGramError_mean_bound (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) (M : ℕ) :
    ∫p,coordinateGramError M p^2 ∂((finiteEmpiricalProbability hn (empiricalGramCoordinates n hn ε hε R)).prod
      (finiteEmpiricalProbability hn (empiricalGramCoordinates n hn ε hε R)) : Measure _)≤
      1/((M+1:ℕ):ℝ)+ε := by
  rw [integral_finiteEmpiricalProbability_prod hn _ _ ((measurable_coordinateGramError M).pow_const 2)]
  simp only [coordinateGramError,empiricalGramCoordinates_inner]
  exact empiricalGramCoordinates_inner_prefix_error n hn ε hε R M

theorem coordinatePairTailEnergy_empirical_bound (ν : ProbabilityMeasure GramArray) (n M : ℕ) :
    coordinatePairTailEnergy (gramEmpiricalDirectingLaw ν n) M≤
      1/((M+1:ℕ):ℝ)+1/(n+1:ℝ) := by
  change (∫p,coordinateGramError M p.2^2 ∂coordinatePairSamplingLaw (gramEmpiricalDirectingLaw ν n))≤_
  rw [integral_coordinatePairSamplingLaw (gramEmpiricalDirectingLaw ν n)
    (fun p => coordinateGramError M p^2) ((measurable_coordinateGramError M).pow_const 2)
    4 (coordinateGramError_sq_norm_le M)]
  rw [gramEmpiricalDirectingLaw,ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_gramEmpiricalDirectingPoint n).aemeasurable
      (measurable_pairGramError_mean M).aestronglyMeasurable]
  let B := 1/((M+1:ℕ):ℝ)+1/(n+1:ℝ)
  have hi : Integrable (fun R : GramArray =>
      ∫p,coordinateGramError M p^2
        ∂((toCoordinateProbability (gramEmpiricalDirectingPoint n R)).prod
          (toCoordinateProbability (gramEmpiricalDirectingPoint n R)) : Measure _))
      (ν : Measure GramArray) :=
    (integrable_const (4 : ℝ)).mono'
      ((measurable_pairGramError_mean M).comp (measurable_gramEmpiricalDirectingPoint n)).aestronglyMeasurable
      (Eventually.of_forall (fun R => pairGramError_mean_norm_le M (gramEmpiricalDirectingPoint n R)))
  have hb (R : GramArray) : (∫p,coordinateGramError M p^2
        ∂((toCoordinateProbability (gramEmpiricalDirectingPoint n R)).prod
          (toCoordinateProbability (gramEmpiricalDirectingPoint n R)) : Measure _))≤B :=
    empirical_pairGramError_mean_bound (n+1) (Nat.succ_pos n) _ (by positivity) R M
  have hh := integral_mono hi (integrable_const B) hb
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,B] using hh

end OverlapPaper
