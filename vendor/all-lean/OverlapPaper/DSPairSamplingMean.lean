module

public import OverlapPaper.DSFiniteSamplingMean
public import OverlapPaper.DSFinitePrefixTail
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Actual pair-sampling means and the continuous prefix-difference moments
used to pass empirical spectral tails through the compact directing limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal
namespace OverlapPaper
set_option maxHeartbeats 500000

def pairCoordinateSamplingMean (f : C(DSCoordinateBall×DSCoordinateBall,ℝ)) (ρ : DSDirectingSpace) : ℝ :=
  ∫p,f p ∂((toCoordinateProbability ρ).prod (toCoordinateProbability ρ) : Measure _)

theorem continuous_pairCoordinateSamplingMean (f : C(DSCoordinateBall×DSCoordinateBall,ℝ)) :
    Continuous (pairCoordinateSamplingMean f) :=
  (ProbabilityMeasure.continuous_integral_continuousMap f).comp
    (ProbabilityMeasure.continuous_prod.comp
      (continuous_toCoordinateProbability.prodMk continuous_toCoordinateProbability))

theorem integral_finiteEmpiricalProbability_prod {E : Type*} [MeasurableSpace E]
    {n : ℕ} (hn : 0<n) (v : Fin n→E) (f : E×E→ℝ) (hf : Measurable f) :
    ∫p,f p ∂((finiteEmpiricalProbability hn v).prod (finiteEmpiricalProbability hn v) : Measure (E×E))=
      (n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,f (v i,v j)) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  rw [finiteEmpiricalProbability,ProbabilityMeasure.map_prod_map _ _
    (measurable_of_countable v) (measurable_of_countable v),ProbabilityMeasure.toMeasure_map,
    integral_map (by fun_prop : Measurable (Prod.map v v)).aemeasurable hf.aestronglyMeasurable]
  change (∫p,f (v p.1,v p.2) ∂((PMF.uniformOfFintype (Fin n)).toMeasure.prod
    (PMF.uniformOfFintype (Fin n)).toMeasure))=_
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,smul_eq_mul]
  simp only [←Finset.mul_sum]
  ring

def prefixDifferencePairTest (M N : ℕ) : C(DSCoordinateBall×DSCoordinateBall,ℝ) :=
  ⟨fun p => (coordinateInnerPrefix N p.1 p.2-coordinateInnerPrefix M p.1 p.2)^2,
    ((continuous_coordinateInnerPrefix N).sub (continuous_coordinateInnerPrefix M)).pow 2⟩

theorem empirical_prefixDifferencePairTest_bound (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) (M N : ℕ) :
    pairCoordinateSamplingMean (prefixDifferencePairTest M N)
      (empiricalDirectingPoint hn (empiricalGramCoordinates n hn ε hε R)) ≤
      2/((M+1:ℕ):ℝ)+2/((N+1:ℕ):ℝ)+4*ε := by
  let v := empiricalGramCoordinates n hn ε hε R
  have hp (i j : Fin n) : (coordinateInnerPrefix N (v i) (v j)-coordinateInnerPrefix M (v i) (v j))^2≤
      2*(completeArray R.1 i.val j.val-coordinateInnerPrefix M (v i) (v j))^2+
      2*(completeArray R.1 i.val j.val-coordinateInnerPrefix N (v i) (v j))^2 := by
    nlinarith [sq_nonneg (2*completeArray R.1 i.val j.val-
      coordinateInnerPrefix M (v i) (v j)-coordinateInnerPrefix N (v i) (v j))]
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin n))) => hp i j))
  have hM := empiricalGramCoordinates_inner_prefix_error n hn ε hε R M
  have hN := empiricalGramCoordinates_inner_prefix_error n hn ε hε R N
  change (n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,
    (completeArray R.1 i.val j.val-coordinateInnerPrefix M (v i) (v j))^2)≤_ at hM
  change (n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,
    (completeArray R.1 i.val j.val-coordinateInnerPrefix N (v i) (v j))^2)≤_ at hN
  change (∫p,(prefixDifferencePairTest M N) p ∂
    ((finiteEmpiricalProbability hn v).prod (finiteEmpiricalProbability hn v) : Measure _))≤_
  rw [integral_finiteEmpiricalProbability_prod hn v _ (prefixDifferencePairTest M N).continuous.measurable]
  change (n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,
    (coordinateInnerPrefix N (v i) (v j)-coordinateInnerPrefix M (v i) (v j))^2)≤_
  calc
    _ ≤ (n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,
      (2*(completeArray R.1 i.val j.val-coordinateInnerPrefix M (v i) (v j))^2+
       2*(completeArray R.1 i.val j.val-coordinateInnerPrefix N (v i) (v j))^2)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = 2*((n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,
      (completeArray R.1 i.val j.val-coordinateInnerPrefix M (v i) (v j))^2))+
      2*((n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,
      (completeArray R.1 i.val j.val-coordinateInnerPrefix N (v i) (v j))^2)) := by
        simp only [Finset.sum_add_distrib,←Finset.mul_sum]
        ring
    _ ≤ _ := by
      simp only [div_eq_mul_inv,one_mul] at hM hN ⊢
      linarith only [hM,hN]

end OverlapPaper
