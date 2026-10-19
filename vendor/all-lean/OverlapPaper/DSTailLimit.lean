module

public import OverlapPaper.DSEmpiricalLaws
public import OverlapPaper.DSCoordinateSamplingKernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! The compact empirical limit retains an actual mean-square Hilbert Gram
approximation. Coordinate compactness alone would not imply this fact. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 700000

theorem prefixDifferencePairTest_norm_le (M N : ℕ) (p : DSCoordinateBall×DSCoordinateBall) :
    ‖prefixDifferencePairTest M N p‖≤4 := by
  have hM := abs_coordinateInnerPrefix_le_one M p.1 p.2
  have hN := abs_coordinateInnerPrefix_le_one N p.1 p.2
  rw [abs_le] at hM hN
  change ‖(coordinateInnerPrefix N p.1 p.2-coordinateInnerPrefix M p.1 p.2)^2‖≤4
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (2-(coordinateInnerPrefix N p.1 p.2-coordinateInnerPrefix M p.1 p.2)),
    sq_nonneg (2+(coordinateInnerPrefix N p.1 p.2-coordinateInnerPrefix M p.1 p.2))]

theorem integral_empirical_prefixDifference_bound (ν : ProbabilityMeasure GramArray) (n M N : ℕ) :
    ∫μ,pairCoordinateSamplingMean (prefixDifferencePairTest M N) μ
      ∂(gramEmpiricalDirectingLaw ν n : Measure DSDirectingSpace) ≤
      2/((M+1:ℕ):ℝ)+2/((N+1:ℕ):ℝ)+4/(n+1:ℝ) := by
  rw [gramEmpiricalDirectingLaw,ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_gramEmpiricalDirectingPoint n).aemeasurable
      (continuous_pairCoordinateSamplingMean _).measurable.aestronglyMeasurable]
  let B := 2/((M+1:ℕ):ℝ)+2/((N+1:ℕ):ℝ)+4/(n+1:ℝ)
  have hb (R : GramArray) : pairCoordinateSamplingMean (prefixDifferencePairTest M N)
      (gramEmpiricalDirectingPoint n R)≤B := by
    have hh := empirical_prefixDifferencePairTest_bound (n+1) (Nat.succ_pos n)
      (1/(n+1:ℝ)) (by positivity) R M N
    simpa only [gramEmpiricalDirectingPoint,B,div_eq_mul_inv,one_mul] using hh
  have hi : Integrable (fun R : GramArray => pairCoordinateSamplingMean
      (prefixDifferencePairTest M N) (gramEmpiricalDirectingPoint n R)) (ν : Measure GramArray) := by
    apply (integrable_const (4 : ℝ)).mono'
      (((continuous_pairCoordinateSamplingMean _).measurable.comp
        (measurable_gramEmpiricalDirectingPoint n)).aestronglyMeasurable)
    apply Eventually.of_forall
    intro R
    simpa only [Function.comp_apply,pairCoordinateSamplingMean,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ :=
        ((toCoordinateProbability (gramEmpiricalDirectingPoint n R)).prod
          (toCoordinateProbability (gramEmpiricalDirectingPoint n R)) : Measure _))
        (f := fun p => prefixDifferencePairTest M N p)
        (Eventually.of_forall (prefixDifferencePairTest_norm_le M N))
  have h := integral_mono hi (integrable_const B) hb
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,B] using h

theorem integral_limit_prefixDifference_bound (ν : ProbabilityMeasure GramArray)
    (ρ : ProbabilityMeasure DSDirectingSpace) (φ : ℕ→ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (gramEmpiricalDirectingLaw ν∘φ) atTop (𝓝 ρ)) (M N : ℕ) :
    ∫μ,pairCoordinateSamplingMean (prefixDifferencePairTest M N) μ ∂(ρ : Measure DSDirectingSpace) ≤
      2/((M+1:ℕ):ℝ)+2/((N+1:ℕ):ℝ) := by
  let g : C(DSDirectingSpace,ℝ) :=
    ⟨pairCoordinateSamplingMean (prefixDifferencePairTest M N),continuous_pairCoordinateSamplingMean _⟩
  have hl := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
    (BoundedContinuousFunction.mkOfCompact g)
  have hzero : Tendsto (fun n => (4:ℝ)/(φ n+1:ℝ)) atTop (𝓝 0) := by
    have hz : Tendsto (fun n : ℕ => (4:ℝ)/(n+1:ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,one_mul,mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
    exact hz.comp hφ.tendsto_atTop
  have hr : Tendsto (fun n => 2/((M+1:ℕ):ℝ)+2/((N+1:ℕ):ℝ)+4/(φ n+1:ℝ))
      atTop (𝓝 (2/((M+1:ℕ):ℝ)+2/((N+1:ℕ):ℝ))) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := 2/((M+1:ℕ):ℝ)+2/((N+1:ℕ):ℝ))).add hzero
  have hh := le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall (fun n => integral_empirical_prefixDifference_bound ν (φ n) M N))
  exact hh

def coordinatePairTailEnergy (ρ : ProbabilityMeasure DSDirectingSpace) (M : ℕ) : ℝ :=
  ∫p,(⟪coordinateVector p.2.1,coordinateVector p.2.2⟫-
    coordinateInnerPrefix M p.2.1 p.2.2)^2 ∂coordinatePairSamplingLaw ρ

theorem coordinatePairTailEnergy_nonneg (ρ : ProbabilityMeasure DSDirectingSpace) (M : ℕ) :
    0≤coordinatePairTailEnergy ρ M := integral_nonneg (fun _ => sq_nonneg _)

theorem coordinatePairTailEnergy_limit_bound (ν : ProbabilityMeasure GramArray)
    (ρ : ProbabilityMeasure DSDirectingSpace) (φ : ℕ→ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (gramEmpiricalDirectingLaw ν∘φ) atTop (𝓝 ρ)) (M : ℕ) :
    coordinatePairTailEnergy ρ M≤2/((M+1:ℕ):ℝ) := by
  have hd := tendsto_integral_of_dominated_convergence (μ := coordinatePairSamplingLaw ρ)
    (F := fun N p => prefixDifferencePairTest M N p.2)
    (f := fun p => (⟪coordinateVector p.2.1,coordinateVector p.2.2⟫-
      coordinateInnerPrefix M p.2.1 p.2.2)^2) (fun _ => (4:ℝ))
    (fun N => ((prefixDifferencePairTest M N).continuous.measurable.comp measurable_snd).aestronglyMeasurable)
    (integrable_const 4)
    (fun N => Eventually.of_forall (fun p => prefixDifferencePairTest_norm_le M N p.2))
    (Eventually.of_forall (fun p => ((tendsto_coordinateInnerPrefix p.2.1 p.2.2).sub_const _).pow 2))
  have hr : Tendsto (fun N : ℕ => 2/((M+1:ℕ):ℝ)+2/((N+1:ℕ):ℝ)) atTop
      (𝓝 (2/((M+1:ℕ):ℝ))) := by
    simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul,mul_zero,add_zero] using
      tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2)
  apply le_of_tendsto_of_tendsto hd hr
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [integral_coordinatePairSamplingLaw ρ _ (prefixDifferencePairTest M N).continuous.measurable
    4 (prefixDifferencePairTest_norm_le M N)]
  exact integral_limit_prefixDifference_bound ν ρ φ hφ hlim M N

theorem tendsto_coordinatePairTailEnergy_zero (ν : ProbabilityMeasure GramArray)
    (ρ : ProbabilityMeasure DSDirectingSpace) (φ : ℕ→ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (gramEmpiricalDirectingLaw ν∘φ) atTop (𝓝 ρ)) :
    Tendsto (coordinatePairTailEnergy ρ) atTop (𝓝 0) := by
  have hz : Tendsto (fun M : ℕ => 2/((M+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (coordinatePairTailEnergy_nonneg ρ)
    (coordinatePairTailEnergy_limit_bound ν ρ φ hφ hlim)

end OverlapPaper
