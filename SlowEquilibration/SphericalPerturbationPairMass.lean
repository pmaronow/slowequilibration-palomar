-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalUniformPositivity

/-! The literal two-replica Gibbs integral behind the true averaged
perturbation overlap law, including singular underlying spin measures. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianGGEnsemble GaussianSpinInterpolation
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The overlap kernel uses the actual independently sampled Gibbs
replicas, on the original unit-spin space. -/
theorem perturbation_overlapKernel_mass {N K : ℕ} (ν : Measure (UnitSpin N))
    [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v)
    (x : Fin K → ℝ) (w : PerturbationDisorder N K)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (overlapKernel ((ambientParameterizedGibbsKernel ν v).sectR x) w).real A=
      ((gibbsMeasure ν (unitLinear (coefficients v x)) w).prod
        (gibbsMeasure ν (unitLinear (coefficients v x)) w)).real
        {z : UnitSpin N × UnitSpin N | inner ℝ z.1.val z.2.val∈A} := by
  let _ := ambientParameterizedGibbsKernel_markov (K := K) ν hv
  let _ := parameterizedGibbsKernel_markov (K := K) ν hv
  let _ : IsProbabilityMeasure (gibbsMeasure ν (unitLinear (coefficients v x)) w) := by
    rw [← parameterizedGibbsKernel_apply ν hv x w]
    infer_instance
  have hs : Measurable (Prod.map (Subtype.val : UnitSpin N → Vector N) (Subtype.val : UnitSpin N → Vector N)) :=
    measurable_subtype_coe.prodMap measurable_subtype_coe
  have hi : Measurable (fun z : Vector N × Vector N => inner ℝ z.1 z.2) :=
    overlap_map_measurable
  rw [overlapKernel,Kernel.map_apply _ hi,Kernel.prod_apply,Kernel.sectR_apply,
    ambientParameterizedGibbsKernel,Kernel.map_apply _ measurable_subtype_coe,
    parameterizedGibbsKernel_apply ν hv,
    Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,
    Measure.map_map hi hs,map_measureReal_apply (hi.comp hs) hA]
  rfl

/-- Exact Gaussian and coefficient averaging of the ordinary product
Gibbs measure. No replacement by a finite-spin model occurs. -/
theorem perturbedOverlapLaw_mass_eq_gibbs_pair_integral {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (perturbedOverlapLaw (K := K) ν v).real A=
      ∫x,∫w,((gibbsMeasure ν (unitLinear (coefficients v x)) w).prod
        (gibbsMeasure ν (unitLinear (coefficients v x)) w)).real
        {z : UnitSpin N × UnitSpin N | inner ℝ z.1.val z.2.val∈A}
        ∂(SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ∂positiveCubeLaw K := by
  let _ := ambientParameterizedGibbsKernel_markov (K := K) ν hv
  rw [perturbedOverlapLaw,kernel_real_mean _ _ A hA]
  apply integral_congr_ae
  exact .of_forall fun x => by
    change ((overlapFamily (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      (ambientParameterizedGibbsKernel ν v)) x).real A=_
    rw [overlapFamily_apply,overlapLaw,kernel_real_mean _ _ A hA]
    apply integral_congr_ae
    exact .of_forall fun w => perturbation_overlapKernel_mass ν hv x w A hA

/-- The fully literal two-Gibbs-replica form of uniform positivity.
The finite tensor degree cutoff and perturbation strength are fixed
before all dimensions and arbitrary underlying spin probability laws. -/
theorem exists_uniform_gibbs_pair_positivity {ε η : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ K : ℕ, ∃ V : ℝ, 0<K ∧ 1≤V ∧
      ∀ {N : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
        (v : ℝ), V≤v →
        (∫x,∫w,((gibbsMeasure ν (unitLinear (coefficients v x)) w).prod
          (gibbsMeasure ν (unitLinear (coefficients v x)) w)).real
          {z : UnitSpin N × UnitSpin N | inner ℝ z.1.val z.2.val≤-ε}
          ∂(SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ∂positiveCubeLaw K)≤η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_perturbation_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N ν _ v hv
  have hvnon : 0≤v := le_trans (by norm_num : (0:ℝ)≤1) (hV.trans hv)
  have heq := perturbedOverlapLaw_mass_eq_gibbs_pair_integral (K := K) ν hvnon (Iic (-ε)) measurableSet_Iic
  exact heq.symm.trans_le (hPos ν v hv)

end SlowEquilibration.SphericalPositivePerturbation
