-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSelectedReplicaIBP

@[expose] public section

/-! # Exact selected thermal variance as one- and two-replica kernels -/
namespace SlowEquilibration.GaussianReplicaCalculus
noncomputable section
open Set MeasureTheory ProbabilityTheory
open GaussianSpinComparison
open scoped Topology BigOperators
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- The true finite selected thermal variance is the diagonal kernel mean
minus the independent two-replica kernel mean. -/
theorem selected_variance_sum_eq_kernel_difference (ρ : Measure V) [IsProbabilityMeasure ρ]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Bool)
    (hφ : ∀ i, MemLp (coordinateObservable L i) 2 ρ) :
    (∑ i, if label i=true then Var[coordinateObservable L i;ρ] else 0)=
      (∫ u, selectedKernel L label u u ∂ρ)-
        ∫ u, ∫ v, selectedKernel L label u v ∂ρ ∂ρ := by
  let φ := coordinateObservable L
  have hi (i : ι) : Integrable (φ i) ρ := (hφ i).integrable (by norm_num)
  have hi₂ (i : ι) : Integrable (fun u => (φ i u)^2) ρ := by
    simpa only [Real.norm_eq_abs,sq_abs] using (hφ i).integrable_norm_pow' (p := 2)
  have hdiag : (∫ u,selectedKernel L label u u ∂ρ)=
      ∑ i,if label i=true then ∫ u,(φ i u)^2 ∂ρ else 0 := by
    unfold selectedKernel
    rw [integral_finsetSum Finset.univ (fun i _ => ?_)]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hh : label i=true
      · simp [hh,φ,coordinateObservable,pow_two]
      · simp [hh]
    · by_cases hh : label i=true
      · simpa [hh,φ,coordinateObservable,pow_two] using hi₂ i
      · simp only [hh,Bool.false_eq_true,ite_false]
        exact integrable_zero _ _ _
  have hinter (u : V) : (∫ v,selectedKernel L label u v ∂ρ)=
      ∑ i,if label i=true then φ i u*(∫ v,φ i v ∂ρ) else 0 := by
    unfold selectedKernel
    rw [integral_finsetSum Finset.univ (fun i _ => ?_)]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hh : label i=true
      · simp [hh,φ,coordinateObservable,integral_const_mul]
      · simp [hh]
    · by_cases hh : label i=true
      · simpa [hh,φ,coordinateObservable] using (hi i).const_mul (φ i u)
      · simp only [hh,Bool.false_eq_true,ite_false]
        exact integrable_zero _ _ _
  have hpair : (∫ u,∫ v,selectedKernel L label u v ∂ρ ∂ρ)=
      ∑ i,if label i=true then (∫ v,φ i v ∂ρ)^2 else 0 := by
    simp_rw [hinter]
    rw [integral_finsetSum Finset.univ (fun i _ => ?_)]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hh : label i=true
      · simp [hh,integral_mul_const,pow_two]
      · simp [hh]
    · by_cases hh : label i=true
      · simpa [hh] using (hi i).mul_const (∫ v,φ i v ∂ρ)
      · simp only [hh,Bool.false_eq_true,ite_false]
        exact integrable_zero _ _ _
  rw [hdiag,hpair,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hh : label i=true
  · simp only [hh,ite_true]
    simpa only [φ,Pi.pow_apply] using variance_eq_sub (hφ i)
  · simp [hh]

end
end SlowEquilibration.GaussianReplicaCalculus
