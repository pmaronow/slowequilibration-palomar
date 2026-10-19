-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianThreeBlockMeanComparison

@[expose] public section

/-! # A finite domination budget for the actual three-block replica kernel

This bound is used only for parameter measurability and integrability.
Its dependence on the finite coordinate cardinality is explicit.
-/
namespace SlowEquilibration.GaussianThreeBlockComparison
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem norm_pairKernelExpectation_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ)
    (w : EuclideanSpace ℝ ι) :
    ‖pairKernelExpectation ν L label θ w‖ ≤ (Fintype.card ι : ℝ)*K^2 := by
  rw [pairKernelExpectation_eq_coordinate_sum ν L hL hK hb label θ w]
  calc
    _ ≤ ∑ i : ι,‖covarianceSign label i*
        (GaussianSpinInterpolation.expectation ν (coordinateObservable L i) (rotatedLinear L label θ) w)^2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : ι,K^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hs : ‖covarianceSign label i‖ ≤ 1 := by
        unfold covarianceSign
        split_ifs <;> norm_num
      have he := GaussianSpinInterpolation.norm_expectation_le ν (coordinateObservable L i)
        (rotatedLinear L label θ) (coordinateObservable_measurable L hL i)
        (rotatedLinear_measurable L hL label θ) hK
        ((coordinateObservable_bound ν L hb i).and (rotatedLinear_bound ν L hK hb label θ)) w
      rw [norm_mul,norm_pow]
      calc
        _ ≤ 1*K^2 := mul_le_mul hs ((sq_le_sq₀ (norm_nonneg _) hK).mpr he) (by positivity) (by norm_num)
        _ = _ := one_mul _
    _ = _ := by simp

theorem norm_meanPairKernel_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) :
    ‖meanPairKernel ν L label θ‖ ≤ (Fintype.card ι : ℝ)*K^2 := by
  have hh := norm_integral_le_of_norm_le_const (μ := SYK.standardGaussianMeasureOnEuclidean ι)
    (.of_forall (norm_pairKernelExpectation_le ν L hL hK hb label θ))
  simpa only [probReal_univ,mul_one,meanPairKernel] using hh

end
end SlowEquilibration.GaussianThreeBlockComparison
