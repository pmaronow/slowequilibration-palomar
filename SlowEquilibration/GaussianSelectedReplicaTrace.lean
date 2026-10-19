-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianVarianceTraceContinuity

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianSelectedReplicaTrace

open MeasureTheory ProbabilityTheory
open GaussianSpinInterpolation GaussianSpinComparison
open GaussianPerturbationParameter GaussianPerturbationSelfAveraging
open GaussianPerturbationResponse
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

def selectedWeight (label : ι → Bool) (i : ι) : ℝ :=
  if label i=true then 1 else 0

def selectedKernel (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (v u : V) : ℝ :=
  ∑ i, selectedWeight label i *
    (coordinateObservable L i v*coordinateObservable L i u)

/-- The selected Gaussian-coordinate variance trace is exactly the
diagonal feature energy minus a genuine two-replica feature Gram moment,
under the actual parameter-dependent Gibbs law. -/
theorem varianceTrace_eq_selectedKernel
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (s : ℝ) (w : EuclideanSpace ℝ ι) :
    varianceTrace ν L label s w =
      (∫ v, selectedKernel L label v v
        ∂gibbsMeasure ν (parameterLinear L label s) w) -
      ∫ z : V × V, selectedKernel L label z.1 z.2
        ∂(gibbsMeasure ν (parameterLinear L label s) w).prod
          (gibbsMeasure ν (parameterLinear L label s) w) := by
  let G := gibbsMeasure ν (parameterLinear L label s) w
  have hLt := parameterLinear_measurable L hL label s
  have hbt := parameterLinear_bound ν L hK hb label s
  have : IsProbabilityMeasure G := gibbsMeasure_probability ν _ hLt hbt w
  have hac : G ≪ ν := gibbsMeasure_absolutelyContinuous ν _ w
  have hLp (i : ι) : MemLp (coordinateObservable L i) 2 G :=
    MemLp.of_bound (coordinateObservable_measurable L hL i).aestronglyMeasurable K
      (((coordinateObservable_bound ν L hb i).mono (fun v hv => by
        simpa only [Real.norm_eq_abs] using hv)).filter_mono hac.ae_le)
  have hvar (i : ι) : variance (coordinateObservable L i) G =
      (∫ v, (coordinateObservable L i v)^2 ∂G) -
        (∫ v, coordinateObservable L i v ∂G)^2 := by
    rw [← covariance_self (hLp i).aemeasurable, covariance_eq_sub (hLp i) (hLp i)]
    simp only [Pi.mul_apply, pow_two]
  change (∑ i, (if label i=true then variance (coordinateObservable L i) G else 0)) =
      (∫ v, selectedKernel L label v v ∂G) -
        ∫ z : V × V, selectedKernel L label z.1 z.2 ∂G.prod G
  have hweight (i : ι) :
      (if label i=true then variance (coordinateObservable L i) G else 0) =
        selectedWeight label i * variance (coordinateObservable L i) G := by
    by_cases hi : label i=true <;> simp [selectedWeight,hi]
  simp_rw [hweight,hvar,mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold selectedKernel
    simp only [← pow_two]
    rw [integral_finsetSum Finset.univ (fun i _ => (hLp i).integrable_sq.const_mul _)]
    simp only [integral_const_mul]
  · unfold selectedKernel
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (((hLp i).integrable (by norm_num)).mul_prod
        ((hLp i).integrable (by norm_num))).const_mul _)]
    simp only [integral_const_mul, integral_prod_mul, pow_two]

end SlowEquilibration.GaussianSelectedReplicaTrace
