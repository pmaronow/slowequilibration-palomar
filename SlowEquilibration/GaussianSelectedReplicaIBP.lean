-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaCovarianceIBP
public import SlowEquilibration.GaussianPerturbationResponse

@[expose] public section

/-! Tested replica response for a genuine selected Gaussian coordinate
block. The scalar parameter multiplies its actual cross Gram kernel. -/
namespace SlowEquilibration.GaussianReplicaCalculus
noncomputable section
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
open GaussianSpinInterpolation GaussianSpinComparison
  GaussianPerturbationParameter GaussianPerturbationSelfAveraging GaussianPerturbationResponse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

def selectedLinear (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Bool) :=
  fun v => (L v).comp (coordinateMask label true)

def selectedKernel (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Bool) (z y : V) : ℝ :=
  ∑ i,if label i=true then L z (EuclideanSpace.single i 1)*L y (EuclideanSpace.single i 1) else 0

omit [DecidableEq ι] in
theorem selectedLinear_measurable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Measurable L) (label : ι → Bool) : Measurable (selectedLinear L label) :=
  (show Continuous (fun l : EuclideanSpace ℝ ι →L[ℝ] ℝ => l.comp (coordinateMask label true))
    from continuous_id.clm_comp continuous_const).measurable.comp hL

omit [MeasurableSpace V] in
theorem selectedLinear_bound (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v,‖L v‖ ≤ K) (v : V) :
    ‖selectedLinear L label v‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro w
  exact ((L v).le_opNorm _).trans
    (mul_le_mul (hb v) (coordinateMask_norm_le label true w) (norm_nonneg _) hK)

omit [MeasurableSpace V] in
theorem parameterLinear_pointwise_bound (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v,‖L v‖ ≤ K) (x : ℝ) (v : V) :
    ‖parameterLinear L label x v‖ ≤ (1+|x|)*K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  exact ((L v).le_opNorm _).trans
    ((mul_le_mul (hb v) (parameterOperator_norm_le label x w) (norm_nonneg _) hK).trans_eq (by ring))

theorem selected_parameter_crossKernel (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) (z y : V) :
    crossKernel (selectedLinear L label) (parameterLinear L label x) z y=
      x*selectedKernel L label z y := by
  rw [crossKernel,selectedKernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : label i=true
  · simp only [selectedLinear,ContinuousLinearMap.comp_apply,
      coordinateMask_single,hi,ite_true,one_smul,
      parameterLinear_single_of_active L label x i hi,coordinateObservable]
    ring
  · simp [selectedLinear,ContinuousLinearMap.comp_apply,coordinateMask_single,hi]

/-- Exact selected Gaussian response with the original n replicas and
one genuinely fresh replica. No GG or positivity identity is assumed. -/
theorem selected_probeEnergy_ibp (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ v,‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) {n : ℕ} (k : Fin n)
    (f : (Fin n → V) → ℝ) (hf : Measurable f) (hfb : ∀ σ,|f σ| ≤ C) :
    (∫ w,probeEnergy ν (parameterLinear L label x) (selectedLinear L label) k f w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) =
    x*(∫ w,
      replicaExpectation ν (parameterLinear L label x) n
        (fun σ => f σ*∑ j,selectedKernel L label (σ k) (σ j)) w-
      (n:ℝ)*replicaExpectation ν (parameterLinear L label x) (n+1)
        (fun σ => f (initialReplicas σ)*selectedKernel L label (σ k.castSucc) (σ (Fin.last n))) w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  rw [probeEnergy_covariance_ibp ν (parameterLinear L label x) (selectedLinear L label)
    (parameterLinear_measurable L hL label x) (selectedLinear_measurable L hL label)
    (by positivity) hK hC (parameterLinear_pointwise_bound L label hK hb x)
    (selectedLinear_bound L label hK hb) k f hf hfb,← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun w => by
    simp_rw [selected_parameter_crossKernel]
    have ho : (fun σ : Fin n → V => f σ*∑ j,x*selectedKernel L label (σ k) (σ j))=
        fun σ => x*(f σ*∑ j,selectedKernel L label (σ k) (σ j)) := by
      funext σ
      rw [← Finset.mul_sum]
      ring
    have hfresh : (fun σ : Fin (n+1) → V => f (initialReplicas σ)*
        (x*selectedKernel L label (σ k.castSucc) (σ (Fin.last n))))=
        fun σ => x*(f (initialReplicas σ)*selectedKernel L label (σ k.castSucc) (σ (Fin.last n))) := by
      funext σ
      ring
    rw [ho,hfresh]
    unfold replicaExpectation
    rw [integral_const_mul,integral_const_mul]
    ring

end
end SlowEquilibration.GaussianReplicaCalculus
