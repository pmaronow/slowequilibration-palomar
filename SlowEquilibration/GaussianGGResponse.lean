-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGEnergyFluctuation

@[expose] public section

/-! A quantitative tested selected-covariance replica response. Every
expectation is under the actual Gaussian field and its genuine IID Gibbs
replicas; the error is the proved thermal plus quenched deviation. -/
namespace SlowEquilibration.GaussianReplicaCalculus
noncomputable section
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
open GaussianSpinInterpolation GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationIntegrated GaussianPerturbationDeviation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem tested_selected_covariance_response_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v,‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) {n : ℕ} (k : Fin n)
    (f : (Fin n → V) → ℝ) (hf : Measurable f) (hfb : ∀ σ,|f σ| ≤ 1) :
    |x*(∫ w,
        replicaExpectation ν (parameterLinear L label x) n
          (fun σ => f σ*∑ j,selectedKernel L label (σ k) (σ j)) w-
        (n:ℝ)*replicaExpectation ν (parameterLinear L label x) (n+1)
          (fun σ => f (initialReplicas σ)*selectedKernel L label (σ k.castSucc) (σ (Fin.last n))) w
        ∂SYK.standardGaussianMeasureOnEuclidean ι)-
      meanScore ν L label x*(∫ w,replicaExpectation ν (parameterLinear L label x) n f w
        ∂SYK.standardGaussianMeasureOnEuclidean ι)| ≤
      meanThermalDeviation ν L label x+energyFluctuation ν L label x := by
  rw [← selected_probeEnergy_ibp ν L hL hK (by norm_num) hb label x k f hf hfb]
  exact selected_tested_energy_centered_le ν L hL hK hb label x k f hf hfb

end
end SlowEquilibration.GaussianReplicaCalculus
