-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeGibbs
public import SlowEquilibration.SphericalPlateauAmplitudeProbeKernel
public import SlowEquilibration.GaussianSelectedVarianceKernel

@[expose] public section

/-! # Exact actual physical one- and two-replica amplitude IBP identity -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter SphericalForm GaussianSpinComparison GaussianReplicaCalculus
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- The literal physical diagonal probe covariance minus its independent
weighted two-replica covariance. -/
def amplitudeProbeReplicaDifference (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (s : Fin 2 → ℝ) (D : BankDisorder n μ) : ℝ :=
  let ρ := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
  let K := selectedKernel (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) (amplitudeBankLabel μ p₀ k)
  (∫ u,K u u ∂ρ)-∫ u,∫ v,K u v ∂ρ ∂ρ

/-- The true finite physical thermal variances have exactly the literal
one- and two-replica physical probe kernel difference. -/
theorem amplitudeSelectedVariances_eq_replicaDifference (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    (∑ i : BankCoordinate n μ, if amplitudeBankLabel μ p₀ k i=true then
      Var[coordinateObservable (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) i;
        amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D] else 0)=
      amplitudeProbeReplicaDifference μ β J δ q₁ q₂ x e p₀ k s D := by
  let ρ := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
  let := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  have hs : ∀ᵐ u ∂ρ,‖u‖^2=((n+1:ℕ):ℝ) :=
    weightedLaw_support (by omega) β (amplitudePlantedField μ β x e p₀ s D)
      (sourceProfile J δ q₁ q₂) x
  have hφ (i : BankCoordinate n μ) :
      MemLp (coordinateObservable (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) i) 2 ρ := by
    apply memLp_sphereSupported_continuous ρ hs
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.comp
      (amplitudeBankLinear_continuous μ β x e p₀ (fun _ => 1))
  exact selected_variance_sum_eq_kernel_difference ρ
    (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) (amplitudeBankLabel μ p₀ k) hφ

/-- Source lem:pl-ibp is a genuine finite-volume identity for the exact
amplitude pressure: both replicas use the literal weighted physical law. -/
theorem amplitudePressureDerivative_eq_physical_replicas (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) :
    amplitudePressureDerivative μ β J δ q₁ q₂ x e p₀ k τ=
      ((1+τ)/(n+1:ℝ))*(∫ w : EuclideanBank n μ,
        amplitudeProbeReplicaDifference μ β J δ q₁ q₂ x e p₀ k (amplitudeAt k τ) (unpackBankCLM n μ w)
        ∂stdGaussian (EuclideanBank n μ)) := by
  rw [amplitudePressureDerivative_eq_physical_variances]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun w => amplitudeSelectedVariances_eq_replicaDifference μ β J δ q₁ q₂ x e p₀ k
    (amplitudeAt k τ) (unpackBankCLM n μ w)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
