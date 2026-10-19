-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeDerivative
public import SlowEquilibration.SphericalWeightedGibbsNormalization

@[expose] public section

/-! # Physical weighted-law form of the actual amplitude response -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter SphericalForm GaussianSpinInterpolation
  GaussianPerturbationParameter GaussianPerturbationResponse
open scoped Topology
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- The Gaussian response measure is exactly the true physical weighted law
of the literal planted bank field, at every source amplitude. -/
theorem amplitudeGaussianGibbs_eq (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) (w : EuclideanBank n μ) :
    gibbsMeasure (gibbsLaw (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x))
      (amplitudeBankLinear μ β x e p₀ (fun _ => 1))
        (parameterOperator (amplitudeBankLabel μ p₀ k) (1+τ) w)=
      amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ) (unpackBankCLM n μ w) := by
  rw [gaussianGibbs_gibbs_eq (by omega) (amplitudeBasePotential_continuous μ β J δ q₁ q₂ x)
    _ (fun w => (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      (amplitudeBankLinear_continuous μ β x e p₀ (fun _ => 1)))]
  unfold amplitudeWeightedLaw
  rw [weightedLaw_eq_gibbsLaw (by omega) β
    (amplitudePlantedField_contDiff μ β x e p₀ (amplitudeAt k τ) (unpackBankCLM n μ w)).continuous
      (sourceProfile_contDiff J δ q₁ q₂)]
  congr 1
  funext u
  rw [amplitudeBankLinear_parameter]
  unfold amplitudeBasePotential weightedPotential amplitudePlantedField
  simp only [Nat.cast_add,Nat.cast_one]
  ring

/-- The true normalized amplitude derivative is the actual selected-feature
thermal variance under the literal source weighted Gibbs law. -/
theorem amplitudePressureDerivative_eq_physical_variances (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) :
    amplitudePressureDerivative μ β J δ q₁ q₂ x e p₀ k τ=
      ((1+τ)/(n+1:ℝ))*(∫ w : EuclideanBank n μ,
        ∑ i : BankCoordinate n μ, if amplitudeBankLabel μ p₀ k i=true then
          Var[GaussianSpinComparison.coordinateObservable (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) i;
            amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ) (unpackBankCLM n μ w)] else 0
        ∂stdGaussian (EuclideanBank n μ)) := by
  rw [amplitudePressureDerivative_eq_varianceTrace]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun w => by
    unfold varianceTrace coordinateVariance
    change (∑ i : BankCoordinate n μ, if amplitudeBankLabel μ p₀ k i=true then
      Var[GaussianSpinComparison.coordinateObservable (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) i;
        gibbsMeasure (gibbsLaw (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x))
          (amplitudeBankLinear μ β x e p₀ (fun _ => 1))
            (parameterOperator (amplitudeBankLabel μ p₀ k) (1+τ) w)] else 0)=_
    rw [amplitudeGaussianGibbs_eq]

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
