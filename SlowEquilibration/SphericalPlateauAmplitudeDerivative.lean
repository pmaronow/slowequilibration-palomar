-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeFeature
public import SlowEquilibration.SphericalPlateauAmplitudeExpected
public import SlowEquilibration.SphericalGibbsTilt
public import SlowEquilibration.GaussianPerturbationResponse

@[expose] public section

/-! # Actual quenched source amplitude derivatives

The derivative of the physical expected log partition is the exact selected
Gaussian response of its genuine tensor bank. The deterministic planted drift
and source penalty stay inside their literal physical Gibbs base measure.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter SphericalForm GaussianSpinInterpolation
  GaussianPerturbationParameter GaussianPerturbationResponse GaussianPerturbationSelfAveraging
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- The actual deterministic physical planted drift and source penalty. -/
def amplitudeBasePotential (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (u : Vector (n+1)) : ℝ :=
  β^2*(n+1:ℝ)*μ.xi (overlap x u)-2*(n+1:ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)

theorem amplitudeBasePotential_continuous (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) : Continuous (amplitudeBasePotential μ β J δ q₁ q₂ x) := by
  have hxi : Continuous μ.xi := continuous_iff_continuousAt.mpr fun r => (μ.hasDerivAt_xi r).continuousAt
  have hR : Continuous (fun u : Vector (n+1) => overlap x u) := by unfold overlap; fun_prop
  exact (continuous_const.mul (hxi.comp hR)).sub
    (continuous_const.mul ((sourceProfile_contDiff J δ q₁ q₂).continuous.comp hR))

/-- Literal physical derivative of the expected amplitude pressure. -/
def amplitudePressureDerivative (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) : ℝ :=
  meanScore (gibbsLaw (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x))
    (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) (amplitudeBankLabel μ p₀ k) (1+τ)/(n+1:ℝ)

/-- The true generic Gaussian parameter logarithm is exactly the physical
source amplitude logarithm minus its literal deterministic normalization. -/
theorem amplitudeParameterLog_eq (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) (w : EuclideanBank n μ) :
    parameterLogPartition (gibbsLaw (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x))
      (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) (amplitudeBankLabel μ p₀ k) w (1+τ)=
    Real.log (amplitudePartition μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ) (unpackBankCLM n μ w))-
      Real.log (partition (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x)) := by
  unfold parameterLogPartition
  rw [logPartition_gibbs_eq_ratio (by omega) (amplitudeBasePotential_continuous μ β J δ q₁ q₂ x)
    _ (fun w => (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      (amplitudeBankLinear_continuous μ β x e p₀ (fun _ => 1)))]
  congr 2
  unfold partition amplitudePartition
  apply integral_congr_ae
  exact .of_forall fun u => by
    dsimp only
    rw [amplitudeBankLinear_parameter,one_mul]
    congr 1
    unfold amplitudeBasePotential amplitudePlantedField
    ring

/-- Actual normalized expectation equality with the proved Gaussian parameter
mean; the whole physical drift and source penalty remain unchanged. -/
theorem amplitudeExpectedPressure_eq_parameterMean (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) :
    amplitudeExpectedPressure μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ)=
      (parameterMean (gibbsLaw (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x))
        (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) (amplitudeBankLabel μ p₀ k) (1+τ)+
        Real.log (partition (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x)))/(n+1:ℝ) := by
  let A := amplitudeBasePotential μ β J δ q₁ q₂ x
  let L := amplitudeBankLinear μ β x e p₀ (fun _ => 1)
  let ν := gibbsLaw (n+1) 1 A
  let label : BankCoordinate n μ → Bool := amplitudeBankLabel μ p₀ k
  have hA : Continuous A := amplitudeBasePotential_continuous μ β J δ q₁ q₂ x
  let := gibbsLaw_probability (by omega : 1≤n+1) 1 hA
  obtain ⟨K,hK,hB⟩ := exists_amplitudeBankLinear_sphere_bound μ β x e p₀ (fun _ => 1)
  have hb : ∀ᵐ u ∂ν, ‖L u‖≤K := by
    filter_upwards [gibbsLaw_support (by omega : 1≤n+1) 1 A] with u hu
    exact hB u (by simpa only [Nat.cast_add,Nat.cast_one] using hu)
  have hi := parameterLogPartition_gaussian_integrable ν L
    (amplitudeBankLinear_continuous μ β x e p₀ (fun _ => 1)).measurable hK hb label (1+τ)
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at hi
  have hmap := (actual_bank_flattened_gaussian n μ).integral_comp hi.aestronglyMeasurable
  have hcomp := (actual_bank_flattened_gaussian n μ).integrable_comp hi
  simp only [Function.comp_apply] at hmap
  change Integrable (fun D : BankDisorder n μ => parameterLogPartition ν L label (euclideanBank D) (1+τ)) (bankLaw n μ) at hcomp
  let C := Real.log (partition (n+1) 1 A)
  have he : (fun D : BankDisorder n μ => Real.log
      (amplitudePartition μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ) D))=
      fun D => parameterLogPartition ν L label (euclideanBank D) (1+τ)+C := by
    funext D
    have hh := amplitudeParameterLog_eq μ β J δ q₁ q₂ x e p₀ k τ (euclideanBank D)
    rw [unpackBank_euclideanBank] at hh
    dsimp only [A,L,ν,label,C]
    linarith
  have hAdd := integral_add hcomp (integrable_const C)
  simp only [integral_const,probReal_univ,one_smul] at hAdd
  unfold amplitudeExpectedPressure
  rw [he,hAdd,hmap]
  simp only [parameterMean,SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian]
  rfl

/-- Genuine differentiation of the exact physical expected pressure at
every real source amplitude; all Gaussian envelopes are proved internally. -/
theorem amplitudeExpectedPressure_hasDerivAt (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) : HasDerivAt (fun t =>
      amplitudeExpectedPressure μ β J δ q₁ q₂ x e p₀ (amplitudeAt k t))
        (amplitudePressureDerivative μ β J δ q₁ q₂ x e p₀ k τ) τ := by
  let A := amplitudeBasePotential μ β J δ q₁ q₂ x
  let L := amplitudeBankLinear μ β x e p₀ (fun _ => 1)
  let ν := gibbsLaw (n+1) 1 A
  have hA : Continuous A := amplitudeBasePotential_continuous μ β J δ q₁ q₂ x
  let := gibbsLaw_probability (by omega : 1≤n+1) 1 hA
  obtain ⟨K,hK,hB⟩ := exists_amplitudeBankLinear_sphere_bound μ β x e p₀ (fun _ => 1)
  have hb : ∀ᵐ u ∂ν, ‖L u‖≤K := by
    filter_upwards [gibbsLaw_support (by omega : 1≤n+1) 1 A] with u hu
    exact hB u (by simpa only [Nat.cast_add,Nat.cast_one] using hu)
  have hd := parameterMean_hasDerivAt ν L
    (amplitudeBankLinear_continuous μ β x e p₀ (fun _ => 1)).measurable hK hb (amplitudeBankLabel μ p₀ k) (1+τ)
  have hline := hd.comp τ ((hasDerivAt_id τ).const_add 1)
  simp only [mul_one] at hline
  have hh := (hline.add_const (Real.log (partition (n+1) 1 A))).div_const (n+1:ℝ)
  convert hh using 1
  · funext t
    exact amplitudeExpectedPressure_eq_parameterMean μ β J δ q₁ q₂ x e p₀ k t
  · rfl

/-- Exact Gaussian integration-by-parts response formula for the true
normalized source derivative. This is an identity, not an asymptotic premise. -/
theorem amplitudePressureDerivative_eq_varianceTrace (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) :
    amplitudePressureDerivative μ β J δ q₁ q₂ x e p₀ k τ=
      ((1+τ)/(n+1:ℝ))*(∫ w, varianceTrace
        (gibbsLaw (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x))
        (amplitudeBankLinear μ β x e p₀ (fun _ => 1)) (amplitudeBankLabel μ p₀ k) (1+τ) w
          ∂stdGaussian (EuclideanBank n μ)) := by
  let A := amplitudeBasePotential μ β J δ q₁ q₂ x
  let L := amplitudeBankLinear μ β x e p₀ (fun _ => 1)
  let ν := gibbsLaw (n+1) 1 A
  have hA : Continuous A := amplitudeBasePotential_continuous μ β J δ q₁ q₂ x
  let := gibbsLaw_probability (by omega : 1≤n+1) 1 hA
  obtain ⟨K,hK,hB⟩ := exists_amplitudeBankLinear_sphere_bound μ β x e p₀ (fun _ => 1)
  have hb : ∀ᵐ u ∂ν, ‖L u‖≤K := by
    filter_upwards [gibbsLaw_support (by omega : 1≤n+1) 1 A] with u hu
    exact hB u (by simpa only [Nat.cast_add,Nat.cast_one] using hu)
  have hh := meanScore_response ν L
    (amplitudeBankLinear_continuous μ β x e p₀ (fun _ => 1)).measurable hK hb (amplitudeBankLabel μ p₀ k) (1+τ)
  simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at hh
  dsimp only [A,L,ν] at hh
  unfold amplitudePressureDerivative
  rw [hh]
  ring

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
