-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeGibbs
public import SlowEquilibration.GaussianSpinKernels
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! # Literal Borel Markov kernel of the actual amplitude-weighted law -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter SphericalForm GaussianSpinInterpolation
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- The actual physical amplitude replica law is a Borel kernel of the
literal independent ordered Gaussian bank coordinates. -/
def amplitudeWeightedKernel (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) : Kernel (BankDisorder n μ) (Vector (n+1)) := by
  let _ := gibbsLaw_probability (by omega : 1≤n+1) 1
    (amplitudeBasePotential_continuous μ β J δ q₁ q₂ x)
  exact (gibbsKernel (gibbsLaw (n+1) 1 (amplitudeBasePotential μ β J δ q₁ q₂ x))
    (amplitudeBankLinear μ β x e p₀ s)).comap euclideanBank (euclideanBank_measurable n μ)

theorem amplitudeWeightedKernel_apply (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    amplitudeWeightedKernel μ β J δ q₁ q₂ x e p₀ s D=
      amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D := by
  let A := amplitudeBasePotential μ β J δ q₁ q₂ x
  have hA : Continuous A := amplitudeBasePotential_continuous μ β J δ q₁ q₂ x
  let _ := gibbsLaw_probability (by omega : 1≤n+1) 1 hA
  obtain ⟨K,hK,hB⟩ := exists_amplitudeBankLinear_sphere_bound μ β x e p₀ s
  have hb : ∀ᵐ u ∂gibbsLaw (n+1) 1 A,‖amplitudeBankLinear μ β x e p₀ s u‖≤K := by
    filter_upwards [gibbsLaw_support (by omega : 1≤n+1) 1 A] with u hu
    exact hB u (by simpa only [Nat.cast_add,Nat.cast_one] using hu)
  rw [amplitudeWeightedKernel,Kernel.comap_apply,gibbsKernel_apply _ _
    (amplitudeBankLinear_continuous μ β x e p₀ s).measurable hK hb]
  rw [gaussianGibbs_gibbs_eq (by omega : 1≤n+1) hA _
    (fun w => (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      (amplitudeBankLinear_continuous μ β x e p₀ s))]
  unfold amplitudeWeightedLaw
  rw [weightedLaw_eq_gibbsLaw (by omega : 1≤n+1) β
    (amplitudePlantedField_contDiff μ β x e p₀ s D).continuous
    (sourceProfile_contDiff J δ q₁ q₂)]
  congr 1
  funext u
  rw [amplitudeBankLinear_apply,unpackBank_euclideanBank]
  unfold A amplitudeBasePotential weightedPotential amplitudePlantedField
  simp only [Nat.cast_add,Nat.cast_one]
  ring

instance amplitudeWeightedKernel_markov (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    IsMarkovKernel (amplitudeWeightedKernel μ β J δ q₁ q₂ x e p₀ s) := by
  constructor
  intro D
  rw [amplitudeWeightedKernel_apply]
  exact amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D

/-- Every actual weighted two-replica Borel observable has Borel bank
expectation, for arbitrary amplitudes. -/
theorem amplitudePairIntegral_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ : Vector (n+1) × Vector (n+1) → ℝ) (hφ : Measurable φ) :
    Measurable (fun D : BankDisorder n μ => ∫ z,φ z
      ∂(amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D).prod
        (amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D)) := by
  let κ := amplitudeWeightedKernel μ β J δ q₁ q₂ x e p₀ s
  have h := (hφ.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ.prod κ)
  simpa only [Kernel.prod_apply,κ,amplitudeWeightedKernel_apply,Function.comp_apply] using h.measurable

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
