-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudePairError
public import SlowEquilibration.SphericalPlateauAmplitudeProbeLocalization
public import SlowEquilibration.SphericalPlateauAmplitudeProbeTargets

@[expose] public section

/-! # Actual bank-integrated physical polynomial localization

All integrals below use the literal amplitude weighted law and the independent
Gaussian bank law. Measurability and integrability follow from the actual Borel
Markov kernel and compact physical sphere support, without additional inputs.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open SphericalModel SphericalBarycenter SphericalForm SphericalWeightedReplicaGeometry
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def amplitudeSingleAverage (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (φ : Vector (n+1) → ℝ)
    (D : BankDisorder n μ) : ℝ :=
  ∫ u,φ u ∂amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D

def amplitudePairAverage (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ : Vector (n+1) × Vector (n+1) → ℝ) (D : BankDisorder n μ) : ℝ :=
  ∫ z,φ z ∂(amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D).prod
    (amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D)

theorem amplitudeSingleAverage_measurable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ : Vector (n+1) → ℝ) (hφ : Measurable φ) :
    Measurable (amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s φ) := by
  have h := (hφ.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
    (κ := amplitudeWeightedKernel μ β J δ q₁ q₂ x e p₀ s)
  change Measurable (fun D : BankDisorder n μ => ∫ u,φ u ∂amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D)
  simpa only [amplitudeWeightedKernel_apply,Function.comp_apply] using h.measurable

theorem amplitudeSingleObservable_integrable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ : Vector (n+1) → ℝ) (hφ : Continuous φ) (D : BankDisorder n μ) :
    Integrable φ (amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D) := by
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  exact integrable_sphereSupported_continuous (amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D)
    (weightedLaw_support (by omega : 1≤n+1) β (amplitudePlantedField μ β x e p₀ s D)
      (sourceProfile J δ q₁ q₂) x) hφ

theorem amplitudePairObservable_integrable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ : Vector (n+1) × Vector (n+1) → ℝ) (hφ : Continuous φ) (D : BankDisorder n μ) :
    Integrable φ ((amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D).prod
      (amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D)) := by
  let W := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector (n+1)) (Real.sqrt (n+1:ℝ))).prod
    (isCompact_closedBall (0 : Vector (n+1)) (Real.sqrt (n+1:ℝ)))).exists_bound_of_continuousOn hφ.continuousOn
  apply Integrable.of_bound hφ.aestronglyMeasurable C
  filter_upwards [sphereSupported_prod W (weightedLaw_support (by omega : 1≤n+1) β
    (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x)] with z hz
  apply hC z
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [show (n+1:ℝ)=‖z.1‖^2 by simpa only [Nat.cast_add,Nat.cast_one] using hz.1.symm,
      Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [show (n+1:ℝ)=‖z.2‖^2 by simpa only [Nat.cast_add,Nat.cast_one] using hz.2.symm,
      Real.sqrt_sq (norm_nonneg z.2)]

theorem amplitudeSingleAverage_integrable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ : Vector (n+1) → ℝ) (hφ : Continuous φ) :
    Integrable (amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s φ) (bankLaw n μ) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector (n+1))
    (Real.sqrt (n+1:ℝ))).exists_bound_of_continuousOn hφ.continuousOn
  apply Integrable.of_bound (amplitudeSingleAverage_measurable μ β J δ q₁ q₂ x e p₀ s φ hφ.measurable).aestronglyMeasurable C
  apply ae_of_all
  intro D
  let W := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  apply (norm_integral_le_integral_norm _).trans
  have hi := amplitudeSingleObservable_integrable μ β J δ q₁ q₂ x e p₀ s φ hφ D
  have hh := integral_mono_ae hi.norm (integrable_const C) (by
    filter_upwards [weightedLaw_support (by omega : 1≤n+1) β
      (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x] with u hu
    apply hC u
    simp only [mem_closedBall,dist_zero_right]
    rw [show (n+1:ℝ)=‖u‖^2 by simpa only [Nat.cast_add,Nat.cast_one] using hu.symm,
      Real.sqrt_sq (norm_nonneg u)])
  simpa only [integral_const,probReal_univ,one_smul] using hh

theorem amplitudePairAverage_integrable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ : Vector (n+1) × Vector (n+1) → ℝ) (hφ : Continuous φ) :
    Integrable (amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s φ) (bankLaw n μ) := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector (n+1)) (Real.sqrt (n+1:ℝ))).prod
    (isCompact_closedBall (0 : Vector (n+1)) (Real.sqrt (n+1:ℝ)))).exists_bound_of_continuousOn hφ.continuousOn
  apply Integrable.of_bound (amplitudePairIntegral_measurable μ β J δ q₁ q₂ x e p₀ s φ hφ.measurable).aestronglyMeasurable C
  apply ae_of_all
  intro D
  let W := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  apply (norm_integral_le_integral_norm _).trans
  have hi := amplitudePairObservable_integrable μ β J δ q₁ q₂ x e p₀ s φ hφ D
  have hh := integral_mono_ae hi.norm (integrable_const C) (by
    filter_upwards [sphereSupported_prod W (weightedLaw_support (by omega : 1≤n+1) β
      (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x)] with z hz
    apply hC z
    constructor
    · simp only [mem_closedBall,dist_zero_right]
      rw [show (n+1:ℝ)=‖z.1‖^2 by simpa only [Nat.cast_add,Nat.cast_one] using hz.1.symm,
        Real.sqrt_sq (norm_nonneg z.1)]
    · simp only [mem_closedBall,dist_zero_right]
      rw [show (n+1:ℝ)=‖z.2‖^2 by simpa only [Nat.cast_add,Nat.cast_one] using hz.2.symm,
        Real.sqrt_sq (norm_nonneg z.2)])
  simpa only [integral_const,probReal_univ,one_smul] using hh

/-- Actual bank expectation of the physical one-replica latitude error. -/
def amplitudeLatitudeL1 (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) : ℝ :=
  ∫ D,amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s
    (fun u => |overlap x u-q|) D ∂bankLaw n μ

def amplitudeDiagonalProbeMean (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (s : Fin 2 → ℝ) : ℝ :=
  ∫ D,amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s
    (fun u => amplitudeSelectedCoefficient μ p₀ k (overlap x u)) D ∂bankLaw n μ

def amplitudePhysicalProbeMean (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (s : Fin 2 → ℝ) : ℝ :=
  ∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s
    (fun z => amplitudePhysicalProbePolynomial μ p₀ k (overlap x z.1)
      (overlap x z.2) (overlap z.1 z.2)) D ∂bankLaw n μ

def amplitudeCenteredProbeMean (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (s : Fin 2 → ℝ) : ℝ :=
  ∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s
    (fun z => amplitudePhysicalProbePolynomial μ p₀ k q q (overlap z.1 z.2)) D ∂bankLaw n μ

private theorem single_average_error_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ ψ : Vector (n+1) → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hbound : ∀ u,‖u‖^2=((n+1:ℕ):ℝ) → |φ u|≤ψ u) (D : BankDisorder n μ) :
    |amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s φ D|≤
      amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s ψ D := by
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  rw [← Real.norm_eq_abs]
  unfold amplitudeSingleAverage
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (amplitudeSingleObservable_integrable μ β J δ q₁ q₂ x e p₀ s φ hφ D).norm
    (amplitudeSingleObservable_integrable μ β J δ q₁ q₂ x e p₀ s ψ hψ D)
  filter_upwards [weightedLaw_support (by omega : 1≤n+1) β
    (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x] with u hu
  simpa only [Real.norm_eq_abs] using hbound u hu

private theorem pair_average_error_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ ψ : Vector (n+1) × Vector (n+1) → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hbound : ∀ u v,‖u‖^2=((n+1:ℕ):ℝ) → ‖v‖^2=((n+1:ℕ):ℝ) → |φ (u,v)|≤ψ (u,v))
    (D : BankDisorder n μ) :
    |amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s φ D|≤
      amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s ψ D := by
  let W := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  rw [← Real.norm_eq_abs]
  unfold amplitudePairAverage
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (amplitudePairObservable_integrable μ β J δ q₁ q₂ x e p₀ s φ hφ D).norm
    (amplitudePairObservable_integrable μ β J δ q₁ q₂ x e p₀ s ψ hψ D)
  filter_upwards [sphereSupported_prod W (weightedLaw_support (by omega : 1≤n+1) β
    (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x)] with z hz
  simpa only [Real.norm_eq_abs] using hbound z.1 z.2 hz.1 hz.2

theorem amplitudeExpectedSingle_error_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ ψ : Vector (n+1) → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hbound : ∀ u,‖u‖^2=((n+1:ℕ):ℝ) → |φ u|≤ψ u) :
    |∫ D,amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s φ D ∂bankLaw n μ|≤
      ∫ D,amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s ψ D ∂bankLaw n μ := by
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (amplitudeSingleAverage_integrable μ β J δ q₁ q₂ x e p₀ s φ hφ).norm
    (amplitudeSingleAverage_integrable μ β J δ q₁ q₂ x e p₀ s ψ hψ)
  intro D
  simpa only [Real.norm_eq_abs] using single_average_error_le μ β J δ q₁ q₂ x e p₀ s φ ψ hφ hψ hbound D

theorem amplitudeExpectedPair_error_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (φ ψ : Vector (n+1) × Vector (n+1) → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hbound : ∀ u v,‖u‖^2=((n+1:ℕ):ℝ) → ‖v‖^2=((n+1:ℕ):ℝ) → |φ (u,v)|≤ψ (u,v)) :
    |∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s φ D ∂bankLaw n μ|≤
      ∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s ψ D ∂bankLaw n μ := by
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (amplitudePairAverage_integrable μ β J δ q₁ q₂ x e p₀ s φ hφ).norm
    (amplitudePairAverage_integrable μ β J δ q₁ q₂ x e p₀ s ψ hψ)
  intro D
  simpa only [Real.norm_eq_abs] using pair_average_error_le μ β J δ q₁ q₂ x e p₀ s φ ψ hφ hψ hbound D

theorem amplitudeDiagonalProbeMean_center_error_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (s : Fin 2 → ℝ) {q : ℝ} (hq : |q|≤1) :
    |amplitudeDiagonalProbeMean μ β J δ q₁ q₂ x e p₀ k s-amplitudeSelectedCoefficient μ p₀ k q|≤
      (2*amplitudeProbeLocalizationConstant μ p₀ k)*amplitudeLatitudeL1 μ β J δ q₁ q₂ q x e p₀ s := by
  let f := fun u : Vector (n+1) => amplitudeSelectedCoefficient μ p₀ k (overlap x u)
  let g := fun u : Vector (n+1) => |overlap x u-q|
  let c := amplitudeSelectedCoefficient μ p₀ k q
  let C := 2*amplitudeProbeLocalizationConstant μ p₀ k
  have hf : Continuous f := by unfold f amplitudeSelectedCoefficient overlap;fun_prop
  have hg : Continuous g := by unfold g overlap;fun_prop
  have he (D : BankDisorder n μ) :
      amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s (fun u => f u-c) D=
        amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s f D-c := by
    let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
    unfold amplitudeSingleAverage
    rw [integral_sub (amplitudeSingleObservable_integrable μ β J δ q₁ q₂ x e p₀ s f hf D) (integrable_const c)]
    simp only [integral_const,probReal_univ,one_smul]
  have he' : amplitudeDiagonalProbeMean μ β J δ q₁ q₂ x e p₀ k s-c=
      ∫ D,amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s (fun u => f u-c) D ∂bankLaw n μ := by
    simp_rw [he]
    rw [integral_sub (amplitudeSingleAverage_integrable μ β J δ q₁ q₂ x e p₀ s f hf) (integrable_const c)]
    simp only [integral_const,probReal_univ,one_smul]
    rfl
  have hb := amplitudeExpectedSingle_error_le μ β J δ q₁ q₂ x e p₀ s
    (fun u => f u-c) (fun u => C*g u) (hf.sub continuous_const) (continuous_const.mul hg) (by
      intro u hu
      exact amplitudeSelectedCoefficient_center_error_le μ p₀ k
        (abs_le.mpr (overlap_mem_Icc_of_norm_sq (by omega : 1≤n+1) x u hx hu)) hq)
  change |amplitudeDiagonalProbeMean μ β J δ q₁ q₂ x e p₀ k s-c|≤C*amplitudeLatitudeL1 μ β J δ q₁ q₂ q x e p₀ s
  rw [he']
  convert hb using 1
  unfold amplitudeSingleAverage amplitudeLatitudeL1
  simp_rw [integral_const_mul]
  rfl

theorem amplitudePhysicalProbeMean_center_error_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (s : Fin 2 → ℝ) {q : ℝ} (hq : |q|≤1) :
    |amplitudePhysicalProbeMean μ β J δ q₁ q₂ x e p₀ k s-
      amplitudeCenteredProbeMean μ β J δ q₁ q₂ q x e p₀ k s|≤
      (2*amplitudeProbeLocalizationConstant μ p₀ k)*amplitudeLatitudeL1 μ β J δ q₁ q₂ q x e p₀ s := by
  let f := fun z : Vector (n+1) × Vector (n+1) => amplitudePhysicalProbePolynomial μ p₀ k
    (overlap x z.1) (overlap x z.2) (overlap z.1 z.2)
  let f₀ := fun z : Vector (n+1) × Vector (n+1) => amplitudePhysicalProbePolynomial μ p₀ k q q (overlap z.1 z.2)
  let g := fun u : Vector (n+1) => |overlap x u-q|
  let C := amplitudeProbeLocalizationConstant μ p₀ k
  have hf : Continuous f := by unfold f amplitudePhysicalProbePolynomial overlap;fun_prop
  have hf₀ : Continuous f₀ := by unfold f₀ amplitudePhysicalProbePolynomial overlap;fun_prop
  have hg : Continuous g := by unfold g overlap;fun_prop
  have he (D : BankDisorder n μ) :
      amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s (fun z => f z-f₀ z) D=
        amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s f D-
        amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s f₀ D := by
    unfold amplitudePairAverage
    exact integral_sub (amplitudePairObservable_integrable μ β J δ q₁ q₂ x e p₀ s f hf D)
      (amplitudePairObservable_integrable μ β J δ q₁ q₂ x e p₀ s f₀ hf₀ D)
  have he' : amplitudePhysicalProbeMean μ β J δ q₁ q₂ x e p₀ k s-
      amplitudeCenteredProbeMean μ β J δ q₁ q₂ q x e p₀ k s=
      ∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s (fun z => f z-f₀ z) D ∂bankLaw n μ := by
    simp_rw [he]
    exact (integral_sub (amplitudePairAverage_integrable μ β J δ q₁ q₂ x e p₀ s f hf)
      (amplitudePairAverage_integrable μ β J δ q₁ q₂ x e p₀ s f₀ hf₀)).symm
  have hb := amplitudeExpectedPair_error_le μ β J δ q₁ q₂ x e p₀ s
    (fun z => f z-f₀ z) (fun z => C*(g z.1+g z.2)) (hf.sub hf₀)
    (continuous_const.mul ((hg.comp continuous_fst).add (hg.comp continuous_snd))) (by
      intro u v hu hv
      exact amplitudePhysicalProbePolynomial_center_error_le μ p₀ k
        (abs_le.mpr (overlap_mem_Icc_of_norm_sq (by omega : 1≤n+1) x u hx hu))
        (abs_le.mpr (overlap_mem_Icc_of_norm_sq (by omega : 1≤n+1) x v hx hv)) hq
        (abs_le.mpr (overlap_mem_Icc_of_norm_sq (by omega : 1≤n+1) u v hu hv)))
  have hψ (D : BankDisorder n μ) : amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s
      (fun z => C*(g z.1+g z.2)) D=
      (2*C)*amplitudeSingleAverage μ β J δ q₁ q₂ x e p₀ s g D := by
    let W := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
    let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
    have hi := amplitudeSingleObservable_integrable μ β J δ q₁ q₂ x e p₀ s g hg D
    unfold amplitudePairAverage amplitudeSingleAverage
    rw [integral_const_mul,integral_add (hi.comp_fst W) (hi.comp_snd W),integral_fun_fst,integral_fun_snd]
    simp only [probReal_univ,one_smul]
    ring
  rw [he']
  apply hb.trans_eq
  simp_rw [hψ]
  rw [integral_const_mul]
  rfl

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
