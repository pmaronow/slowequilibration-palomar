-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeWeightedKernel
public import SlowEquilibration.SphericalPlateauAmplitudeNormErrorLaw
public import SlowEquilibration.SphericalWeightedReplicaGeometry

@[expose] public section

/-! # Actual amplitude replica variance controls the physical mean norm error -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter SphericalWeightedReplicaGeometry
open scoped Topology
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- The genuine weighted two-replica overlap squared error. -/
def amplitudePairError (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) : ℝ :=
  ∫ z : Vector (n+1) × Vector (n+1),(overlap z.1 z.2-q)^2
    ∂(amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D).prod
      (amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D)

theorem amplitudePairError_measurable (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Measurable (amplitudePairError μ β J δ q₁ q₂ q x e p₀ s) :=
  amplitudePairIntegral_measurable μ β J δ q₁ q₂ x e p₀ s _ (by
    apply Continuous.measurable
    unfold overlap
    fun_prop)

theorem amplitudePairError_nonneg (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    0≤amplitudePairError μ β J δ q₁ q₂ q x e p₀ s D := integral_nonneg fun _ => sq_nonneg _

theorem amplitudePairError_le_four (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    amplitudePairError μ β J δ q₁ q₂ q x e p₀ s D≤4 := by
  let W := amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
  have hs : ∀ᵐ u ∂W,‖u‖^2=((n+1:ℕ):ℝ) := weightedLaw_support (by omega) β
    (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x
  have hm := overlap_deviation_memLp (by omega : 1≤n+1) W hs q
  have hBound : ∀ᵐ z : Vector (n+1) × Vector (n+1) ∂W.prod W,(overlap z.1 z.2-q)^2≤4 := by
    filter_upwards [sphereSupported_prod W hs] with z hz
    have hr := overlap_mem_Icc_of_norm_sq (by omega : 1≤n+1) z.1 z.2 hz.1 hz.2
    have h1 := hq.1
    have h2 := hq.2
    have hr1 := hr.1
    have hr2 := hr.2
    nlinarith
  have hi := hm.integrable_sq
  have hh := integral_mono_ae hi (integrable_const (4:ℝ)) hBound
  change (∫ z : Vector (n+1) × Vector (n+1),(overlap z.1 z.2-q)^2 ∂W.prod W)≤4
  simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul] using hh

theorem amplitudePairError_integrable (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Integrable (amplitudePairError μ β J δ q₁ q₂ q x e p₀ s) (bankLaw n μ) :=
  Integrable.of_bound (amplitudePairError_measurable μ β J δ q₁ q₂ q x e p₀ s).aestronglyMeasurable 4
    (.of_forall fun D => by
      rw [Real.norm_eq_abs,abs_of_nonneg (amplitudePairError_nonneg μ β J δ q₁ q₂ q x e p₀ s D)]
      exact amplitudePairError_le_four μ β J δ q₁ q₂ hq x e p₀ s D)

theorem amplitudeNormError_le_one (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    amplitudeNormError μ β J δ q₁ q₂ q x e p₀ s D≤1 := by
  have hB := barycenter_norm_le_one (by omega : 1≤n+1) β
    (amplitudePlantedField_contDiff μ β x e p₀ s D).continuous
    (sourceProfile_contDiff J δ q₁ q₂) x
  have hs : ‖barycenter β (amplitudePlantedField μ β x e p₀ s D)
      (sourceProfile J δ q₁ q₂) x‖^2≤1 := by
    nlinarith [norm_nonneg (barycenter β (amplitudePlantedField μ β x e p₀ s D)
      (sourceProfile J δ q₁ q₂) x)]
  have hq1 := hq.1
  have hq2 := hq.2
  unfold amplitudeNormError
  nlinarith [sq_nonneg ‖barycenter β (amplitudePlantedField μ β x e p₀ s D)
    (sourceProfile J δ q₁ q₂) x‖]

/-- Genuine expected physical barycenter error is controlled by the
actual expected weighted overlap variance. -/
theorem amplitudeNormError_expectation_le_pairError (μ : FiniteMixture)
    (β J δ q₁ q₂ : ℝ) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    (∫ D,amplitudeNormError μ β J δ q₁ q₂ q x e p₀ s D ∂bankLaw n μ)≤
      ∫ D,amplitudePairError μ β J δ q₁ q₂ q x e p₀ s D ∂bankLaw n μ := by
  have hi : Integrable (amplitudeNormError μ β J δ q₁ q₂ q x e p₀ s) (bankLaw n μ) :=
    Integrable.of_bound (amplitudeNormError_measurable μ β J δ q₁ q₂ q x e p₀ s).aestronglyMeasurable 1
      (.of_forall fun D => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact amplitudeNormError_le_one μ β J δ q₁ q₂ hq x e p₀ s D)
  apply integral_mono hi (amplitudePairError_integrable μ β J δ q₁ q₂ hq x e p₀ s)
  intro D
  exact barycenter_deviation_sq_le (by omega : 1≤n+1) β
    (amplitudePlantedField_contDiff μ β x e p₀ s D).continuous
    (sourceProfile_contDiff J δ q₁ q₂) x q

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
