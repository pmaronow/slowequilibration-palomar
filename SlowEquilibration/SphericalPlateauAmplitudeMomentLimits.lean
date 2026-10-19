-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeProbeTargets
public import SlowEquilibration.SphericalPlateauAmplitudeProbeLocalization

@[expose] public section

/-! # Extracting the actual first and second physical overlap moments

The two centered Gaussian probes have strictly positive coefficients. Their
limits determine the ordinary first and second physical overlap moments.
Probability integral identities provide the exact centered expansions;
no normalized transverse overlap is introduced.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory SphericalModel
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Remove a fixed nonzero physical probe coefficient from its moment limit. -/
theorem amplitudeProbeMoment_tendsto_of_scaled {ι : Type*} {l : Filter ι}
    {c a : ℝ} (hc : c ≠ 0) {M : ι → ℝ}
    (hM : Filter.Tendsto (fun i => c * M i) l (𝓝 (c * a))) :
    Filter.Tendsto M l (𝓝 a) := by
  simpa only [mul_div_cancel_left₀ _ hc] using hM.div_const c

/-- The first two centered physical probes determine the uncentered
first moment and second moment, with arbitrary physical target. -/
theorem amplitudePhysicalMoments_tendsto_of_centered_probes
    {ι : Type*} {l : Filter ι} (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (hp₀ : 0 < mixtureCoefficients μ p₀) {q : ℝ} (hq : 0 < q)
    (target : ℝ) (M₁ M₂ : ι → ℝ)
    (h₁ : Filter.Tendsto
      (fun i => amplitudeProbeMomentCoefficient μ p₀ 0 q * (M₁ i - q^2))
      l (𝓝 (amplitudeProbeMomentCoefficient μ p₀ 0 q * (target - q^2))))
    (h₂ : Filter.Tendsto
      (fun i => amplitudeProbeMomentCoefficient μ p₀ 1 q *
        (M₂ i - 2*q^2*M₁ i + q^4))
      l (𝓝 (amplitudeProbeMomentCoefficient μ p₀ 1 q * (target - q^2)^2))) :
    Filter.Tendsto M₁ l (𝓝 target) ∧ Filter.Tendsto M₂ l (𝓝 (target^2)) := by
  have hC₁ := (amplitudeProbeMomentCoefficient_pos μ p₀ hp₀ 0 hq).ne'
  have hC₂ := (amplitudeProbeMomentCoefficient_pos μ p₀ hp₀ 1 hq).ne'
  have hA := amplitudeProbeMoment_tendsto_of_scaled hC₁ h₁
  have hB := amplitudeProbeMoment_tendsto_of_scaled hC₂ h₂
  have hFirst : Filter.Tendsto M₁ l (𝓝 target) := by
    convert hA.add_const (q^2) using 1 <;> simp
  refine ⟨hFirst, ?_⟩
  have hSecond := (hB.add (hFirst.const_mul (2*q^2))).sub_const (q^4)
  convert hSecond using 1
  · funext i
    ring
  · ring

/-- Exact first centered moment under an honest probability law. -/
theorem amplitudeCenteredFirstMoment_eq {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (R : Ω → ℝ)
    (hR : Integrable R ν) (a : ℝ) :
    (∫ ω, (R ω-a) ∂ν) = (∫ ω, R ω ∂ν)-a := by
  rw [integral_sub hR (integrable_const a)]
  simp only [integral_const, probReal_univ, one_smul]

/-- Exact second centered moment under an honest probability law. -/
theorem amplitudeCenteredSecondMoment_eq {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (R : Ω → ℝ)
    (hR : Integrable R ν) (hR₂ : Integrable (fun ω => (R ω)^2) ν) (a : ℝ) :
    (∫ ω, (R ω-a)^2 ∂ν) =
      (∫ ω, (R ω)^2 ∂ν)-2*a*(∫ ω, R ω ∂ν)+a^2 := by
  have he : (fun ω => (R ω-a)^2) =
      (fun ω => (R ω)^2-(2*a)*R ω+a^2) := by
    funext ω
    ring
  have hAdd : (∫ ω, (R ω)^2-(2*a)*R ω+a^2 ∂ν) =
      (∫ ω, (R ω)^2-(2*a)*R ω ∂ν)+a^2 := by
    simpa only [Pi.add_apply, Pi.sub_apply, integral_const, probReal_univ, one_smul]
      using integral_add (hR₂.sub (hR.const_mul (2*a))) (integrable_const (a^2))
  have hSub : (∫ ω, (R ω)^2-(2*a)*R ω ∂ν) =
      (∫ ω, (R ω)^2 ∂ν)-(2*a)*(∫ ω, R ω ∂ν) := by
    simpa only [Pi.sub_apply, integral_const_mul]
      using integral_sub hR₂ (hR.const_mul (2*a))
  rw [he, hAdd, hSub]

/-- Integrability of the actual centered square uses only its honest
ordinary first and second moments. -/
theorem amplitudeCenteredSecondMoment_integrable {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (R : Ω → ℝ)
    (hR : Integrable R ν) (hR₂ : Integrable (fun ω => (R ω)^2) ν) (a : ℝ) :
    Integrable (fun ω => (R ω-a)^2) ν := by
  have he : (fun ω => (R ω-a)^2) =
      (fun ω => (R ω)^2-(2*a)*R ω+a^2) := by
    funext ω
    ring
  rw [he]
  exact (hR₂.sub (hR.const_mul (2*a))).add (integrable_const (a^2))

/-- Literal centered physical kernel integral, with its true polynomial
coefficient pulled outside the expectation. -/
theorem amplitudePhysicalProbePolynomial_center_integral {Ω : Type*}
    [MeasurableSpace Ω] (ν : Measure Ω) (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (q : ℝ) (R : Ω → ℝ) :
    (∫ ω, amplitudePhysicalProbePolynomial μ p₀ k q q (R ω) ∂ν) =
      amplitudeProbeMomentCoefficient μ p₀ k q *
        (∫ ω, (R ω-q^2)^(k.val+1) ∂ν) := by
  simp_rw [amplitudePhysicalProbePolynomial_center_eq_moment]
  rw [integral_const_mul]

/-- Physical squared overlap error is exactly its first/second moment
combination under the actual probability measure. -/
theorem amplitudePhysicalPairError_eq_moments {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (R : Ω → ℝ)
    (hR : Integrable R ν) (hR₂ : Integrable (fun ω => (R ω)^2) ν)
    (target : ℝ) :
    (∫ ω, (R ω-target)^2 ∂ν) =
      (∫ ω, (R ω)^2 ∂ν)-2*target*(∫ ω, R ω ∂ν)+target^2 :=
  amplitudeCenteredSecondMoment_eq ν R hR hR₂ target

/-- Once the actual first and second moments converge to the target and
its square, the expected physical squared pair error converges to zero. -/
theorem amplitudePhysicalPairError_tendsto_zero_of_moments
    {ι : Type*} {l : Filter ι} (target : ℝ) (M₁ M₂ E : ι → ℝ)
    (hE : ∀ i, E i=M₂ i-2*target*M₁ i+target^2)
    (h₁ : Filter.Tendsto M₁ l (𝓝 target))
    (h₂ : Filter.Tendsto M₂ l (𝓝 (target^2))) :
    Filter.Tendsto E l (𝓝 0) := by
  have hh := (h₂.sub (h₁.const_mul (2*target))).add_const (target^2)
  convert hh using 1
  · funext i
    exact hE i
  · ring

/-- Scalar interface for expectations under the actual varying-dimension
laws: exact centered first/second identities and the two centered probe
limits imply both physical moment limits and vanishing pair error. -/
theorem amplitudePhysicalMoments_and_pairError_tendsto_of_centered_probes
    {ι : Type*} {l : Filter ι} (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (hp₀ : 0 < mixtureCoefficients μ p₀) {q : ℝ} (hq : 0 < q)
    (target : ℝ) (C : Fin 2 → ι → ℝ) (M₁ M₂ E : ι → ℝ)
    (hC₁ : ∀ i, C 0 i=M₁ i-q^2)
    (hC₂ : ∀ i, C 1 i=M₂ i-2*q^2*M₁ i+q^4)
    (hE : ∀ i, E i=M₂ i-2*target*M₁ i+target^2)
    (hProbes : ∀ k : Fin 2, Filter.Tendsto
      (fun i => amplitudeProbeMomentCoefficient μ p₀ k q * C k i)
      l (𝓝 (amplitudeProbeMomentCoefficient μ p₀ k q *
        (target-q^2)^(k.val+1)))) :
    Filter.Tendsto M₁ l (𝓝 target) ∧
      Filter.Tendsto M₂ l (𝓝 (target^2)) ∧ Filter.Tendsto E l (𝓝 0) := by
  have h₁ := hProbes 0
  have h₂ := hProbes 1
  simp only [hC₁, Fin.val_zero, Nat.zero_add, pow_one] at h₁
  simp only [hC₂] at h₂
  have hMoments := amplitudePhysicalMoments_tendsto_of_centered_probes μ p₀ hp₀ hq target
    M₁ M₂ h₁ h₂
  exact ⟨hMoments.1, hMoments.2,
    amplitudePhysicalPairError_tendsto_zero_of_moments target M₁ M₂ E hE hMoments.1 hMoments.2⟩

/-- A single honest probability-law statement: the limits of the two
literal physical probe integrals give the ordinary first and second
overlap limits and then the expected physical squared pair-error limit.
The state space and probability law may vary with the index. -/
theorem amplitudePhysicalMoments_and_pairError_tendsto_of_probe_integrals
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {l : Filter ι}
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (R : ∀ i, Ω i → ℝ)
    (hR : ∀ i, Integrable (R i) (ν i))
    (hR₂ : ∀ i, Integrable (fun ω => (R i ω)^2) (ν i))
    (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (hp₀ : 0 < mixtureCoefficients μ p₀) {q : ℝ} (hq : 0 < q)
    (target : ℝ)
    (hProbes : ∀ k : Fin 2, Filter.Tendsto
      (fun i => ∫ ω, amplitudePhysicalProbePolynomial μ p₀ k q q (R i ω) ∂ν i)
      l (𝓝 (amplitudeProbeMomentCoefficient μ p₀ k q *
        (target-q^2)^(k.val+1)))) :
    Filter.Tendsto (fun i => ∫ ω, R i ω ∂ν i) l (𝓝 target) ∧
      Filter.Tendsto (fun i => ∫ ω, (R i ω)^2 ∂ν i) l (𝓝 (target^2)) ∧
      Filter.Tendsto (fun i => ∫ ω, (R i ω-target)^2 ∂ν i) l (𝓝 0) := by
  have hIdentity₁ (i : ι) :
      (∫ ω, amplitudePhysicalProbePolynomial μ p₀ 0 q q (R i ω) ∂ν i) =
        amplitudeProbeMomentCoefficient μ p₀ 0 q * ((∫ ω, R i ω ∂ν i)-q^2) := by
    rw [amplitudePhysicalProbePolynomial_center_integral]
    simp only [Fin.val_zero, Nat.zero_add, pow_one]
    rw [amplitudeCenteredFirstMoment_eq (ν i) (R i) (hR i)]
  have hIdentity₂ (i : ι) :
      (∫ ω, amplitudePhysicalProbePolynomial μ p₀ 1 q q (R i ω) ∂ν i) =
        amplitudeProbeMomentCoefficient μ p₀ 1 q *
          ((∫ ω, (R i ω)^2 ∂ν i)-2*q^2*(∫ ω, R i ω ∂ν i)+q^4) := by
    rw [amplitudePhysicalProbePolynomial_center_integral]
    change amplitudeProbeMomentCoefficient μ p₀ 1 q * (∫ ω, (R i ω-q^2)^2 ∂ν i) = _
    rw [amplitudeCenteredSecondMoment_eq (ν i) (R i) (hR i) (hR₂ i)]
    ring
  have h₁ := hProbes 0
  have h₂ := hProbes 1
  simp only [hIdentity₁, Fin.val_zero, Nat.zero_add, pow_one] at h₁
  simp only [hIdentity₂] at h₂
  have hMoments := amplitudePhysicalMoments_tendsto_of_centered_probes μ p₀ hp₀ hq target
    (fun i => ∫ ω, R i ω ∂ν i) (fun i => ∫ ω, (R i ω)^2 ∂ν i) h₁ h₂
  refine ⟨hMoments.1, hMoments.2, ?_⟩
  exact amplitudePhysicalPairError_tendsto_zero_of_moments target _ _ _
    (fun i => amplitudePhysicalPairError_eq_moments (ν i) (R i) (hR i) (hR₂ i) target)
    hMoments.1 hMoments.2

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
