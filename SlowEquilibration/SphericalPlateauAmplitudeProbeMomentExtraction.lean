-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeProbeMoments

@[expose] public section

/-! # Physical moment extraction from actual derivatives and localization

Both Gaussian responses are the literal finite amplitude derivatives.
The localization input is the true bank-averaged one-replica latitude L¹
error. These two analytic inputs yield the actual weighted two-replica
overlap first and second moments and its vanishing physical pair error.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalForm
open scoped Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def amplitudePhysicalOverlapFirst (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) : ℝ :=
  ∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s
    (fun z => overlap z.1 z.2) D ∂bankLaw n μ

def amplitudePhysicalOverlapSecond (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) : ℝ :=
  ∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s
    (fun z => (overlap z.1 z.2)^2) D ∂bankLaw n μ

def amplitudePhysicalOverlapCenteredMoment (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (s : Fin 2 → ℝ) : ℝ :=
  ∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s
    (fun z => (overlap z.1 z.2-q^2)^(k.val+1)) D ∂bankLaw n μ

theorem amplitudeCenteredProbeMean_eq_moment (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (s : Fin 2 → ℝ) :
    amplitudeCenteredProbeMean μ β J δ q₁ q₂ q x e p₀ k s=
      amplitudeProbeMomentCoefficient μ p₀ k q*
        amplitudePhysicalOverlapCenteredMoment μ β J δ q₁ q₂ q x e p₀ k s := by
  unfold amplitudeCenteredProbeMean amplitudePhysicalOverlapCenteredMoment amplitudePairAverage
  simp_rw [amplitudePhysicalProbePolynomial_center_eq_moment,integral_const_mul]

theorem amplitudeExpectedPair_centered_first_eq (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (R : Vector (n+1) × Vector (n+1) → ℝ) (hR : Continuous R) (a : ℝ) :
    (∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s (fun z => R z-a) D ∂bankLaw n μ)=
      (∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s R D ∂bankLaw n μ)-a := by
  have he (D : BankDisorder n μ) : amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s (fun z => R z-a) D=
      amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s R D-a := by
    let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
    exact amplitudeCenteredFirstMoment_eq _ R
      (amplitudePairObservable_integrable μ β J δ q₁ q₂ x e p₀ s R hR D) a
  simp_rw [he]
  rw [integral_sub (amplitudePairAverage_integrable μ β J δ q₁ q₂ x e p₀ s R hR) (integrable_const a)]
  simp only [integral_const,probReal_univ,one_smul]

theorem amplitudeExpectedPair_centered_sq_eq (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (R : Vector (n+1) × Vector (n+1) → ℝ) (hR : Continuous R) (a : ℝ) :
    (∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s (fun z => (R z-a)^2) D ∂bankLaw n μ)=
      (∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s (fun z => (R z)^2) D ∂bankLaw n μ)-
      2*a*(∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s R D ∂bankLaw n μ)+a^2 := by
  have hR₂ : Continuous (fun z => (R z)^2) := hR.pow 2
  have he (D : BankDisorder n μ) : amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s (fun z => (R z-a)^2) D=
      amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s (fun z => (R z)^2) D-
      2*a*amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s R D+a^2 := by
    let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x e p₀ s D
    exact amplitudeCenteredSecondMoment_eq _ R
      (amplitudePairObservable_integrable μ β J δ q₁ q₂ x e p₀ s R hR D)
      (amplitudePairObservable_integrable μ β J δ q₁ q₂ x e p₀ s (fun z => (R z)^2) hR₂ D) a
  have hi := amplitudePairAverage_integrable μ β J δ q₁ q₂ x e p₀ s R hR
  have hi₂ := amplitudePairAverage_integrable μ β J δ q₁ q₂ x e p₀ s (fun z => (R z)^2) hR₂
  simp_rw [he]
  have hAdd := integral_add (hi₂.sub (hi.const_mul (2*a))) (integrable_const (a^2))
  have hSub := integral_sub hi₂ (hi.const_mul (2*a))
  simp only [Pi.sub_apply] at hAdd hSub
  rw [hAdd,hSub,integral_const_mul]
  simp only [integral_const,probReal_univ,one_smul]

theorem amplitudePhysicalOverlapCenteredMoment_first (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    amplitudePhysicalOverlapCenteredMoment μ β J δ q₁ q₂ q x e p₀ 0 s=
      amplitudePhysicalOverlapFirst μ β J δ q₁ q₂ x e p₀ s-q^2 := by
  unfold amplitudePhysicalOverlapCenteredMoment amplitudePhysicalOverlapFirst
  simp only [Fin.val_zero,Nat.zero_add,pow_one]
  apply amplitudeExpectedPair_centered_first_eq
  unfold overlap
  fun_prop

theorem amplitudePhysicalOverlapCenteredMoment_second (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    amplitudePhysicalOverlapCenteredMoment μ β J δ q₁ q₂ q x e p₀ 1 s=
      amplitudePhysicalOverlapSecond μ β J δ q₁ q₂ x e p₀ s-
      2*q^2*amplitudePhysicalOverlapFirst μ β J δ q₁ q₂ x e p₀ s+q^4 := by
  have hh := amplitudeExpectedPair_centered_sq_eq μ β J δ q₁ q₂ x e p₀ s
    (fun z => overlap z.1 z.2) (by unfold overlap;fun_prop) (q^2)
  unfold amplitudePhysicalOverlapCenteredMoment amplitudePhysicalOverlapFirst amplitudePhysicalOverlapSecond
  change (∫ D,amplitudePairAverage μ β J δ q₁ q₂ x e p₀ s
    (fun z => (overlap z.1 z.2-q^2)^2) D ∂bankLaw n μ)=_
  rw [hh]
  ring_nf

theorem amplitudePairError_expectation_eq_moments (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    (∫ D,amplitudePairError μ β J δ q₁ q₂ q x e p₀ s D ∂bankLaw n μ)=
      amplitudePhysicalOverlapSecond μ β J δ q₁ q₂ x e p₀ s-
      2*q*amplitudePhysicalOverlapFirst μ β J δ q₁ q₂ x e p₀ s+q^2 := by
  exact amplitudeExpectedPair_centered_sq_eq μ β J δ q₁ q₂ x e p₀ s
    (fun z => overlap z.1 z.2) (by unfold overlap;fun_prop) q

/-- Actual derivatives and actual physical latitude L¹ localization give
both centered physical polynomial probe limits. -/
theorem amplitudeCenteredProbeMean_tendsto_of_derivative_localization
    (μ : FiniteMixture) {β : ℝ} (hβ : β≠0) (J δ q₁ q₂ : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {q : ℝ} (hq : q∈Ioo (0:ℝ) 1)
    (x : (n : ℕ) → Vector (n+1)) (hx : ∀ n,‖x n‖^2=((n+1:ℕ):ℝ))
    (hLatitude : Tendsto (fun n => amplitudeLatitudeL1 μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (0:ℝ)))
    (hDerivative : Tendsto (fun n => amplitudePressureDerivative μ β J δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ k 0) atTop
      (𝓝 (2*amplitudeDiracShiftCoefficient μ β p₀ k q))) :
    Tendsto (fun n => amplitudeCenteredProbeMean μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ k (fun _ => 1)) atTop
      (𝓝 (amplitudeProbeMomentCoefficient μ p₀ k q*(q-q^2)^(k.val+1))) := by
  have hqabs : |q|≤1 := abs_le.mpr ⟨by linarith [hq.1],hq.2.le⟩
  let D := fun n => amplitudeDiagonalProbeMean μ β J δ q₁ q₂ (x n) (latitudeFrameAt (x n)) p₀ k (fun _ => 1)
  let P := fun n => amplitudePhysicalProbeMean μ β J δ q₁ q₂ (x n) (latitudeFrameAt (x n)) p₀ k (fun _ => 1)
  let C := fun n => amplitudeCenteredProbeMean μ β J δ q₁ q₂ q (x n) (latitudeFrameAt (x n)) p₀ k (fun _ => 1)
  have hBound : Tendsto (fun n => (2*amplitudeProbeLocalizationConstant μ p₀ k)*
      amplitudeLatitudeL1 μ β J δ q₁ q₂ q (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using hLatitude.const_mul (2*amplitudeProbeLocalizationConstant μ p₀ k)
  have hD : Tendsto D atTop (𝓝 (amplitudeSelectedCoefficient μ p₀ k q)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    exact squeeze_zero (fun n => abs_nonneg _) (fun n => amplitudeDiagonalProbeMean_center_error_le
      μ β J δ q₁ q₂ (x n) (hx n) (latitudeFrameAt (x n)) p₀ k (fun _ => 1) hqabs) hBound
  have hPscaled := (hD.const_mul (β^2)).sub hDerivative
  have he : (fun n => β^2*D n-amplitudePressureDerivative μ β J δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ k 0)=(fun n => β^2*P n) := by
    funext n
    rw [amplitudePressureDerivative_zero_eq_probeMeans μ β J δ q₁ q₂ (x n) (hx n) p₀ k]
    dsimp only [D,P]
    ring_nf
  rw [he,amplitudeProbe_source_target_identity μ β p₀ k hq.1.le] at hPscaled
  have hP : Tendsto P atTop (𝓝 (amplitudeProbeMomentCoefficient μ p₀ k q*(q-q^2)^(k.val+1))) := by
    apply amplitudeProbeMoment_tendsto_of_scaled (pow_ne_zero 2 hβ)
    simpa only [mul_assoc] using hPscaled
  have hPC : Tendsto (fun n => P n-C n) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    exact squeeze_zero (fun n => abs_nonneg _) (fun n => amplitudePhysicalProbeMean_center_error_le
      μ β J δ q₁ q₂ (x n) (hx n) (latitudeFrameAt (x n)) p₀ k (fun _ => 1) hqabs) hBound
  have hh := hP.sub hPC
  convert hh using 1
  · funext n
    change C n=P n-(P n-C n)
    ring_nf
  · ring

/-- The actual two amplitude responses extract the ordinary first and
second physical overlap moments, and force the literal pair error to zero.
No measurable-kernel or integrability premise is supplied by the caller. -/
theorem amplitudePhysicalMoments_and_pairError_tendsto_of_derivatives_localization
    (μ : FiniteMixture) {β : ℝ} (hβ : β≠0) (J δ q₁ q₂ : ℝ)
    (p₀ : Degree μ.maxDegree) (hp₀ : 0 < mixtureCoefficients μ p₀)
    {q : ℝ} (hq : q∈Ioo (0:ℝ) 1)
    (x : (n : ℕ) → Vector (n+1)) (hx : ∀ n,‖x n‖^2=((n+1:ℕ):ℝ))
    (hLatitude : Tendsto (fun n => amplitudeLatitudeL1 μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (0:ℝ)))
    (hDerivatives : ∀ k : Fin 2,Tendsto (fun n => amplitudePressureDerivative μ β J δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ k 0) atTop
      (𝓝 (2*amplitudeDiracShiftCoefficient μ β p₀ k q))) :
    Tendsto (fun n => amplitudePhysicalOverlapFirst μ β J δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 q) ∧
    Tendsto (fun n => amplitudePhysicalOverlapSecond μ β J δ q₁ q₂
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)) atTop (𝓝 (q^2)) ∧
    Tendsto (fun n => ∫ D,amplitudePairError μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1) D ∂bankLaw n μ) atTop (𝓝 (0:ℝ)) := by
  apply amplitudePhysicalMoments_and_pairError_tendsto_of_centered_probes μ p₀ hp₀ hq.1 q
    (fun k n => amplitudePhysicalOverlapCenteredMoment μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ k (fun _ => 1))
  · intro n
    exact amplitudePhysicalOverlapCenteredMoment_first μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)
  · intro n
    exact amplitudePhysicalOverlapCenteredMoment_second μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)
  · intro n
    exact amplitudePairError_expectation_eq_moments μ β J δ q₁ q₂ q
      (x n) (latitudeFrameAt (x n)) p₀ (fun _ => 1)
  · intro k
    simpa only [amplitudeCenteredProbeMean_eq_moment] using
      amplitudeCenteredProbeMean_tendsto_of_derivative_localization μ hβ J δ q₁ q₂ p₀ k hq x hx hLatitude (hDerivatives k)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
