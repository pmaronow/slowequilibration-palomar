-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeProbeAverages
public import SlowEquilibration.SphericalPlateauAmplitudeMomentLimits
public import SlowEquilibration.SphericalPlateauAmplitudeIBP
public import SlowEquilibration.SphericalPlateauAmplitudeDerivativeLimit

@[expose] public section

/-! # Actual amplitude responses determine physical replica moments

The exact finite Gaussian integration by parts, physical polynomial
localization, and both positive probe coefficients yield the genuine
physical overlap variance limit. Actual amplitude derivative limits and
actual latitude L¹ localization remain explicit analytic inputs.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalForm GaussianReplicaCalculus
open scoped Topology
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem amplitudeProbeReplicaDifference_eq_polynomial (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ)) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    amplitudeProbeReplicaDifference μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ k s D=
      (β^2*(n+1:ℝ))*(
        amplitudeSingleAverage μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s
          (fun u => amplitudeSelectedCoefficient μ p₀ k (overlap x u)) D-
        amplitudePairAverage μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s
          (fun z => amplitudePhysicalProbePolynomial μ p₀ k (overlap x z.1)
            (overlap x z.2) (overlap z.1 z.2)) D) := by
  let W := amplitudeWeightedLaw μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D
  let K := selectedKernel (amplitudeBankLinear μ β x (latitudeFrameAt x) p₀ (fun _ => 1))
    (amplitudeBankLabel μ p₀ k)
  let A := β^2*(n+1:ℝ)
  let f := fun z : Vector (n+1) × Vector (n+1) => amplitudePhysicalProbePolynomial μ p₀ k
    (overlap x z.1) (overlap x z.2) (overlap z.1 z.2)
  let _ := amplitudeWeightedLaw_probability μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D
  have hK (u v : Vector (n+1)) : K u v=A*f (u,v) := by
    simpa only [K,A,f,Nat.cast_add,Nat.cast_one] using
      selectedKernel_amplitudeBankLinear_canonical μ β x hx p₀ k u v
  have hf : Continuous f := by unfold f amplitudePhysicalProbePolynomial overlap;fun_prop
  have hDiag : (∫ u,K u u ∂W)=A*amplitudeSingleAverage μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s
      (fun u => amplitudeSelectedCoefficient μ p₀ k (overlap x u)) D := by
    unfold amplitudeSingleAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [weightedLaw_support (by omega : 1≤n+1) β
      (amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s D) (sourceProfile J δ q₁ q₂) x] with u hu
    rw [hK]
    dsimp only [f]
    rw [overlap_self (by omega : 1≤n+1) u hu,amplitudePhysicalProbePolynomial_diag]
  have hPair : (∫ u,∫ v,K u v ∂W ∂W)=A*amplitudePairAverage μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s f D := by
    simp_rw [hK,integral_const_mul]
    rw [← integral_prod f (amplitudePairObservable_integrable μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s f hf D)]
    rfl
  change (∫ u,K u u ∂W)-(∫ u,∫ v,K u v ∂W ∂W)=_
  rw [hDiag,hPair]
  dsimp only [A,f]
  ring_nf

/-- Literal finite amplitude derivative at amplitude one, expressed
under the original independent Gaussian bank law. -/
theorem amplitudePressureDerivative_zero_eq_probeMeans (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ)) (p₀ : Degree μ.maxDegree) (k : Fin 2) :
    amplitudePressureDerivative μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ k 0=
      β^2*(amplitudeDiagonalProbeMean μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ k (fun _ => 1)-
        amplitudePhysicalProbeMean μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ k (fun _ => 1)) := by
  let f := fun u : Vector (n+1) => amplitudeSelectedCoefficient μ p₀ k (overlap x u)
  let g := fun z : Vector (n+1) × Vector (n+1) => amplitudePhysicalProbePolynomial μ p₀ k
    (overlap x z.1) (overlap x z.2) (overlap z.1 z.2)
  have hf : Continuous f := by unfold f amplitudeSelectedCoefficient overlap;fun_prop
  have hg : Continuous g := by unfold g amplitudePhysicalProbePolynomial overlap;fun_prop
  let F := amplitudeProbeReplicaDifference μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ k (fun _ => 1)
  have hF : Measurable F := by
    have he : F=fun D => (β^2*(n+1:ℝ))*(
        amplitudeSingleAverage μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) f D-
        amplitudePairAverage μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) g D) :=
      funext fun D => amplitudeProbeReplicaDifference_eq_polynomial μ β J δ q₁ q₂ x hx p₀ k (fun _ => 1) D
    rw [he]
    exact measurable_const.mul ((amplitudeSingleAverage_measurable μ β J δ q₁ q₂ x
      (latitudeFrameAt x) p₀ (fun _ => 1) f hf.measurable).sub
      (amplitudePairIntegral_measurable μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) g hg.measurable))
  have hLaw := (actual_bank_flattened_gaussian n μ).integral_comp
    (hF.comp (unpackBankCLM n μ).continuous.measurable).aestronglyMeasurable
  simp only [Function.comp_apply,unpackBank_euclideanBank] at hLaw
  rw [amplitudePressureDerivative_eq_physical_replicas,amplitudeAt_zero,← hLaw]
  simp_rw [F,amplitudeProbeReplicaDifference_eq_polynomial μ β J δ q₁ q₂ x hx p₀ k (fun _ => 1)]
  rw [integral_const_mul,integral_sub
    (amplitudeSingleAverage_integrable μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) f hf)
    (amplitudePairAverage_integrable μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ (fun _ => 1) g hg)]
  unfold amplitudeDiagonalProbeMean amplitudePhysicalProbeMean
  have hN : (n+1:ℝ)≠0 := by positivity
  simp only [f,g,add_zero]
  field_simp [hN]

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
