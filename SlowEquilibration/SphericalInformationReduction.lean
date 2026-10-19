-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalFieldEntryMass
public import SlowEquilibration.ReductionInformationEventually
public import SlowEquilibration.ReductionEntropyTransfer

/-! Source `prop:red-information` and `cor:red-entropy` for the actual
mixed spherical polynomial field and physical diffusion. The original
Borel equivariant bands, fixed-window Gibbs capture and polynomial uniform
entry q are the source premises. Information is I(H;X₀), and the conclusion
is the literal infimum of TV over the entire physical time interval. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInformationReduction

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalDynamics SphericalRotationCovariance SphericalFieldKernels
open SphericalAging.HardSphereDynamics ReductionJointInformation
open ReductionInformation ReductionEntropy VaryingProbability
open scoped Topology NNReal ENNReal ProbabilityTheory

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] mixedTransitionKernel

/-- Full actual spherical source information reduction. It includes
singular field-dependent initial laws, extended KL and all source times. -/
theorem information_allTime_separation (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (κ : ∀ N, Kernel (Field N μ) (Vector N)) [∀ N, IsMarkovKernel (κ N)]
    (B : ∀ N, ℝ → Set (Field N μ × Vector N)) (hB : ∀ N M, MeasurableSet (B N M))
    (hsupport : ∀ N, 2 ≤ N → ∀ H, ∀ᵐ x ∂κ N H, OnSphere x)
    (hrot : ∀ M : ℝ, 0 < M → ∀ N, 2 ≤ N →
      ∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) J,
      pullbackBand μ (B N M) (rotatedDisorder U J) = U '' pullbackBand μ (B N M) J)
    {ζ : ℝ} (hζ : 0 < ζ)
    (hpoly : ∀ M : ℝ, 0 < M → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N in atTop, uniformEntryMass μ β (T N) (B N M) ≤ C*(N : ℝ)^(-ζ))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop,
        (∫ H, (gibbsKernel (N := N) μ β H).real (Prod.mk H ⁻¹' B N M)ᶜ ∂fieldLaw N μ) < η)
    (hI : LittleLog (fun N => endpointMutualInformation (fieldLaw N μ) (κ N))) :
    InProbability (fun N => fieldLaw N μ)
      (fun N => intervalDistance μ β (T N) (κ N)) 1 := by
  have hequal (M : ℝ) (hM : 0 < M) :
      ∀ᶠ N in atTop, ∀ᵐ x ∂(κ N ∘ₘ fieldLaw N μ),
      (∫ H, (transitionKernel (N := N) μ β (T N) (H,x)).real
        (Prod.mk H ⁻¹' B N M) ∂fieldLaw N μ) = uniformEntryMass μ β (T N) (B N M) := by
    filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
    have hs := ReductionInformationSupport.marginal_support (fieldLaw N μ) (κ N)
      (sphere_measurableSet N) (.of_forall (hsupport N hN))
    filter_upwards [hs] with x hx
    exact point_entry_eq_uniform (by omega) μ β (T N) (hB N M) (hrot M hM N hN) x hx
  have hend := ReductionInformationEventually.information_endpoint_separation
    (fun N => fieldLaw N μ) κ (fun N => gibbsKernel (N := N) μ β)
    (fun N => transitionKernel (N := N) μ β (T N)) B hB
    (fun N M => uniformEntryMass μ β (T N) (B N M)) hζ hequal hpoly hcapture hI
  apply ReductionInformationEventually.inProbability_congr_eventually
    (fun N => fieldLaw N μ) _ (fun N => intervalDistance μ β (T N) (κ N)) 1 _ hend
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  intro H
  exact (intervalDistance_eq_endpoint hN μ β (T N) (κ N) H).symm

/-- Full source entropy reduction: actual conditional KL/log N only
vanishes in probability; infinite entropies may occur on rare fields. -/
theorem entropy_allTime_separation (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (κ : ∀ N, Kernel (Field N μ) (Vector N)) [∀ N, IsMarkovKernel (κ N)]
    (B : ∀ N, ℝ → Set (Field N μ × Vector N)) (hB : ∀ N M, MeasurableSet (B N M))
    {ζ : ℝ} (hζ : 0 < ζ)
    (hpoly : ∀ M : ℝ, 0 < M → ∃ C : ℝ,
      ∀ᶠ N in atTop, uniformEntryMass μ β (T N) (B N M) ≤ C*(N : ℝ)^(-ζ))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop,
        (∫ H, (gibbsKernel (N := N) μ β H).real (Prod.mk H ⁻¹' B N M)ᶜ ∂fieldLaw N μ) < η)
    (hI : LittleLogInProbability (fun N => fieldLaw N μ)
      (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N))) :
    InProbability (fun N => fieldLaw N μ)
      (fun N => intervalDistance μ β (T N) (κ N)) 1 := by
  let _ : ∀ N, IsProbabilityMeasure (sphereLaw N) := fun N => sphereLaw_probability N
  have hpoly' (M : ℝ) (hM : 0 < M) : ∃ C : ℝ, ∀ᶠ N in atTop,
      (∫ H, conditionalMass (Kernel.const (Field N μ) (sphereLaw N))
        (transitionKernel (N := N) μ β (T N)) (B N M) H ∂fieldLaw N μ) ≤ C*(N:ℝ)^(-ζ) := by
    obtain ⟨C,hC⟩ := hpoly M hM
    refine ⟨C,?_⟩
    filter_upwards [hC,eventually_ge_atTop (1:ℕ)] with N hCN hN
    rw [uniform_conditional_mass_eq hN μ β (T N) (hB N M)]
    exact hCN
  have hend := ReductionEntropyTransfer.entropy_endpoint_separation
    (fun N => fieldLaw N μ) κ (fun N => gibbsKernel (N := N) μ β)
    (fun N => sphereLaw N) (fun N => transitionKernel (N := N) μ β (T N))
    B hB hζ hpoly' hcapture hI
  apply ReductionInformationEventually.inProbability_congr_eventually
    (fun N => fieldLaw N μ) _ (fun N => intervalDistance μ β (T N) (κ N)) 1 _ hend
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  intro H
  exact (intervalDistance_eq_endpoint hN μ β (T N) (κ N) H).symm

end SlowEquilibration.SphericalInformationReduction
