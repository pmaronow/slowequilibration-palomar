-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferPureConsumer
public import SlowEquilibration.SourceConditionedCPTransferInitialAdapter

/-! Conditional pure instances of source `thm:main-condensed` and the
field-independent clauses of `thm:main-initial`. The source-specific
physical capture inputs remain explicit until discharged. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferPureInitial

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalTAPCertificate PureStationarity
open PureCapturePhysicalCoarseDiniAssembly
open SphericalOrthogonalHaar
open SourceConditionedCPTransferPureConsumer
open SourceConditionedCPTransferInitialAdapter
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 700000

/-- The same exponential horizon works for uniform initialization and for
the source supremum over all prescribed, field-independent initial laws. -/
theorem pure_prescribed_initial_separation_of_three_physical_inputs
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hNorm : PhysicalDirectingNormQ
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      uniformSeparationInProbability μ β
        (fun N => exponentialGridHorizon γ N) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨γ,hγ,hsep⟩ := pure_separation_of_three_physical_inputs
    p hp h hNorm hMean hRelocate
  have hhaar : uniformSeparationInProbability μ β
      (fun N => exponentialGridHorizon γ N) :=
    original_uniform_to_haar μ β _ hsep
  exact ⟨γ,hγ,hhaar,fun ε hε =>
    uniformPrescribedFailure_tendsto_zero μ β _ hhaar hε⟩

/-- The independently sampled source initial law may live on any genuine
probability space. The same physical proof supplies its exponent. -/
theorem pure_independent_initial_separation_of_three_physical_inputs
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hNorm : PhysicalDirectingNormQ
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hMean : PhysicalReplicaMeanEnergy
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q
      (pureEnergyConstant p (by omega)))
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega)))
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (J : ∀ N, Ω N → Disorder N
      (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree)
    (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N))
    (hJ : ∀ N, HasLaw (J N)
      (disorderLaw N (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree)
      (P N))
    (hν : ∀ N, AEMeasurable (ν N) (P N))
    (hind : ∀ N, IndepFun (J N) (ν N) (P N))
    (hsphere : ∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧ ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => (P N).real
        {ω | intervalDistance μ β (exponentialGridHorizon γ N)
          (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨γ,hγ,hsep⟩ := pure_separation_of_three_physical_inputs
    p hp h hNorm hMean hRelocate
  refine ⟨γ,hγ,?_⟩
  intro ε hε
  exact independent_initial_failure_of_original_uniform μ β _ hsep
    P J ν hJ hν hind hsphere hε

end SlowEquilibration.SourceConditionedCPTransferPureInitial
