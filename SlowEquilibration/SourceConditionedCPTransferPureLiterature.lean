-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferPureInitial
public import SlowEquilibration.SourceLiteraturePhysicalNormQ
public import SlowEquilibration.PureReplicaMeanEnergyAssembly

/-! Conditional pure instances of source `thm:main-condensed` and the
field-independent clauses of `thm:main-initial` in which the directing-norm
premise is discharged from the cited Chen, Chen–Sen and Subag theorems, and
the ordinary replicated-mean energy estimate from the cited Chen and Subag
Proposition 24 theorems. High-energy relocation remains an explicit
manuscript-specific premise. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferPureLiterature

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate
open PureCapturePhysicalCoarseDiniAssembly SphericalOrthogonalHaar
open SourceConditionedCPTransferPureConsumer SourceConditionedCPTransferPureInitial
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open SourceLiteraturePhysicalNormQ LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SphericalOverlapExponential PureStationarity
open LiteratureSubagProposition24 PureReplicaMeanEnergyAssembly
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 700000

/-- Pure `p ≥ 4`: the uniform-start and prescribed-initial separation, with
the directing norm supplied by the literature interfaces. -/
theorem pure_prescribed_initial_separation_of_literature
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le))
    (h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
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
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0) :=
  pure_prescribed_initial_separation_of_three_physical_inputs p hp h
    (physicalDirectingNormQ_of_cited_theorems hChen hChenSen h h5 h25)
    hMean hRelocate

/-- Pure `p ≥ 4`: the same separation with both the directing norm and the
replicated-mean energy estimate supplied by the literature interfaces. The
only remaining manuscript-specific premise is high-energy relocation. -/
theorem pure_prescribed_initial_separation_of_literature_and_relocation
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le))
    (h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q)
    (hRelocate : PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega))) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      uniformSeparationInProbability μ β
        (fun N => exponentialGridHorizon γ N) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0) :=
  pure_prescribed_initial_separation_of_literature p hp h hChen hChenSen h5 h25
    (pure_physicalReplicaMeanEnergy_of_literature p hp h hChen h24) hRelocate

end SlowEquilibration.SourceConditionedCPTransferPureLiterature
