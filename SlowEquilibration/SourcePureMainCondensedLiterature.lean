-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferPureLiterature
public import SlowEquilibration.PurePhysicalHighEnergyRelocation

/-!
# Pure models: `thm:main-condensed` and `thm:main-initial`(i) from cited literature

For the pure model `ξ(r) = r^p`, `p ≥ 4`, at an inverse temperature where the
strict one-step certificate holds, the dynamics started from the uniform law
stays at total variation distance tending to one from the Gibbs measure up to
time `e^{γN}`, in probability (source `thm:main-condensed`). With the same
exponent, the failure probability tends to zero uniformly over prescribed
initial laws, and also for random initial laws independent of the disorder
(source `thm:main-initial`(i)).

The hypotheses are the certificate and explicit interfaces for published
results: Chen (2013) Theorem 1, Chen–Sen (2017) Theorem 1, and Subag
(arXiv:1804.10576v6) Theorem 5, Remark 25 and Proposition 24. The three
manuscript-specific premises of the pure consumer theorem (directing norm,
replicated-mean energy, high-energy relocation) are all proved.
-/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourcePureMainCondensedLiterature

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate PureStationarity
open PureCapturePhysicalCoarseDiniAssembly SphericalOrthogonalHaar
open SourceConditionedCPTransferPureConsumer SourceConditionedCPTransferInitialAdapter
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open SourceLiteraturePhysicalNormQ LiteratureSubagTAP LiteratureSubagReplicaExclusion
open LiteratureSubagProposition24 PureReplicaMeanEnergyAssembly
open PurePhysicalHighEnergyRelocation SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 700000

/-- Pure `p ≥ 4`, conditional only on the cited literature: uniform-start
separation, uniform failure over prescribed initial laws, and failure for
independent random initial laws, all with one exponent `γ`. -/
theorem pure_main_condensed_and_initial_of_literature
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) h.beta_pos.le))
    (h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
    (h24 : Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun (J N) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨γ, hγ, hsep⟩ := pure_separation_of_three_physical_inputs p hp h
    (physicalDirectingNormQ_of_cited_theorems hChen hChenSen h h5 h25)
    (pure_physicalReplicaMeanEnergy_of_literature p hp h hChen h24)
    (pure_physicalHighEnergyRelocation p hp)
  have hhaar : uniformSeparationInProbability μ β
      (fun N => exponentialGridHorizon γ N) :=
    original_uniform_to_haar μ β _ hsep
  refine ⟨γ, hγ, hhaar, fun ε hε => uniformPrescribedFailure_tendsto_zero μ β _ hhaar hε, ?_⟩
  intro Ω _ P _ J ν hJ hν hind hsphere ε hε
  exact independent_initial_failure_of_original_uniform μ β _ hsep
    P J ν hJ hν hind hsphere hε

/-- Source `cor:main-classes`(a), conditional on the cited literature: for the
pure model `ξ(r) = r^p` with `p ≥ 4` and every `β > β_s(p)`, the conclusions of
`thm:main-condensed` and `thm:main-initial`(i) hold with a common exponent.
The certificate is constructed by `pure_certificate_above_static`; Subag's
results are taken at every overlap, as published. -/
theorem pure_corollary_a_of_literature (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ p) < β)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : ∀ hβ₀ : 0 ≤ β, Theorem5 (literatureThermodynamicData hChen hChenSen
      (FiniteMixture.pure p (by omega) 1 (by positivity)) hβ₀))
    (h25 : Remark25Contrapositive
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
    (h24 : ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 →
      Proposition24 (FiniteMixture.pure p (by omega) 1 (by positivity)) β q) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun (J N) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  obtain ⟨x, Q, h⟩ := pure_certificate_above_static p hp hβ
  exact pure_main_condensed_and_initial_of_literature p hp h hChen hChenSen
    (h5 _) h25 (h24 Q h.overlap_range)

end SlowEquilibration.SourcePureMainCondensedLiterature
