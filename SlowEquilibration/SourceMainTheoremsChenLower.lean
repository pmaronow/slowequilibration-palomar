-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMainTheoremsReducedFinal
public import SlowEquilibration.LiteratureSubagBandUpperFinal
public import SlowEquilibration.LiteratureSubagBandLowerComplete

/-!
# Principal manuscript endpoints from Chen and the lower band input

Every composition-A declaration in
`docs/LITERATURE_INTERFACE_PROOFS_CHECKPOINT.md` has two exports here:
`<row>_of_chen_and_lower` and `<row>_of_chen_residual_thick`.
`C` means `Chen2013FiniteParisi`; `L(D)` means
`ExpectedBandLowerApproximation D`; `R(D)` means
`ResidualReplicatedLimit D`; `T(μ,β)` means
`ExpectedThickLatitudeLowerComparison μ β`.
The hypotheses column lists the two variants, separated by a semicolon.
The physical data are stated explicitly as `chenThermodynamicData` in the
signatures, except for replica exclusion, which retains its supplied `D`.
All original certificate, temperature, degree, geometry and initial-law
assumptions and endpoint conclusions are retained. In the perturbative row,
the lower inputs remain implications after the common positive cutoff and
after choosing the resulting mixture; no uniform lower input is assumed.
The supplied-data replica-exclusion proof does not need Chen; its Chen
argument is retained solely for the requested common export convention.

| Row (suffix omitted) | Manuscript label | Hypotheses (lower; residual/thick) |
| --- | --- | --- |
| `finiteMixture_main_condensed_and_initial_literal` | `thm:main-condensed; thm:main-initial(i)` | C + L(D); C + R(D) + T(μ,β) |
| `finiteMixture_all_initial_spherical` | `thm:main-initial(i)–(iii); cor:cp-information` | C + L(D); C + R(D) + T(μ,β) |
| `pure_corollary_a_all_initial` | `cor:main-classes(a), all initial laws` | C + L(D); C + R(D) + T(μ,β) |
| `convex_corollary_b` | `cor:main-classes(b), convexity` | C + L(D); C + R(D) + T(μ,β) |
| `degree_window_corollary_b` | `cor:main-classes(b), degree window` | C + L(D); C + R(D) + T(μ,β) |
| `support_four_through_eleven_corollary_b` | `cor:main-classes(b), support 4–11` | C + L(D); C + R(D) + T(μ,β) |
| `perturbative_corollary_c` | `cor:main-classes(c), after the common positive cutoff` | C + L(D); C + R(D) + T(μ,β), each resulting μ after the cutoff |
| `nonconvex_corollary_d` | `cor:main-classes(d)` | C + L(D); C + R(D) + T(μ,β) |
| `directing_norm` | `thm:dir-norm, literal directing families` | C + L(D); C + R(D) + T(μ,β) |
| `pureBranchFixedWindowCapture` | `thm:pc-capture, arbitrary amplitude` | C + L(D); C + R(D) + T(μ,β) |
| `mixed_original_fixed_window_capture` | `thm:mb-capture, mixed fixed-window witness` | C + L(D); C + R(D) + T(μ,β) |
| `mixed_count_capture_package` | `thm:mc-counts; lem:mb-counts; thm:mb-capture, mixed` | C + L(D); C + R(D) + T(μ,β) |
| `pure_normalized_count_capture_package` | `thm:mc-counts; lem:mb-counts; thm:mb-capture, normalized pure` | C + L(D); C + R(D) + T(μ,β) |
| `finiteMixture_count_capture_package` | `thm:mc-counts; lem:mb-counts; thm:mb-capture, all finite mixtures` | C + L(D); C + R(D) + T(μ,β) |
| `source_normalized_replica_exclusion` | `lem:th-replica-exclusion, arbitrary nonsamplable positive overlap` | C + L(D); C + R(D) + T(μ,β), supplied D (C redundant) |

The proved upper approximation and `subagBandApproximations_iff` supply the
band conjunction at any chosen physical data. The residual/thick variants
use `expectedBandLowerApproximation_of_residual_and_thickLatitude` without
changing its quantifiers. No new analytic input is asserted.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMainTheoremsChenLower

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi SourceLiteratureGroundState
open LiteratureSubagTAP LiteratureSubagRemark25Proof LiteratureSubagTheorem5Proof
open LiteratureSubagRemark25Final LiteratureSubagBandLowerComplete
open SourceMainTheoremsReducedFinal
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u v

private theorem bands_of_lower {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (hLower : ExpectedBandLowerApproximation D) :
    SubagBandApproximations μ β :=
  (subagBandApproximations_iff D).mpr
    ⟨LiteratureSubagBandUpperFinal.expectedBandUpperApproximation D, hLower⟩

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalEffectiveField SphericalRotationCovariance SphericalReversibility SphericalDynamics
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceFiniteMixtureMainLiteral

/-- `thm:main-condensed; thm:main-initial(i)`, from Chen and the lower band approximation. -/
theorem finiteMixture_main_condensed_and_initial_literal_of_chen_and_lower
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
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
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  exact SourceMainTheoremsReducedFinal.finiteMixture_main_condensed_and_initial_literal_of_chen_and_bands
    (μ := μ) (h := h) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `thm:main-condensed; thm:main-initial(i)`, from Chen, residual replication and thick latitude. -/
theorem finiteMixture_main_condensed_and_initial_literal_of_chen_residual_thick
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ h.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
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
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  exact finiteMixture_main_condensed_and_initial_literal_of_chen_and_lower
    (μ := μ) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage

/-- `thm:main-initial(i)–(iii); cor:cp-information`, from Chen and the lower band approximation. -/
theorem finiteMixture_all_initial_spherical_of_chen_and_lower
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    ∃ γ : ℝ, 0 < γ ∧ SphericalInitialConclusions.{u,v} μ β γ := by
  exact SourceMainTheoremsReducedFinal.finiteMixture_all_initial_spherical_of_chen_and_bands
    (μ := μ) (h := h) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `thm:main-initial(i)–(iii); cor:cp-information`, from Chen, residual replication and thick latitude. -/
theorem finiteMixture_all_initial_spherical_of_chen_residual_thick
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ h.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SphericalInitialConclusions.{u,v} μ β γ := by
  exact finiteMixture_all_initial_spherical_of_chen_and_lower
    (μ := μ) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate PureStationarity
open PureCapturePhysicalCoarseDiniAssembly SphericalAging.HardSphereDynamics
open SourceConditionedCPTransferPureAllInitial SourceInitialQuantitativeInput
open SourceInitialPolynomialMenu SourceInitialEntropyInformation
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open SourceLiteraturePhysicalNormQ LiteratureSubagTAP LiteratureSubagReplicaExclusion
open LiteratureSubagProposition24 PureReplicaMeanEnergyAssembly PurePhysicalHighEnergyRelocation
open SphericalOverlapExponential SphericalOrthogonalHaar
open scoped Topology NNReal ENNReal
open SourcePureMainTheoremsLiterature

/-- `cor:main-classes(a), all initial laws`, from Chen and the lower band approximation. -/
theorem pure_corollary_a_all_initial_of_chen_and_lower
    (p : ℕ)
    (hp : 4 ≤ p)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ p) < β)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen (FiniteMixture.pure p (by omega) 1 (by positivity))
        (β := β) (by
        have ht := (FiniteMixture.pure p (by omega) 1 (by positivity)).staticThreshold_pos
        have hξ : (FiniteMixture.pure p (by omega) 1 (by positivity)).xi =
            (fun r : ℝ => r ^ p) := by
          funext r
          simp only [FiniteMixture.pure_xi, one_mul]
        rw [hξ] at ht
        exact (ht.trans hβ).le))) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      SphericalOrthogonalHaar.uniformSeparationInProbability μ β
        (fun N => exponentialGridHorizon γ N) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (ν : ∀ N, ι N → Measure (Vector N))
        [∀ N j, IsProbabilityMeasure (ν N j)],
        (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((p : ℝ) - 2) / 2 → 0 < C₀ →
        (∀ᶠ N in atTop,
          (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalMenuReduction.physicalMenuDistance
            μ β (ν N) (exponentialGridHorizon γ N)) 1) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (R : ℕ → Type v) [∀ N, MeasurableSpace (R N)]
        (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
        (ν : ∀ N, R N → ι N → Measure (Vector N)),
        (∀ N j, Measurable (fun r => ν N r j)) →
        ∀ [∀ N r j, IsProbabilityMeasure (ν N r j)],
        (∀ N, 2 ≤ N → ∀ r j, ∀ᵐ y ∂ν N r j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((p : ℝ) - 2) / 2 → 0 < C₀ →
        (∀ᶠ N in atTop,
          (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) →
        VaryingProbability.InProbability
          (fun N => (ρ N).prod (SphericalFieldKernels.fieldLaw N μ))
          (fun N z => SphericalMenuReduction.physicalMenuDistance
            μ β (ν N z.1) (exponentialGridHorizon γ N) z.2) 1) ∧
      (∀ (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
        [∀ N, IsMarkovKernel (κ N)],
        ReductionEntropy.LittleLogInProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N)) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalFieldKernels.intervalDistance
            μ β (exponentialGridHorizon γ N) (κ N)) 1) ∧
      (∀ (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
        [∀ N, IsMarkovKernel (κ N)],
        (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
        ReductionInformation.LittleLog
          (fun N => endpointMutualInformation
            (SphericalFieldKernels.fieldLaw N μ) (κ N)) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalFieldKernels.intervalDistance
            μ β (exponentialGridHorizon γ N) (κ N)) 1) := by
  exact SourceMainTheoremsReducedFinal.pure_corollary_a_all_initial_of_chen_and_bands
    (p := p) (hp := hp) (hβ := hβ) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `cor:main-classes(a), all initial laws`, from Chen, residual replication and thick latitude. -/
theorem pure_corollary_a_all_initial_of_chen_residual_thick
    (p : ℕ)
    (hp : 4 ≤ p)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ p) < β)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen (FiniteMixture.pure p (by omega) 1 (by positivity))
        (β := β) (by
        have ht := (FiniteMixture.pure p (by omega) 1 (by positivity)).staticThreshold_pos
        have hξ : (FiniteMixture.pure p (by omega) 1 (by positivity)).xi =
            (fun r : ℝ => r ^ p) := by
          funext r
          simp only [FiniteMixture.pure_xi, one_mul]
        rw [hξ] at ht
        exact (ht.trans hβ).le)))
    (hThick : ExpectedThickLatitudeLowerComparison (FiniteMixture.pure p (by omega) 1 (by positivity)) β) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∃ γ : ℝ, 0 < γ ∧
      SphericalOrthogonalHaar.uniformSeparationInProbability μ β
        (fun N => exponentialGridHorizon γ N) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (ν : ∀ N, ι N → Measure (Vector N))
        [∀ N j, IsProbabilityMeasure (ν N j)],
        (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((p : ℝ) - 2) / 2 → 0 < C₀ →
        (∀ᶠ N in atTop,
          (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalMenuReduction.physicalMenuDistance
            μ β (ν N) (exponentialGridHorizon γ N)) 1) ∧
      (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
        (R : ℕ → Type v) [∀ N, MeasurableSpace (R N)]
        (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
        (ν : ∀ N, R N → ι N → Measure (Vector N)),
        (∀ N j, Measurable (fun r => ν N r j)) →
        ∀ [∀ N r j, IsProbabilityMeasure (ν N r j)],
        (∀ N, 2 ≤ N → ∀ r j, ∀ᵐ y ∂ν N r j, OnSphere y) →
        ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((p : ℝ) - 2) / 2 → 0 < C₀ →
        (∀ᶠ N in atTop,
          (Fintype.card (ι N) : ℝ) ≤ C₀ * (N : ℝ)^κ) →
        VaryingProbability.InProbability
          (fun N => (ρ N).prod (SphericalFieldKernels.fieldLaw N μ))
          (fun N z => SphericalMenuReduction.physicalMenuDistance
            μ β (ν N z.1) (exponentialGridHorizon γ N) z.2) 1) ∧
      (∀ (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
        [∀ N, IsMarkovKernel (κ N)],
        ReductionEntropy.LittleLogInProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N)) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalFieldKernels.intervalDistance
            μ β (exponentialGridHorizon γ N) (κ N)) 1) ∧
      (∀ (κ : ∀ N, Kernel (SphericalFieldKernels.Field N μ) (Vector N))
        [∀ N, IsMarkovKernel (κ N)],
        (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
        ReductionInformation.LittleLog
          (fun N => endpointMutualInformation
            (SphericalFieldKernels.fieldLaw N μ) (κ N)) →
        VaryingProbability.InProbability
          (fun N => SphericalFieldKernels.fieldLaw N μ)
          (fun N => SphericalFieldKernels.intervalDistance
            μ β (exponentialGridHorizon γ N) (κ N)) 1) := by
  exact pure_corollary_a_all_initial_of_chen_and_lower
    (p := p) (hp := hp) (hβ := hβ) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature

/-- `cor:main-classes(b), convexity`, from Chen and the lower band approximation. -/
theorem convex_corollary_b_of_chen_and_lower
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))))
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le)) :
    MainCondensedAndInitialLiteral μ β := by
  exact SourceMainTheoremsReducedFinal.convex_corollary_b_of_chen_and_bands
    (μ := μ) (hd := hd) (hβ := hβ) (hξ := hξ) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `cor:main-classes(b), convexity`, from Chen, residual replication and thick latitude. -/
theorem convex_corollary_b_of_chen_residual_thick
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))))
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    MainCondensedAndInitialLiteral μ β := by
  exact convex_corollary_b_of_chen_and_lower
    (μ := μ) (hd := hd) (hβ := hβ) (hξ := hξ) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature

/-- `cor:main-classes(b), degree window`, from Chen and the lower band approximation. -/
theorem degree_window_corollary_b_of_chen_and_lower
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2))
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le)) :
    MainCondensedAndInitialLiteral μ β := by
  exact SourceMainTheoremsReducedFinal.degree_window_corollary_b_of_chen_and_bands
    (μ := μ) (hd := hd) (hwindow := hwindow) (hβ := hβ) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `cor:main-classes(b), degree window`, from Chen, residual replication and thick latitude. -/
theorem degree_window_corollary_b_of_chen_residual_thick
    (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2))
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    MainCondensedAndInitialLiteral μ β := by
  exact degree_window_corollary_b_of_chen_and_lower
    (μ := μ) (hd := hd) (hwindow := hwindow) (hβ := hβ) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set SphericalModel SourceMainClassesLiterature
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceMainClassesDegreeWindow

/-- `cor:main-classes(b), support 4–11`, from Chen and the lower band approximation. -/
theorem support_four_through_eleven_corollary_b_of_chen_and_lower
    (μ : FiniteMixture)
    (hsupport : ∀ p ∈ μ.coeff.support, p ∈ Finset.Icc 4 11)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le)) :
    MainCondensedAndInitialLiteral μ β := by
  exact SourceMainTheoremsReducedFinal.support_four_through_eleven_corollary_b_of_chen_and_bands
    (μ := μ) (hsupport := hsupport) (hβ := hβ) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `cor:main-classes(b), support 4–11`, from Chen, residual replication and thick latitude. -/
theorem support_four_through_eleven_corollary_b_of_chen_residual_thick
    (μ : FiniteMixture)
    (hsupport : ∀ p ∈ μ.coeff.support, p ∈ Finset.Icc 4 11)
    {β : ℝ}
    (hβ : Thresholds.staticThreshold μ.xi < β)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ (μ.staticThreshold_pos.trans hβ).le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    MainCondensedAndInitialLiteral μ β := by
  exact support_four_through_eleven_corollary_b_of_chen_and_lower
    (μ := μ) (hsupport := hsupport) (hβ := hβ) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open CrisantiSommers CSParisiMeasure SourceMainClassesLiterature CSPerturbative
open SphericalOrthogonalHaar
open LiteratureSubagPhysicalDefinitions
open LiteratureSubagBandUpperExtraction.Endpoints

/-- `cor:main-classes(c), after the common positive cutoff`, with only the lower approximation for each resulting mixture. -/
theorem perturbative_corollary_c_of_chen_and_lower (d P : ℕ)
    (hd : 4 ≤ d) (hdEven : Even d) (hdP : d < P) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ d) < β)
    (hChen : Chen2013FiniteParisi) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (b : EvenPerturbation d P), b.coeff.sum (fun _ c => c) = 1 →
        ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
          let μ := b.covariance (by omega) ε hε.le
          ExpectedBandLowerApproximation
            (chenThermodynamicData hChen μ (β := β) (by
              have ht := (FiniteMixture.pure d (by omega) 1 (by positivity)).staticThreshold_pos
              have hξ : (FiniteMixture.pure d (by omega) 1 (by positivity)).xi =
                  (fun r : ℝ => r ^ d) := by
                funext r
                simp only [FiniteMixture.pure_xi, one_mul]
              rw [hξ] at ht
              exact (ht.trans hβ).le)) → MainCondensedAndInitialLiteral μ β := by
  obtain ⟨ε₀, hε₀, hresult⟩ :=
    SourceMainTheoremsReducedFinal.perturbative_corollary_c_of_chen_and_bands
      d P hd hdEven hdP hβ hChen
  refine ⟨ε₀, hε₀, ?_⟩
  intro b hb ε hε hsmall
  dsimp only
  intro hLower
  exact hresult b hb ε hε hsmall (bands_of_lower _ hLower)

/-- `cor:main-classes(c), after the common positive cutoff`, from residual replication and thick latitude for each resulting mixture. -/
theorem perturbative_corollary_c_of_chen_residual_thick (d P : ℕ)
    (hd : 4 ≤ d) (hdEven : Even d) (hdP : d < P) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r ^ d) < β)
    (hChen : Chen2013FiniteParisi) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (b : EvenPerturbation d P), b.coeff.sum (fun _ c => c) = 1 →
        ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
          let μ := b.covariance (by omega) ε hε.le
          ResidualReplicatedLimit
            (chenThermodynamicData hChen μ (β := β) (by
              have ht := (FiniteMixture.pure d (by omega) 1 (by positivity)).staticThreshold_pos
              have hξ : (FiniteMixture.pure d (by omega) 1 (by positivity)).xi =
                  (fun r : ℝ => r ^ d) := by
                funext r
                simp only [FiniteMixture.pure_xi, one_mul]
              rw [hξ] at ht
              exact (ht.trans hβ).le)) →
          ExpectedThickLatitudeLowerComparison μ β → MainCondensedAndInitialLiteral μ β := by
  obtain ⟨ε₀, hε₀, hresult⟩ :=
    perturbative_corollary_c_of_chen_and_lower d P hd hdEven hdP hβ hChen
  refine ⟨ε₀, hε₀, ?_⟩
  intro b hb ε hε hsmall
  dsimp only
  intro hResidual hThick
  exact hresult b hb ε hε hsmall
    (expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set MeasureTheory ProbabilityTheory Filter CrisantiSommers CSParisiMeasure
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SourceFiniteMixtureMainLiteral CSPerturbative
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
open SourceMainClassesLiterature

/-- `cor:main-classes(d)`, from Chen and the lower band approximation. -/
theorem nonconvex_corollary_d_of_chen_and_lower
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen NonconvexCertificate.exampleMixture
        NonconvexCertificate.beta_pos.le)) :
    MainCondensedAndInitialLiteral
      NonconvexCertificate.exampleMixture NonconvexCertificate.beta := by
  exact SourceMainTheoremsReducedFinal.nonconvex_corollary_d_of_chen_and_bands
    (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `cor:main-classes(d)`, from Chen, residual replication and thick latitude. -/
theorem nonconvex_corollary_d_of_chen_residual_thick
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen NonconvexCertificate.exampleMixture
        NonconvexCertificate.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison NonconvexCertificate.exampleMixture NonconvexCertificate.beta) :
    MainCondensedAndInitialLiteral
      NonconvexCertificate.exampleMixture NonconvexCertificate.beta := by
  exact nonconvex_corollary_d_of_chen_and_lower
    (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalTAPCertificate
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalReplicaExclusionLimit PureCapturePhysicalReplicaExclusionDirecting
open PureCaptureDirectingFullToScore PureCapturePhysicalFullToScore
open PureCaptureOverlapScoreCoordinates PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalCoarseDiniAssembly DirectingPhysical
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceSphericalSelfAveraging
open scoped Topology BigOperators ENNReal
open PureCapturePhysicalInfiniteArrayTightness
open PureCapturePhysicalInfiniteAsymptoticLift
open SourceDirectingFamilies

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- `thm:dir-norm, literal directing families`, from Chen and the lower band approximation. -/
theorem directing_norm_of_chen_and_lower
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (d : Measure Ω)
    [IsProbabilityMeasure d]
    {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hL : L ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (F : DirectingFamily (H := H) d L)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, (F.measure ω : Measure H) {v | ‖v‖ ^ 2 = Q} = 1 := by
  exact SourceMainTheoremsReducedFinal.directing_norm_of_chen_and_bands
    (hChen := hChen) (h := h) (d := d) (hL := hL) (F := F)
    (hBands := bands_of_lower _ hLower)

/-- `thm:dir-norm, literal directing families`, from Chen, residual replication and thick latitude. -/
theorem directing_norm_of_chen_residual_thick
    (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture}
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (d : Measure Ω)
    [IsProbabilityMeasure d]
    {L : ProbabilityMeasure InfiniteOverlapCoordinates}
    (hL : L ∈ physicalInfiniteAsymptoticLimitSet μ β)
    (F : DirectingFamily (H := H) d L)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ h.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    ∃ Z : Set Ω, MeasurableSet Z ∧ d Z = 0 ∧
      ∀ ω ∉ Z, (F.measure ω : Measure H) {v | ‖v‖ ^ 2 = Q} = 1 := by
  exact directing_norm_of_chen_and_lower
    (hChen := hChen) (h := h) (d := d) (hL := hL) (F := F)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate SphericalOrthogonalHaar
open SphericalMarkedWindows TwoAtomStationarity
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SourceConditionedCPTransferInitialAdapter
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SphericalGaussianJet SphericalForm SourceReductionClosedBandGraph
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open scoped Topology NNReal
open SourcePureAmplitudeScaling

/-- `thm:pc-capture, arbitrary amplitude`, from Chen and the lower band approximation. -/
theorem pureBranchFixedWindowCapture_of_chen_and_lower
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    PureBranchFixedWindowCapture μ β x Q := by
  exact SourceMainTheoremsReducedFinal.pureBranchFixedWindowCapture_of_chen_and_bands
    (μ := μ) (h := h) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `thm:pc-capture, arbitrary amplitude`, from Chen, residual replication and thick latitude. -/
theorem pureBranchFixedWindowCapture_of_chen_residual_thick
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ h.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    PureBranchFixedWindowCapture μ β x Q := by
  exact pureBranchFixedWindowCapture_of_chen_and_lower
    (μ := μ) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal
open SourceMixedCaptureCommonWitness

/-- `thm:mb-capture, mixed fixed-window witness`, from Chen and the lower band approximation. -/
theorem mixed_original_fixed_window_capture_of_chen_and_lower
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    ∃ L R b₀ : ℝ,
      2 * Real.sqrt (Q^2 * μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ,
        Tendsto (fun n => m n / ((n+2 : ℕ) : ℝ))
          atTop (𝓝 (markE μ β x Q)) ∧
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M (Icc L R))
            atTop < ⊤) ∧
        ∀ b : ℝ, 0 < b → b ≤ b₀ →
          Tendsto (fun M : ℝ => limsup (fun n =>
            ∫ J, originalBandComplementMass μ Q (m n) M b β
              (Icc L R) J ∂disorderLaw (n+2) μ.maxDegree) atTop)
            atTop (𝓝 0) := by
  exact SourceMainTheoremsReducedFinal.mixed_original_fixed_window_capture_of_chen_and_bands
    (μ := μ) (h := h) (hnp := hnp) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `thm:mb-capture, mixed fixed-window witness`, from Chen, residual replication and thick latitude. -/
theorem mixed_original_fixed_window_capture_of_chen_residual_thick
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ h.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    ∃ L R b₀ : ℝ,
      2 * Real.sqrt (Q^2 * μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ,
        Tendsto (fun n => m n / ((n+2 : ℕ) : ℝ))
          atTop (𝓝 (markE μ β x Q)) ∧
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M (Icc L R))
            atTop < ⊤) ∧
        ∀ b : ℝ, 0 < b → b ≤ b₀ →
          Tendsto (fun M : ℝ => limsup (fun n =>
            ∫ J, originalBandComplementMass μ Q (m n) M b β
              (Icc L R) J ∂disorderLaw (n+2) μ.maxDegree) atTop)
            atTop (𝓝 0) := by
  exact mixed_original_fixed_window_capture_of_chen_and_lower
    (μ := μ) (h := h) (hnp := hnp) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SourceMixedCountCapturePackage

/-- `thm:mc-counts; lem:mb-counts; thm:mb-capture, mixed`, from Chen and the lower band approximation. -/
theorem mixed_count_capture_package_of_chen_and_lower
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    ∃ C cut η ε L R b₀ : ℝ,
      0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 h.min_degree ∧
      0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss
        ((markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2/2) C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        CountCapturePackage μ β x Q L R b₀ d.center ∧
        ∀ t : ℝ, 0 < t → MixedSharpAtWindow μ β x Q C cut η ε L R d.center t := by
  exact SourceMainTheoremsReducedFinal.mixed_count_capture_package_of_chen_and_bands
    (μ := μ) (h := h) (hnp := hnp) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `thm:mc-counts; lem:mb-counts; thm:mb-capture, mixed`, from Chen, residual replication and thick latitude. -/
theorem mixed_count_capture_package_of_chen_residual_thick
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ h.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    ∃ C cut η ε L R b₀ : ℝ,
      0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 h.min_degree ∧
      0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss
        ((markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2/2) C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        CountCapturePackage μ β x Q L R b₀ d.center ∧
        ∀ t : ℝ, 0 < t → MixedSharpAtWindow μ β x Q C cut η ε L R d.center t := by
  exact mixed_count_capture_package_of_chen_and_lower
    (μ := μ) (h := h) (hnp := hnp) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage

/-- `thm:mc-counts; lem:mb-counts; thm:mb-capture, normalized pure`, from Chen and the lower band approximation. -/
theorem pure_normalized_count_capture_package_of_chen_and_lower
    (p : ℕ)
    (hp : 2 ≤ p)
    (a : ℝ)
    (ha : 0 < a)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen (FiniteMixture.pure p hp a ha)
      h.beta_pos.le)) :
    let μ := FiniteMixture.pure p hp a ha
    ∃ L R b₀ C cut η ε δ : ℝ, ∃ m : ℕ → ℝ,
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < δ ∧
      0 < cut ∧ cut ≤ 1 ∧ 0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      CountCapturePackage μ β x Q L R b₀ m ∧
      (∀ᶠ n : ℕ in atTop, ExpectedTailCentering.tail
        (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(markE μ β x Q-δ)) ((n+2 : ℕ)*(markE μ β x Q+δ))) (m n) = 1) ∧
      ∀ t : ℝ, 0 < t → PureSharpAtWindow μ β x Q C cut η ε δ m t ∧
        PureWindowIdentification μ β x Q C η ε δ L R m t := by
  exact SourceMainTheoremsReducedFinal.pure_normalized_count_capture_package_of_chen_and_bands
    (p := p) (hp := hp) (a := a) (ha := ha) (h := h) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `thm:mc-counts; lem:mb-counts; thm:mb-capture, normalized pure`, from Chen, residual replication and thick latitude. -/
theorem pure_normalized_count_capture_package_of_chen_residual_thick
    (p : ℕ)
    (hp : 2 ≤ p)
    (a : ℝ)
    (ha : 0 < a)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen (FiniteMixture.pure p hp a ha)
      h.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison (FiniteMixture.pure p hp a ha) β) :
    let μ := FiniteMixture.pure p hp a ha
    ∃ L R b₀ C cut η ε δ : ℝ, ∃ m : ℕ → ℝ,
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧ 0 < δ ∧
      0 < cut ∧ cut ≤ 1 ∧ 0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      CountCapturePackage μ β x Q L R b₀ m ∧
      (∀ᶠ n : ℕ in atTop, ExpectedTailCentering.tail
        (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(markE μ β x Q-δ)) ((n+2 : ℕ)*(markE μ β x Q+δ))) (m n) = 1) ∧
      ∀ t : ℝ, 0 < t → PureSharpAtWindow μ β x Q C cut η ε δ m t ∧
        PureWindowIdentification μ β x Q C η ε δ L R m t := by
  exact pure_normalized_count_capture_package_of_chen_and_lower
    (p := p) (hp := hp) (a := a) (ha := ha) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly LatitudeGroundTrial SphericalPairChartKacRice
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal NNReal
open SphericalEffectiveField SphericalFieldKernels SphericalRotationCovariance
open SphericalDynamics SphericalReversibility SphericalOrthogonalHaar SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open SourceFiniteMixtureAllInitialLiterature SourceInitialQuantitativeInput
open SourceConditionedCPTransferFiniteMixtureLiterature
open CrisantiSommers LiteratureSubagPhysicalDefinitions
open PureCapturePhysicalFullOverlapArray PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalCoarseDiniAssembly
open SourceReductionConsumerBandBound WholeFieldRegression
open scoped RealInnerProductSpace
open SourceMixedCountCapturePackage

/-- `thm:mc-counts; lem:mb-counts; thm:mb-capture, all finite mixtures`, from Chen and the lower band approximation. -/
theorem finiteMixture_count_capture_package_of_chen_and_lower
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation
      (chenThermodynamicData hChen μ h.beta_pos.le)) :
    ∃ L R b₀ : ℝ, sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧
      markK μ β Q < R ∧ 0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ, CountCapturePackage μ β x Q L R b₀ m := by
  exact SourceMainTheoremsReducedFinal.finiteMixture_count_capture_package_of_chen_and_bands
    (μ := μ) (h := h) (hChen := hChen)
    (hBands := bands_of_lower _ hLower)

/-- `thm:mc-counts; lem:mb-counts; thm:mb-capture, all finite mixtures`, from Chen, residual replication and thick latitude. -/
theorem finiteMixture_count_capture_package_of_chen_residual_thick
    (μ : FiniteMixture)
    {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit
      (chenThermodynamicData hChen μ h.beta_pos.le))
    (hThick : ExpectedThickLatitudeLowerComparison μ β) :
    ∃ L R b₀ : ℝ, sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧
      markK μ β Q < R ∧ 0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ, CountCapturePackage μ β x Q L R b₀ m := by
  exact finiteMixture_count_capture_package_of_chen_and_lower
    (μ := μ) (h := h) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

section

open LiteratureSubagPhysicalDefinitions LiteratureSubagContact

/-- `lem:th-replica-exclusion, arbitrary nonsamplable positive overlap`, from Chen and the lower band approximation. -/
theorem source_normalized_replica_exclusion_of_chen_and_lower
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hChen : Chen2013FiniteParisi)
    (hLower : ExpectedBandLowerApproximation D) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hn : ¬ MultiSamplable μ β q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
  have _ := hChen
  exact SourceMainTheoremsReducedFinal.source_normalized_replica_exclusion_of_chen_and_bands
    (D := D) (hβ := hβ) (hq := hq) (hn := hn)
    (hBands := bands_of_lower _ hLower)

/-- `lem:th-replica-exclusion, arbitrary nonsamplable positive overlap`, from Chen, residual replication and thick latitude. -/
theorem source_normalized_replica_exclusion_of_chen_residual_thick
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hChen : Chen2013FiniteParisi)
    (hResidual : ResidualReplicatedLimit D)
    (hThick : ExpectedThickLatitudeLowerComparison μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hn : ¬ MultiSamplable μ β q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) := by
  exact source_normalized_replica_exclusion_of_chen_and_lower
    (D := D) (hβ := hβ) (hq := hq) (hn := hn) (hChen := hChen)
    (hLower := expectedBandLowerApproximation_of_residual_and_thickLatitude _ hResidual hThick)

end

end SlowEquilibration.SourceMainTheoremsChenLower
